import Savitch.Outer.VLoop

/-!
# Building the tape layout for a width

Phase 4b-6 of the Savitch formalization (see `PLAN.md`).

The ruler tape `tRu` holds `L` copies of a record. From it:
* `makeBlock t g`: tape `t` gets the block of `L` copies of `g` (`Spec.makeBlock`),
  whatever it held before beyond cell 0.
-/

set_option linter.unusedSectionVars false

namespace Savitch.Edge

open TM Machine Machine.NTM

variable {Λ Γ : Type} [Fintype Λ] [Fintype Γ] [DecidableEq Λ] [DecidableEq Γ]
variable {x : List Bool} {B : ℕ}

theorem map_const_eq_replicate {α β : Type} (l : List α) (g : β) :
    l.map (fun _ => g) = List.replicate l.length g := by
  induction l with
  | nil => rfl
  | cons _ l ih => simp [ih, List.replicate_succ]

/-- Write `L` copies of `g` on tape `t`, `L` being the length of the ruler. -/
noncomputable def makeBlock (t : Fin NT) (g : Sym Λ Γ) : Code NT (Sym Λ Γ) :=
  copyMapWhile tRu t isRec (fun _ => g) ++ [Instr.write t .blank] ++ TM.home tRu .mk ++
    TM.home t .mk

theorem Spec.makeBlock {t : Fin NT} (htR : tRu ≠ t) {g : Sym Λ Γ} (hgm : g ≠ .mk)
    {lr : List (Sym Λ Γ)} {T : Tapes NT (Sym Λ Γ)} (hRu : Lay tRu .mk .blank T lr)
    (hrec : ∀ g ∈ lr, isRec g = true) (h0 : T.tp t 0 = .mk) (h1 : T.hd t = 1)
    (hT : T.Within B) (hB : lr.length + 2 ≤ B) :
    ∃ T', Spec (makeBlock t g) x B T T' ∧ Lay t .mk .blank T' (List.replicate lr.length g) ∧
      Lay tRu .mk .blank T' lr ∧ T.Agree (fun i => i = t) T' ∧ T'.ih = T.ih ∧ T'.Within B := by
  have hmb : (Sym.mk : Sym Λ Γ) ≠ .blank := fun h => by cases h
  set L := lr.length
  have hc := Spec.copyMapWhile (x := x) htR isRec (fun _ => g) L T
    (fun j hj => hrec _ (hRu.cell hj)) (by rw [hRu.endCell]; rfl) hT
    (by rw [hRu.2.2.2]; omega) (by rw [h1]; omega)
  set T₁ := T.copyMapRes tRu t (fun _ => g) L
  have hW₁ : T₁.Within B := hc.target_within
  have hT₁hd : T₁.hd t = 1 + L := by rw [Tapes.copyMapRes_hd_b, h1]
  have hT₁R : T₁.tp tRu = T.tp tRu := Tapes.copyMapRes_tp_ne htR T L
  have hseg : seg (T₁.tp t) 1 L = List.replicate L g := by
    have := Tapes.seg_copyMapRes (a := tRu) (b := t) (h := fun _ => g) T L
    rw [h1, hRu.2.2.2, hRu.2.1, map_const_eq_replicate] at this; exact this
  have h0₁ : T₁.tp t 0 = .mk := by
    rw [Tapes.copyMapRes_tp_b_out T L (Or.inl (by rw [h1]; omega))]; exact h0
  -- end marker
  have s2 := Spec.write (x := x) (t := t) (g := (Sym.blank : Sym Λ Γ)) hW₁
  set T₂ := T₁.write t .blank
  have hW₂ : T₂.Within B := Tapes.within_write hW₁
  have hT₂t : ∀ j, j ≠ 1 + L → T₂.tp t j = T₁.tp t j := fun j hj => by
    simp only [T₂]; rw [Tapes.write_tp_self, ite_neg' (by rw [hT₁hd]; exact hj)]
  have hseg₂ : seg (T₂.tp t) 1 L = List.replicate L g := by
    rw [seg_congr (g := T₁.tp t) (fun j _ h => hT₂t j (by omega))]; exact hseg
  have hend₂ : T₂.tp t (L + 1) = .blank := by
    simp only [T₂]; rw [Tapes.write_tp_self, ite_pos' (by rw [hT₁hd]; omega)]
  have h0₂ : T₂.tp t 0 = .mk := by rw [hT₂t 0 (by omega)]; exact h0₁
  -- heads home
  have hh1 := Spec.home (x := x) tRu .mk (T := T₂)
    (by simp only [T₂, Tapes.write, Function.update_apply, htR, ite_false]; rw [hT₁R]; exact hRu.1)
    (by simp only [T₂, Tapes.write, Function.update_apply, htR, ite_false]
        rw [hT₁R, Tapes.copyMapRes_hd_a htR, hRu.2.2.2]
        exact home_ok hmb (fun g hg => by
          have := hrec g hg; intro h; subst h; simp [isRec] at this) hRu.2.1 hRu.2.2.1
          (by omega))
    hW₂ (by omega)
  set T₃ := T₂.setHead tRu 1
  have hW₃ : T₃.Within B := Tapes.within_setHead hW₂ (by omega)
  have hlr : (List.replicate L g).length = L := List.length_replicate
  have hh2 := Spec.home (x := x) t .mk (T := T₃) (by simp only [T₃, Tapes.setHead_tp]; exact h0₂)
    (by simp only [T₃, Tapes.setHead_tp]
        rw [Tapes.setHead_hd_ne _ _ (Ne.symm htR), show T₂.hd t = T₁.hd t from rfl, hT₁hd]
        exact home_ok (l := List.replicate L g) hmb (fun g' hg' => by
          rw [List.eq_of_mem_replicate hg']; exact hgm) (by rw [hlr]; exact hseg₂)
          (by rw [hlr]; exact hend₂) (by rw [hlr]; omega))
    hW₃ (by omega)
  refine ⟨T₃.setHead t 1, ((hc.seq s2).seq hh1).seq hh2, ⟨?_, ?_, ?_, by simp⟩, ?_, ?_, rfl,
    Tapes.within_setHead hW₃ (by omega)⟩
  · simp only [Tapes.setHead_tp, T₃]; exact h0₂
  · simp only [Tapes.setHead_tp, T₃]; rw [hlr]; exact hseg₂
  · simp only [Tapes.setHead_tp, T₃]; rw [hlr]; exact hend₂
  · refine hRu.congr ?_ ?_
    · simp only [Tapes.setHead_tp, T₃, T₂, Tapes.write, Function.update_apply, htR, ite_false]
      exact hT₁R
    · rw [Tapes.setHead_hd_ne _ _ htR]; simp [T₃, hRu.2.2.2]
  · intro i hi
    refine ⟨?_, ?_⟩
    · simp only [Tapes.setHead_tp, T₃, T₂, Tapes.write, Function.update_apply, hi, ite_false]
      exact Tapes.copyMapRes_tp_ne (h := fun _ => g) hi T L
    · rw [Tapes.setHead_hd_ne _ _ hi]
      by_cases hiR : i = tRu
      · subst hiR; simp [T₃, hRu.2.2.2]
      · rw [Tapes.setHead_hd_ne _ _ hiR]
        exact Tapes.copyMapRes_hd_ne (h := fun _ => g) hiR hi T L

/-! ### Many blocks at once -/

noncomputable def makeBlocks : List (Fin NT × Sym Λ Γ) → Code NT (Sym Λ Γ)
  | [] => []
  | (t, g) :: rest => makeBlock t g ++ makeBlocks rest

theorem Spec.makeBlocks {lr : List (Sym Λ Γ)} (hrec : ∀ g ∈ lr, isRec g = true) :
    ∀ (bs : List (Fin NT × Sym Λ Γ)) {T : Tapes NT (Sym Λ Γ)},
      (bs.map Prod.fst).Nodup → (∀ p ∈ bs, tRu ≠ p.1 ∧ p.2 ≠ .mk) →
      Lay tRu .mk .blank T lr → (∀ p ∈ bs, T.tp p.1 0 = .mk ∧ T.hd p.1 = 1) →
      T.Within B → lr.length + 2 ≤ B →
      ∃ T', Spec (makeBlocks bs) x B T T' ∧
        (∀ p ∈ bs, Lay p.1 .mk .blank T' (List.replicate lr.length p.2)) ∧
        Lay tRu .mk .blank T' lr ∧ T.Agree (fun i => ∃ p ∈ bs, p.1 = i) T' ∧ T'.ih = T.ih ∧
        T'.Within B
  | [], T, _, _, hRu, _, hT, _ =>
    ⟨T, Spec.nil hT, fun _ h => absurd h List.not_mem_nil, hRu, Tapes.Agree.refl _ T, rfl, hT⟩
  | (t, g) :: rest, T, hnd, hok, hRu, hpre, hT, hB => by
    obtain ⟨htR, hgm⟩ := hok (t, g) List.mem_cons_self
    obtain ⟨h0, h1⟩ := hpre (t, g) List.mem_cons_self
    obtain ⟨T₁, s1, hL₁, hRu₁, ag1, ih1, hW₁⟩ :=
      Spec.makeBlock (x := x) htR hgm hRu hrec h0 h1 hT hB
    have hnd' : (rest.map Prod.fst).Nodup := (List.nodup_cons.1 hnd).2
    have hnotin : ∀ p ∈ rest, p.1 ≠ t := fun p hp e => (List.nodup_cons.1 hnd).1
      (List.mem_map.2 ⟨p, hp, e⟩)
    have hpre' : ∀ q ∈ rest, T₁.tp q.1 0 = .mk ∧ T₁.hd q.1 = 1 := by
      intro q hq
      have g := ag1 q.1 (hnotin q hq)
      exact ⟨by rw [g.1]; exact (hpre q (List.mem_cons_of_mem _ hq)).1,
        by rw [g.2]; exact (hpre q (List.mem_cons_of_mem _ hq)).2⟩
    obtain ⟨T₂, s2, hL₂, hRu₂, ag2, ih2, hW₂⟩ := Spec.makeBlocks hrec rest hnd'
      (fun q hq => hok q (List.mem_cons_of_mem _ hq)) hRu₁ hpre' hW₁ hB
    refine ⟨T₂, s1.seq s2, ?_, hRu₂, ?_, by rw [ih2, ih1], hW₂⟩
    · intro p hp
      rcases List.mem_cons.1 hp with h | hp
      · rw [h]
        have g' : ¬ (∃ q ∈ rest, q.1 = t) := fun ⟨q, hq, e⟩ => hnotin q hq e
        exact hL₁.congr (ag2 t g').1 (ag2 t g').2
      · exact hL₂ p hp
    · intro i hi
      have hit : i ≠ t := fun e => hi ⟨(t, g), List.mem_cons_self, e.symm⟩
      have hir : ¬ (∃ p ∈ rest, p.1 = i) := fun ⟨p, hp, e⟩ =>
        hi ⟨p, List.mem_cons_of_mem _ hp, e⟩
      exact ⟨(ag2 i hir).1.trans (ag1 i hit).1, (ag2 i hir).2.trans (ag1 i hit).2⟩

/-! ### Growing a block by one cell -/

/-- Append `g` at the end of the block on `t` (whose cells satisfy `p`). -/
noncomputable def appendCell (t : Fin NT) (p : Sym Λ Γ → Bool) (g : Sym Λ Γ) : Code NT (Sym Λ Γ) :=
  TM.scanRight t p ++ [Instr.write t g] ++ [Instr.move t .right] ++ [Instr.write t .blank] ++
    TM.home t .mk

theorem Spec.appendCell {t : Fin NT} {p : Sym Λ Γ → Bool} {g : Sym Λ Γ} (hgm : g ≠ .mk)
    {l : List (Sym Λ Γ)} {T : Tapes NT (Sym Λ Γ)} (h0 : T.tp t 0 = .mk)
    (hseg : seg (T.tp t) 1 l.length = l) (hp : ∀ g ∈ l, p g = true) (hml : ∀ g ∈ l, g ≠ .mk)
    (hend : p (T.tp t (l.length + 1)) = false) (h1 : T.hd t = 1) (hT : T.Within B)
    (hB : l.length + 3 ≤ B) :
    ∃ T', Spec (appendCell t p g) x B T T' ∧ T'.tp t 0 = .mk ∧
      seg (T'.tp t) 1 (l.length + 1) = l ++ [g] ∧ T'.tp t (l.length + 2) = .blank ∧
      T'.hd t = 1 ∧ T.Agree (fun i => i = t) T' ∧ T'.ih = T.ih ∧ T'.Within B := by
  have hmb : (Sym.mk : Sym Λ Γ) ≠ .blank := fun h => by cases h
  set n := l.length
  have hs := Spec.scanRight (x := x) t p n T
    (fun j hj => by rw [h1]; exact hp _ (by rw [← hseg]; exact mem_seg _ hj))
    (by rw [h1, Nat.add_comm]; exact hend) hT (by rw [h1]; omega)
  set T₁ := T.setHead t (T.hd t + n)
  have hW₁ : T₁.Within B := Tapes.within_setHead hT (by rw [h1]; omega)
  have hT₁hd : T₁.hd t = n + 1 := by simp [T₁, h1]; omega
  have s2 := Spec.write (x := x) (t := t) (g := g) hW₁
  have hW₂ := Tapes.within_write (t := t) (g := g) hW₁
  have s3 := Spec.moveRight (x := x) (t := t) hW₂ (by simp [hT₁hd]; omega)
  set T₃ := (T₁.write t g).setHead t ((T₁.write t g).hd t + 1)
  have hW₃ : T₃.Within B := Tapes.within_setHead hW₂ (by simp [hT₁hd]; omega)
  have hT₃hd : T₃.hd t = n + 2 := by simp [T₃, hT₁hd]
  have s4 := Spec.write (x := x) (t := t) (g := (Sym.blank : Sym Λ Γ)) hW₃
  set T₄ := T₃.write t .blank
  have hW₄ : T₄.Within B := Tapes.within_write hW₃
  have hcell : ∀ j, T₄.tp t j = if j = n + 2 then .blank else if j = n + 1 then g else T.tp t j := by
    intro j
    simp only [T₄, T₃, T₁, Tapes.write_tp_self, Tapes.setHead_tp, Tapes.setHead_hd_self,
      Tapes.write_hd, hT₁hd]
    split_ifs <;> first | rfl | omega
  have hseg₄ : seg (T₄.tp t) 1 (n + 1) = l ++ [g] := by
    rw [seg_append]
    rw [seg_congr (g := T.tp t) (fun j h1 h2 => by rw [hcell]; rw [ite_neg' (by omega),
      ite_neg' (by omega)])]
    rw [hseg]; simp [seg, hcell, Nat.add_comm]
  have h0₄ : T₄.tp t 0 = .mk := by
    rw [hcell, ite_neg' (by omega), ite_neg' (by omega)]; exact h0
  have hh := Spec.home (x := x) t .mk (T := T₄) h0₄
    (by
      intro j hj1 hj2
      rw [hcell]
      split_ifs
      · exact fun h => by cases h
      · exact hgm
      · have : j ≤ n := by simp [T₄, hT₃hd] at hj2; omega
        rw [← hseg] at hml
        exact hml _ (by
          have := mem_seg (T.tp t) (s := 1) (n := n) (i := j - 1) (by omega)
          rwa [show 1 + (j - 1) = j by omega] at this))
    hW₄ (by omega)
  refine ⟨T₄.setHead t 1, (((hs.seq s2).seq s3).seq s4).seq hh, ?_, ?_, ?_, by simp, ?_, rfl,
    Tapes.within_setHead hW₄ (by omega)⟩
  · simp only [Tapes.setHead_tp]; exact h0₄
  · simp only [Tapes.setHead_tp]; exact hseg₄
  · simp only [Tapes.setHead_tp]; rw [hcell, ite_pos' rfl]
  · intro i hi
    exact ⟨by simp [T₄, T₃, T₁, Tapes.write, hi], by
      simp [T₄, T₃, T₁, Tapes.setHead_hd_ne _ _ hi]⟩

/-! ### Blocks of `c · L` cells -/

noncomputable def copyRep (t : Fin NT) (g : Sym Λ Γ) : ℕ → Code NT (Sym Λ Γ)
  | 0 => []
  | c + 1 => copyMapWhile tRu t isRec (fun _ => g) ++ TM.home tRu .mk ++ copyRep t g c

theorem Spec.copyRep {t : Fin NT} (htR : tRu ≠ t) {g : Sym Λ Γ} {lr : List (Sym Λ Γ)}
    (hrec : ∀ g ∈ lr, isRec g = true) :
    ∀ (c : ℕ) {T : Tapes NT (Sym Λ Γ)}, Lay tRu .mk .blank T lr → T.Within B →
      T.hd t + c * lr.length < B → lr.length + 2 ≤ B →
      ∃ T', Spec (Edge.copyRep t g c) x B T T' ∧
        (∀ j, T'.tp t j = if T.hd t ≤ j ∧ j < T.hd t + c * lr.length then g else T.tp t j) ∧
        T'.hd t = T.hd t + c * lr.length ∧ Lay tRu .mk .blank T' lr ∧
        T.Agree (fun i => i = t) T' ∧ T'.ih = T.ih ∧ T'.Within B
  | 0, T, hRu, hT, _, _ => ⟨T, Spec.nil hT, fun j => by simp, by simp, hRu,
      Tapes.Agree.refl _ T, rfl, hT⟩
  | c + 1, T, hRu, hT, hB₁, hB => by
    have hmb : (Sym.mk : Sym Λ Γ) ≠ .blank := fun h => by cases h
    have hmul : (c + 1) * lr.length = c * lr.length + lr.length := Nat.succ_mul _ _
    have hc := Spec.copyMapWhile (x := x) htR isRec (fun _ => g) lr.length T
      (fun j hj => hrec _ (hRu.cell hj)) (by rw [hRu.endCell]; rfl) hT
      (by rw [hRu.2.2.2]; omega) (by omega)
    have hW₁ : (T.copyMapRes tRu t (fun _ => g) lr.length).Within B := hc.target_within
    have hT₁R : (T.copyMapRes tRu t (fun _ => g) lr.length).tp tRu = T.tp tRu :=
      Tapes.copyMapRes_tp_ne htR T _
    have hh := Spec.home (x := x) tRu .mk (T := T.copyMapRes tRu t (fun _ => g) lr.length)
      (by rw [hT₁R]; exact hRu.1)
      (by rw [hT₁R, Tapes.copyMapRes_hd_a htR, hRu.2.2.2]
          exact home_ok hmb (fun g hg => by
            have := hrec g hg; intro h; subst h; simp [isRec] at this) hRu.2.1 hRu.2.2.1
            (by omega))
      hW₁ (by omega)
    have hW₂ := Tapes.within_setHead (t := tRu) (n := 1) hW₁ (by omega)
    have hRu₂ : Lay tRu .mk .blank ((T.copyMapRes tRu t (fun _ => g) lr.length).setHead tRu 1) lr :=
      hRu.congr (by simp [hT₁R]) (by simp [hRu.2.2.2])
    have hT₂hd : ((T.copyMapRes tRu t (fun _ => g) lr.length).setHead tRu 1).hd t =
        T.hd t + lr.length := by
      rw [Tapes.setHead_hd_ne _ _ (Ne.symm htR)]; exact Tapes.copyMapRes_hd_b T _
    obtain ⟨T₃, s3, hc3, hhd3, hRu₃, ag3, ih3, hW₃⟩ :=
      Spec.copyRep htR hrec c hRu₂ hW₂ (by rw [hT₂hd]; omega) hB
    refine ⟨T₃, (hc.seq hh).seq s3, ?_, by rw [hhd3, hT₂hd, hmul]; omega, hRu₃, ?_, by
      rw [ih3]; rfl, hW₃⟩
    · intro j
      rw [hc3, hT₂hd, hmul]
      simp only [Tapes.setHead_tp, Tapes.copyMapRes, Function.update_self]
      split_ifs <;> first | rfl | omega
    · intro i hi
      refine ⟨(ag3 i hi).1.trans ?_, (ag3 i hi).2.trans ?_⟩
      · simp only [Tapes.setHead_tp]; exact Tapes.copyMapRes_tp_ne (h := fun _ => g) hi T _
      · by_cases hiR : i = tRu
        · subst hiR; simp [hRu.2.2.2]
        · rw [Tapes.setHead_hd_ne _ _ hiR]
          exact Tapes.copyMapRes_hd_ne (h := fun _ => g) hiR hi T _

/-- A block of `c · L` copies of `g` on tape `t`. -/
noncomputable def makeBlockN (t : Fin NT) (g : Sym Λ Γ) (c : ℕ) : Code NT (Sym Λ Γ) :=
  copyRep t g c ++ [Instr.write t .blank] ++ TM.home t .mk

theorem Spec.makeBlockN {t : Fin NT} (htR : tRu ≠ t) {g : Sym Λ Γ} (hgm : g ≠ .mk) (c : ℕ)
    {lr : List (Sym Λ Γ)} {T : Tapes NT (Sym Λ Γ)} (hRu : Lay tRu .mk .blank T lr)
    (hrec : ∀ g ∈ lr, isRec g = true) (h0 : T.tp t 0 = .mk) (h1 : T.hd t = 1)
    (hT : T.Within B) (hB : c * lr.length + lr.length + 3 ≤ B) :
    ∃ T', Spec (makeBlockN t g c) x B T T' ∧
      Lay t .mk .blank T' (List.replicate (c * lr.length) g) ∧ Lay tRu .mk .blank T' lr ∧
      T.Agree (fun i => i = t) T' ∧ T'.ih = T.ih ∧ T'.Within B := by
  have hmb : (Sym.mk : Sym Λ Γ) ≠ .blank := fun h => by cases h
  set m := c * lr.length
  obtain ⟨T₁, s1, hc1, hhd1, hRu₁, ag1, ih1, hW₁⟩ :=
    Spec.copyRep (x := x) (g := g) htR hrec c hRu hT (by rw [h1]; omega) (by omega)
  rw [h1] at hc1 hhd1
  have s2 := Spec.write (x := x) (t := t) (g := (Sym.blank : Sym Λ Γ)) hW₁
  set T₂ := T₁.write t .blank
  have hW₂ : T₂.Within B := Tapes.within_write hW₁
  have hcell : ∀ j, T₂.tp t j = if j = 1 + m then .blank else if 1 ≤ j ∧ j < 1 + m then g
      else T.tp t j := by
    intro j
    simp only [T₂, Tapes.write_tp_self, hhd1, hc1]; rfl
  have hseg : seg (T₂.tp t) 1 m = List.replicate m g := by
    rw [seg_ofFn, ← List.ofFn_const]
    congr 1; funext j
    rw [hcell, ite_neg' (by omega), ite_pos' (by omega)]
  have hrl : (List.replicate m g).length = m := List.length_replicate
  have hh := Spec.home (x := x) t .mk (T := T₂)
    (by rw [hcell, ite_neg' (by omega), ite_neg' (by omega)]; exact h0)
    (by
      intro j hj1 hj2
      rw [hcell]
      split_ifs
      · exact fun h => by cases h
      · exact hgm
      · simp only [T₂, Tapes.write_hd, hhd1] at hj2; omega)
    hW₂ (by omega)
  refine ⟨T₂.setHead t 1, (s1.seq s2).seq hh, ⟨?_, ?_, ?_, by simp⟩, ?_, ?_, ?_,
    Tapes.within_setHead hW₂ (by omega)⟩
  · simp only [Tapes.setHead_tp]; rw [hcell, ite_neg' (by omega), ite_neg' (by omega)]; exact h0
  · simp only [Tapes.setHead_tp]; rw [hrl]; exact hseg
  · simp only [Tapes.setHead_tp]; rw [hrl, hcell, ite_pos' (by omega)]
  · refine hRu₁.congr ?_ ?_
    · simp [T₂, Tapes.write, htR]
    · rw [Tapes.setHead_hd_ne _ _ htR]; rfl
  · intro i hi
    exact ⟨by simp [T₂, Tapes.write, hi, (ag1 i hi).1],
      by rw [Tapes.setHead_hd_ne _ _ hi]; exact (ag1 i hi).2⟩
  · show T₁.ih = T.ih; exact ih1

end Savitch.Edge
