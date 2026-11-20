import Savitch.Edge.Test
import Savitch.Machine.Width

/-!
# The escape test

Phase 4b-6 of the Savitch formalization (see `PLAN.md`).

`escTest M` decides `M.Escapes x (decV v)` for the block on `tU`: whether some move
of `M` from the decoded configuration leaves the block. It shares the edge test's
front end (seek, mark the head, build the key) and then, for each move, runs only
`markMove` and records an out-of-range move on `tR` (`Spec.escTest`).
-/

set_option linter.unusedSectionVars false

namespace Savitch.Edge

open TM Machine Machine.NTM

variable {Λ Γ : Type} [Fintype Λ] [Fintype Γ] [DecidableEq Λ] [DecidableEq Γ]
variable {x : List Bool} {B : ℕ}

theorem nextB_eq_none_iff {n L : ℕ} (b : BCfg Λ Γ n L) (t : Λ × Γ × Dir × Dir) :
    nextB b t = none ↔ ¬ moveWork b.2.2.1.val t.2.2.2 < L := by
  unfold nextB; split_ifs with h <;> simp [h]

/-- The `A₂` part of the scratch invariant. -/
def A₂Inv (L : ℕ) (T : Tapes NT (Sym Λ Γ)) : Prop :=
  ∃ l : List Bool, LayW tA₂ .mk T (l.map bit) ∧ l.length = L ∧
    T.tp tA₂ (L + 1) ≠ .z ∧ T.tp tA₂ (L + 1) ≠ .o

/-- One move: flag it on `tR` if it leaves the block. -/
noncomputable def escCheck (t : Λ × Γ × Dir × Dir) : Code NT (Sym Λ Γ) :=
  markMove t.2.2.2 tA₁ tA₂ tG ++
    ifElse (.tape tG (fun g => decide (g = .yes))) [] [Instr.write tR .yes]

theorem Spec.escCheck {L : ℕ} (w : Fin L) (t : Λ × Γ × Dir × Dir) {T : Tapes NT (Sym Λ Γ)}
    (hA₁ : Lay tA₁ .mk .blank T ((List.ofFn fun j : Fin L => decide (j = w)).map bit))
    (hA₂ : A₂Inv L T) (hT : T.Within B) (hB : L + 2 ≤ B) :
    ∃ T', Spec (Edge.escCheck t) x B T T' ∧
      T'.tp tR (T.hd tR) = (if moveWork w.val t.2.2.2 < L then T.tp tR (T.hd tR) else .yes) ∧
      Lay tA₁ .mk .blank T' ((List.ofFn fun j : Fin L => decide (j = w)).map bit) ∧
      A₂Inv L T' ∧ T.Agree (fun i => i = tA₂ ∨ i = tG ∨ i = tR) T' ∧ T'.hd tR = T.hd tR ∧
      T'.ih = T.ih ∧ T'.Within B := by
  obtain ⟨l₂, hA₂, hl₂, hz, ho⟩ := hA₂
  obtain ⟨T₁, s1, hA₁₁, hG₁, _, ⟨l₄, hA₂₁, hl₄⟩, hend₁, _, ag1, hGhd₁, ih1, hW₁⟩ :=
    Spec.markMove (x := x) (A₁ := tA₁) (A₂ := tA₂) (G := tG) (by decide) (by decide) (by decide)
      t.2.2.2 w hA₁ hA₂ (by simp [hl₂]) hz ho hT hB
  have hTG : T₁.read tG = (if moveWork w.val t.2.2.2 < L then .yes else .no) := by
    rw [Tapes.read, hGhd₁]; exact hG₁
  have hA₂I : A₂Inv L T₁ := ⟨l₄, hA₂₁, hl₄, by rw [hend₁]; exact hz, by rw [hend₁]; exact ho⟩
  have hR₁ := ag1 tR (by decide)
  by_cases hr : moveWork w.val t.2.2.2 < L
  · refine ⟨T₁, s1.seq (Spec.ifElse_true (by simp [Cond.eval, hTG, hr]) hW₁ (Spec.nil hW₁)),
      by rw [ite_pos' hr, hR₁.1], hA₁₁, hA₂I, ag1.mono (fun i h => by
        rcases h with h | h <;> simp [h]), hR₁.2, ih1, hW₁⟩
  · have s2 := Spec.write (x := x) (t := tR) (g := (Sym.yes : Sym Λ Γ)) hW₁
    refine ⟨T₁.write tR .yes, s1.seq (Spec.ifElse_false (by simp [Cond.eval, hTG, hr]) hW₁ s2),
      ?_, agree_lay (fun i hi => ⟨by simp [Tapes.write, hi], rfl⟩ :
        T₁.Agree (fun i => i = tR) (T₁.write tR .yes)) (by decide) hA₁₁, ?_, ?_, by simp [hR₁.2],
      ih1, Tapes.within_write hW₁⟩
    · rw [ite_neg' hr, Tapes.write_tp_self, hR₁.2, ite_pos' rfl]
    · obtain ⟨l, h1, h2, h3, h4⟩ := hA₂I
      exact ⟨l, h1.congr (by simp [Tapes.write, show tA₂ ≠ tR by decide]) rfl, h2,
        by simpa [Tapes.write, show tA₂ ≠ tR by decide] using h3,
        by simpa [Tapes.write, show tA₂ ≠ tR by decide] using h4⟩
    · intro i hi
      have g := ag1 i (fun h => hi (by rcases h with h | h <;> simp [h]))
      have hiR : i ≠ tR := fun e => hi (Or.inr (Or.inr e))
      exact ⟨by simp [Tapes.write, hiR, g.1], g.2⟩

/-- Check every move in the list. -/
noncomputable def escChecksL : List (Λ × Γ × Dir × Dir) → Code NT (Sym Λ Γ)
  | [] => []
  | t :: ts => escCheck t ++ escChecksL ts

theorem Spec.escChecksL {L : ℕ} (w : Fin L) :
    ∀ (ts : List (Λ × Γ × Dir × Dir)) {T : Tapes NT (Sym Λ Γ)},
    Lay tA₁ .mk .blank T ((List.ofFn fun j : Fin L => decide (j = w)).map bit) →
    A₂Inv L T → T.Within B → L + 2 ≤ B →
    ∃ T', Spec (Edge.escChecksL ts) x B T T' ∧
      T'.tp tR (T.hd tR) = (if (∃ t ∈ ts, ¬ moveWork w.val t.2.2.2 < L) then .yes
        else T.tp tR (T.hd tR)) ∧
      Lay tA₁ .mk .blank T' ((List.ofFn fun j : Fin L => decide (j = w)).map bit) ∧
      A₂Inv L T' ∧ T.Agree (fun i => i = tA₂ ∨ i = tG ∨ i = tR) T' ∧ T'.hd tR = T.hd tR ∧
      T'.ih = T.ih ∧ T'.Within B
  | [], T, hA₁, hA₂, hT, _ => ⟨T, Spec.nil hT, by simp, hA₁, hA₂, Tapes.Agree.refl _ T, rfl, rfl, hT⟩
  | t :: ts, T, hA₁, hA₂, hT, hB => by
    obtain ⟨T₁, s1, hR₁, hA₁₁, hA₂₁, ag1, hRhd₁, ih1, hW₁⟩ :=
      Spec.escCheck (x := x) w t hA₁ hA₂ hT hB
    obtain ⟨T₂, s2, hR₂, hA₁₂, hA₂₂, ag2, hRhd₂, ih2, hW₂⟩ :=
      Spec.escChecksL w ts hA₁₁ hA₂₁ hW₁ hB
    refine ⟨T₂, s1.seq s2, ?_, hA₁₂, hA₂₂, ag1.trans ag2, by rw [hRhd₂, hRhd₁],
      by rw [ih2, ih1], hW₂⟩
    rw [hRhd₁] at hR₂
    rw [hR₂, hR₁]
    have hcons : (∃ t' ∈ t :: ts, ¬ moveWork w.val t'.2.2.2 < L) ↔
        (¬ moveWork w.val t.2.2.2 < L) ∨ ∃ t' ∈ ts, ¬ moveWork w.val t'.2.2.2 < L := by
      constructor
      · rintro ⟨t', ht', h⟩
        rcases List.mem_cons.1 ht' with rfl | ht'
        · exact Or.inl h
        · exact Or.inr ⟨t', ht', h⟩
      · rintro (h | ⟨t', ht', h⟩)
        · exact ⟨t, List.mem_cons_self, h⟩
        · exact ⟨t', List.mem_cons_of_mem _ ht', h⟩
    by_cases h1 : moveWork w.val t.2.2.2 < L
    · rw [ite_pos' h1]
      by_cases h2 : ∃ t' ∈ ts, ¬ moveWork w.val t'.2.2.2 < L
      · rw [ite_pos' h2, ite_pos' (hcons.2 (Or.inr h2))]
      · rw [ite_neg' h2, ite_neg' (fun h => (hcons.1 h).elim (fun h' => h' h1) h2)]
    · rw [ite_neg' h1, ite_pos' (hcons.2 (Or.inl h1))]
      split_ifs <;> rfl

noncomputable def perKeyE (M : NTM Λ Γ) : Code NT (Sym Λ Γ) :=
  TM.cases tK (fun g => match g with
    | .key q i g' => escChecksL (M.δ q i g')
    | _ => []) Finset.univ.toList

/-- **The escape test.** -/
noncomputable def escTest (M : NTM Λ Γ) : Code NT (Sym Λ Γ) :=
  TM.rewindIn tP tF .mk .z .o .yes .no ++ [Instr.write tR .no] ++
    copyPass tU tCU .mk isRec ihSym ++ TM.seekIn tCU tP tF .mk .z .o .yes .no ++
    markFirst tU tA₁ ++ buildKey M.blank tU tK tA₁ ++ perKeyE M

open Classical in
theorem Spec.escTest (M : NTM Λ Γ) {L : ℕ} (hL : 0 < L) (_hfit : x.length + 1 < 2 ^ L)
    (u : Fin (nV Λ Γ L)) {T : Tapes NT (Sym Λ Γ)}
    (hU : Lay tU .mk .blank T ((List.ofFn (recs u)).map .rc))
    (hI : EInv (x := x) L T) (hT : T.Within B) (hB : L + 2 ≤ B) :
    ∃ T', Spec (escTest M) x B T T' ∧
      T'.tp tR (T.hd tR) = (if M.Escapes x (decV (n := x.length) hL u) then (Sym.yes : Sym Λ Γ)
        else .no) ∧
      Lay tU .mk .blank T' ((List.ofFn (recs u)).map .rc) ∧ EInv (x := x) L T' ∧
      T.Agree (fun i => i = tS ∨ i = tA₁ ∨ i = tA₂ ∨ i = tP ∨ i = tP₂ ∨ i = tCU ∨ i = tK ∨
        i = tF ∨ i = tF₂ ∨ i = tG ∨ i = tR) T' ∧
      T'.hd tR = T.hd tR ∧ T'.Within B := by
  obtain ⟨⟨la, hA₁, hla⟩, ⟨lp, hP, hlp⟩, ⟨lc, hC, hlc⟩, hSc⟩ := hI
  have hzo : (Sym.z : Sym Λ Γ) ≠ .o := fun h => by cases h
  have hmz : (Sym.mk : Sym Λ Γ) ≠ .z := fun h => by cases h
  have hmo : (Sym.mk : Sym Λ Γ) ≠ .o := fun h => by cases h
  have hyn : (Sym.yes : Sym Λ Γ) ≠ .no := fun h => by cases h
  have hmb : (Sym.mk : Sym Λ Γ) ≠ .blank := fun h => by cases h
  have hBl : lp.length + 2 ≤ B := by rw [hlp]; exact hB
  -- 0. rewind the input head
  obtain ⟨T₀, lp₀, s0, hP₀, hlp₀, hih₀, ag0, hF₀, hW₀⟩ :=
    Spec.rewindIn (x := x) (P := tP) (F := tF) (by decide) hzo hmz hmo hyn hP hT hBl
  -- 1. clear the result
  have s1 := Spec.write (x := x) (t := tR) (g := (Sym.no : Sym Λ Γ)) hW₀
  set T₁ := T₀.write tR .no
  have hW₁ : T₁.Within B := Tapes.within_write hW₀
  have ag1 : T₀.Agree (fun i => i = tR) T₁ := fun i hi => ⟨by simp [T₁, Tapes.write, hi], rfl⟩
  have agT1 : T.Agree (fun i => i = tP ∨ i = tF ∨ i = tR) T₁ :=
    (ag0.mono (fun i h => by rcases h with h | h <;> simp [h])).trans
      (ag1.mono (fun i h => by simp [h]))
  have hU₁ := agree_lay agT1 (by decide) hU
  have hA₁₁ := agree_lay agT1 (by decide) hA₁
  have hC₁ : Holds tCU .mk .z .o T₁ lc :=
    hC.congr (agT1 tCU (by decide)).1 (agT1 tCU (by decide)).2
  have hP₁ : InPos tP .mk .z .o x T₁ lp₀ :=
    ⟨hP₀.1.congr (ag1 tP (by decide)).1 (ag1 tP (by decide)).2, hP₀.2.1, hP₀.2.2.1, hP₀.2.2.2⟩
  have hih₁ : T₁.ih = 0 := hih₀
  have hR₁ : T₁.tp tR (T.hd tR) = .no := by
    simp only [T₁, Tapes.write_tp_self]
    rw [ite_pos' (by rw [(ag0 tR (by decide)).2])]
  have hRhd₁ : T₁.hd tR = T.hd tR := by simp [T₁, (ag0 tR (by decide)).2]
  -- 2. extract the input-position bits of `u`
  set ihl := List.ofFn fun j : Fin L => (recs u j).2.2.1 with hihl
  have hmap : ((List.ofFn (recs u)).map (Sym.rc (Λ := Λ) (Γ := Γ))).map ihSym = ihl.map bit := by
    rw [List.map_map, List.map_ofFn, hihl, List.map_ofFn]; rfl
  have hlu : ((List.ofFn (recs u)).map (Sym.rc (Λ := Λ) (Γ := Γ))).length = L := by simp
  obtain ⟨T₂, s2, hUw₂, hCw₂, hUtp₂, hCend₂, ag2, ih2, hW₂⟩ :=
    Spec.copyPassW (x := x) (p := isRec) (h := ihSym) (show tU ≠ tCU by decide) (hU₁.toW hmb)
      (by rw [hU₁.2.2.1]; rfl) hC₁.toW (by simp [hlc]) isRec_rec not_mk_rec
      (fun g hg => by obtain ⟨r, _, rfl⟩ := List.mem_map.1 hg; exact bit_ne_mk _) hW₁
      (by rw [hlu]; exact hB)
  rw [hmap] at hCw₂
  rw [hlu] at hCend₂
  have hihll : ihl.length = L := by simp [ihl]
  have hC₂ : Holds tCU .mk .z .o T₂ ihl := Holds.ofW hCw₂
    (by rw [hihll, hCend₂, ← hlc]; exact hC₁.2.2.1) (by rw [hihll, hCend₂, ← hlc]; exact hC₁.2.2.2.1)
  have hP₂ : InPos tP .mk .z .o x T₂ lp₀ :=
    ⟨hP₁.1.congr (ag2 tP (by decide)).1 (ag2 tP (by decide)).2, by rw [ih2]; exact hP₁.2.1,
      by rw [ih2]; exact hP₁.2.2.1, hP₁.2.2.2⟩
  -- 3. seek to `u`'s input position
  obtain ⟨T₃, lp₃, lc₃, s3, hP₃, hlp₃, hih₃, hC₃, hlc₃, _, ag3, hF₃, hW₃⟩ :=
    Spec.seekIn (x := x) (C := tCU) (P := tP) (F := tF) (by decide) (by decide) (by decide)
      hzo hmz hmo hyn hC₂ hP₂ hW₂ (by rw [hihll]; exact hB) (by rw [hlp₀, hlp]; exact hB)
  have hih₃' : T₃.ih = (decV (n := x.length) hL u).2.1.val := by
    rw [hih₃, ih2, hih₁]; simp [decV, decR, ihl]
  have agT3 : T₁.Agree (fun i => i = tCU ∨ i = tP ∨ i = tF) T₃ :=
    (ag2.mono (fun i h => by simp [h])).trans ag3
  have hU₃ := agree_lay agT3 (by decide) hU₁
  have hA₁₃ := agree_lay agT3 (by decide) hA₁₁
  -- 4. mark the work head
  obtain ⟨T₄, s4, hU₄, hA₁₄, ag4, ih4, hW₄⟩ :=
    Spec.markFirst (x := x) (U := tU) (A := tA₁) (by decide) hL (recs u) hU₃ hA₁₃ hla hW₃ hB
  -- 5. build the key cell
  obtain ⟨T₅, s5, hK₅, hU₅, hA₁₅, ag5, hKhd₅, ih5, hW₅⟩ :=
    Spec.buildKey (x := x) M.blank (U := tU) (K := tK) (A₁ := tA₁) (by decide) (by decide)
      (by decide) hL (recs u) hU₄ hA₁₄ hW₄ hB
  have agT5 : T₃.Agree (fun i => i = tA₁ ∨ i = tK) T₅ :=
    (ag4.mono (fun i h => by simp [h])).trans (ag5.mono (fun i h => by simp [h]))
  have hP₅ : InPos tP .mk .z .o x T₅ lp₃ :=
    ⟨hP₃.1.congr (agT5 tP (by decide)).1 (agT5 tP (by decide)).2,
      by rw [ih5, ih4]; exact hP₃.2.1, by rw [ih5, ih4]; exact hP₃.2.2.1, hP₃.2.2.2⟩
  have hih₅ : T₅.ih = (decV (n := x.length) hL u).2.1.val := by rw [ih5, ih4, hih₃']
  have hSc₅ : Scratch L T₅ := by
    obtain ⟨⟨ls, hS, hls, hlsm⟩, ⟨l₂, hA₂, hl₂, hA₂z, hA₂o⟩, ⟨l₃, hP₂', hl₃⟩⟩ := hSc
    have agT : T.Agree (fun i => i = tP ∨ i = tF ∨ i = tR ∨ i = tCU ∨ i = tA₁ ∨ i = tK) T₅ :=
      ((agT1.mono (fun i h => by rcases h with h | h | h <;> simp [h])).trans
        (agT3.mono (fun i h => by rcases h with h | h | h <;> simp [h]))).trans
        (agT5.mono (fun i h => by rcases h with h | h <;> simp [h]))
    refine ⟨⟨ls, agree_lay agT (by decide) hS, hls, hlsm⟩,
      ⟨l₂, agree_layW agT (by decide) hA₂, hl₂, by rw [(agT tA₂ (by decide)).1]; exact hA₂z,
        by rw [(agT tA₂ (by decide)).1]; exact hA₂o⟩,
      ⟨l₃, hP₂'.congr (agT tP₂ (by decide)).1 (agT tP₂ (by decide)).2, hl₃⟩⟩
  have hR₅ : T₅.tp tR (T.hd tR) = .no := by
    rw [(agT5 tR (by decide)).1, (agT3 tR (by decide)).1, hR₁]
  have hRhd₅ : T₅.hd tR = T.hd tR := by
    rw [(agT5 tR (by decide)).2, (agT3 tR (by decide)).2, hRhd₁]
  -- 6. dispatch on the key and run the checks
  set q := (recs u ⟨0, hL⟩).2.2.2
  set g := (recs u (firstFlag hL (recs u))).1
  have hread : T₅.read tK = .key q (inputSym x T₅.ih) g := by
    rw [Tapes.read, hKhd₅, hK₅, ih5]
  obtain ⟨⟨ls, hS₅, hls, hlsm⟩, hA₂₅, ⟨l₃, hP₂₅, hl₃⟩⟩ := hSc₅
  obtain ⟨T₆, s6, hR₆, hA₁₆, hA₂₆, ag6, hRhd₆, ih6, hW₆⟩ :=
    Spec.escChecksL (x := x) (firstFlag hL (recs u)) (M.δ q (inputSym x T₅.ih) g) hA₁₅ hA₂₅ hW₅ hB
  have s6' : Spec (perKeyE M) x B T₅ T₆ :=
    Spec.cases tK _ Finset.univ.toList (by simp) hW₅ (by rw [hread]; exact s6)
  have hE : (∃ t ∈ M.δ q (inputSym x T₅.ih) g, ¬ moveWork (firstFlag hL (recs u)).val t.2.2.2 < L)
      ↔ M.Escapes x (decV (n := x.length) hL u) := by
    rw [hih₅]
    unfold Escapes
    exact exists_congr fun t => and_congr_right fun _ =>
      (nextB_eq_none_iff (decV (n := x.length) hL u) t).symm
  have hC₆ : Holds tCU .mk .z .o T₆ lc₃ :=
    hC₃.congr ((ag6 tCU (by decide)).1.trans (agT5 tCU (by decide)).1)
      ((ag6 tCU (by decide)).2.trans (agT5 tCU (by decide)).2)
  refine ⟨T₆, (((((s0.seq s1).seq s2).seq s3).seq s4).seq s5).seq s6', ?_,
    agree_lay ag6 (by decide) hU₅, ⟨⟨_, hA₁₆, by simp⟩,
      ⟨lp₃, ⟨hP₅.1.congr (ag6 tP (by decide)).1 (ag6 tP (by decide)).2,
        by rw [ih6]; exact hP₅.2.1, by rw [ih6]; exact hP₅.2.2.1, hP₅.2.2.2⟩,
        by rw [hlp₃, hlp₀, hlp]⟩,
      ⟨lc₃, hC₆, by rw [hlc₃, hihll]⟩,
      ⟨⟨ls, agree_lay ag6 (by decide) hS₅, hls, hlsm⟩, hA₂₆,
        ⟨l₃, hP₂₅.congr (ag6 tP₂ (by decide)).1 (ag6 tP₂ (by decide)).2, hl₃⟩⟩⟩, ?_,
    hRhd₆.trans hRhd₅, hW₆⟩
  · rw [hRhd₅] at hR₆
    rw [hR₆, hR₅]
    exact if_congr hE rfl rfl
  · exact (((agT1.mono (fun i h => by rcases h with h | h | h <;> simp [h])).trans
      (agT3.mono (fun i h => by rcases h with h | h | h <;> simp [h]))).trans
      (agT5.mono (fun i h => by rcases h with h | h <;> simp [h]))).trans
      (ag6.mono (fun i h => by rcases h with h | h | h <;> simp [h]))

end Savitch.Edge
