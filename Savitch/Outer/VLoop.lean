import Savitch.Outer.Vertex

/-!
# The loop over all vertices

Phase 4b-6 of the Savitch formalization (see `PLAN.md`).

`vLoop M` walks the register `tW` through every vertex (`incBlk`, wraparound
detected by `cmpZ`), running `perVertex` on each. Afterwards `tEsc` reads `yes` iff
some vertex reachable from the start block escapes, and `tAcc` reads `yes` iff some
reachable vertex is accepting (`Spec.vLoop`).
-/

set_option linter.unusedSectionVars false

namespace Savitch.Edge

open TM Machine Machine.NTM

variable {Λ Γ : Type} [Fintype Λ] [Fintype Γ] [DecidableEq Λ] [DecidableEq Γ]
variable {x : List Bool} {B : ℕ} {L : ℕ}

noncomputable def incBlk [NeZero (nR Λ Γ)] (t : Fin NT) : Code NT (Sym Λ Γ) :=
  TM.incrD t symR ++ TM.home t .mk

theorem Spec.incBlk [NeZero (nR Λ Γ)] (t : Fin NT) {l : List (Fin (nR Λ Γ))} {T : Tapes NT (Sym Λ Γ)}
    (hV : Lay t .mk .blank T (cellsOf l)) (hT : T.Within B) (hB : l.length + 2 ≤ B) :
    ∃ T', Spec (incBlk (Λ := Λ) (Γ := Γ) t) x B T T' ∧ Lay t .mk .blank T' (cellsOf (dinc l)) ∧
      T.Agree (fun i => i = t) T' ∧ T'.ih = T.ih ∧ T'.Within B := by
  have hmb : (Sym.mk : Sym Λ Γ) ≠ .blank := fun h => by cases h
  have hcl := cellsOf_length (Λ := Λ) (Γ := Γ) l
  obtain ⟨T₁, s1, p1, p2, p3, p4⟩ := Spec.incrD (x := x) (t := t) symR_inj l T
    (by rw [hV.2.2.2]; have := hV.2.1; rwa [hcl] at this)
    (fun d => by
      rw [hV.2.2.2, Nat.add_comm]; have := hV.2.2.1; rw [hcl] at this; rw [this]
      exact fun h => by simp [symR] at h)
    hT (by rw [hV.2.2.2]; omega)
  rw [hV.2.2.2] at p1 p2 p4
  have hW₁ : T₁.Within B := fun i => by
    by_cases hi : i = t
    · subst hi; omega
    · rw [(p3.2 i hi).2]; exact hT i
  have hdl := dinc_length l
  have hcl' := cellsOf_length (Λ := Λ) (Γ := Γ) (dinc l)
  have hh := Spec.home (x := x) t .mk (T := T₁) (by rw [p2 0 (Or.inl (by omega))]; exact hV.1)
    (home_ok (l := cellsOf (dinc l)) hmb (cellsOf_not_mk _) (by rw [hcl', hdl]; exact p1)
      (by rw [hcl', hdl, p2 _ (Or.inr (by omega))]; have := hV.2.2.1; rwa [hcl] at this)
      (by rw [hcl', hdl]; omega))
    hW₁ (by omega)
  refine ⟨T₁.setHead t 1, s1.seq hh, ⟨?_, ?_, ?_, by simp⟩, ?_, ?_,
    Tapes.within_setHead hW₁ (by omega)⟩
  · simp only [Tapes.setHead_tp]; rw [p2 0 (Or.inl (by omega))]; exact hV.1
  · simp only [Tapes.setHead_tp]; rw [hcl', hdl]; exact p1
  · simp only [Tapes.setHead_tp]; rw [hcl', hdl, p2 _ (Or.inr (by omega))]
    have := hV.2.2.1; rwa [hcl] at this
  · intro i hi
    exact ⟨(p3.2 i hi).1, by rw [Tapes.setHead_hd_ne _ _ hi]; exact (p3.2 i hi).2⟩
  · exact p3.1

/-! ### Comparing a block with zero -/

noncomputable def cmpZ (t f : Fin NT) : Code NT (Sym Λ Γ) :=
  cmpD t tZ f symR .yes .no ++ TM.home t .mk ++ TM.home tZ .mk

theorem Spec.cmpZ [NeZero (nV Λ Γ L)] {t f : Fin NT} (htZ : t ≠ tZ) (htf : t ≠ f) (hZf : tZ ≠ f)
    {l : List (Fin (nR Λ Γ))} (hl : l.length = L) {T : Tapes NT (Sym Λ Γ)}
    (ht : Lay t .mk .blank T (cellsOf l))
    (hZ : Lay tZ .mk .blank T (cellsOf (digs (Gen.zero : Fin (nV Λ Γ L)))))
    (hT : T.Within B) (hB : L + 2 ≤ B) :
    ∃ T', Spec (cmpZ (Λ := Λ) (Γ := Γ) t f) x B T T' ∧
      T'.tp f (T.hd f) = (if l = digs (Gen.zero : Fin (nV Λ Γ L)) then .yes else .no) ∧
      Lay t .mk .blank T' (cellsOf l) ∧
      Lay tZ .mk .blank T' (cellsOf (digs (Gen.zero : Fin (nV Λ Γ L)))) ∧
      T.Agree (fun i => i = f) T' ∧ T'.hd f = T.hd f ∧ T'.ih = T.ih ∧ T'.Within B := by
  have hmb : (Sym.mk : Sym Λ Γ) ≠ .blank := fun h => by cases h
  have hl2 := digs_length (Gen.zero : Fin (nV Λ Γ L))
  obtain ⟨T₃, s3, c1, c2, c3, c4, c5, c6, c7⟩ := Spec.cmpD (x := x) (a := t) (b := tZ) (f := f)
    htZ htf hZf symR_inj (yes := .yes) (no := .no) l (digs Gen.zero) T (by rw [hl, hl2])
    (by rw [ht.2.2.2]; have := ht.2.1; rwa [cellsOf_length] at this)
    (by rw [hZ.2.2.2]; have := hZ.2.1; rwa [cellsOf_length] at this)
    (fun d => by
      rw [ht.2.2.2, Nat.add_comm, ← cellsOf_length (Λ := Λ) (Γ := Γ), ht.2.2.1]
      exact fun h => by simp [symR] at h)
    hT (by rw [ht.2.2.2, hl]; omega) (by rw [hZ.2.2.2, hl]; omega)
  simp only [Tapes.write_hd] at c1 c2 c4 c5 c6
  have hW₃ : T₃.Within B := s3.target_within
  have hT₃tp : ∀ i, i ≠ f → T₃.tp i = T.tp i := fun i hi => by
    rw [c3 i hi]; simp [Tapes.write, hi]
  have hF : T₃.tp f (T.hd f) = if l = digs (Gen.zero : Fin (nV Λ Γ L)) then .yes else .no := by
    rw [c1]; simp [Tapes.read, Tapes.write_tp_self]
  have hh1 := Spec.home (x := x) t .mk (T := T₃) (by rw [hT₃tp t htf]; exact ht.1)
    (by rw [hT₃tp t htf]
        exact home_ok hmb (cellsOf_not_mk _) ht.2.1 ht.2.2.1
          (by rw [c4, ht.2.2.2, cellsOf_length]; omega))
    hW₃ (by omega)
  set T₄ := T₃.setHead t 1
  have hW₄ : T₄.Within B := Tapes.within_setHead hW₃ (by omega)
  have hh2 := Spec.home (x := x) tZ .mk (T := T₄)
    (by simp only [T₄, Tapes.setHead_tp]; rw [hT₃tp tZ hZf]; exact hZ.1)
    (by simp only [T₄, Tapes.setHead_tp]; rw [hT₃tp tZ hZf]
        exact home_ok hmb (cellsOf_not_mk _) hZ.2.1 hZ.2.2.1
          (by rw [Tapes.setHead_hd_ne _ _ (Ne.symm htZ), c5, hZ.2.2.2, cellsOf_length, hl2, ← hl]
              omega))
    hW₄ (by omega)
  set T₅ := T₄.setHead tZ 1
  have hfhd : T₅.hd f = T.hd f := by
    simp only [T₅, T₄, Tapes.setHead_hd_ne _ _ (Ne.symm hZf), Tapes.setHead_hd_ne _ _ (Ne.symm htf)]
    exact c6 f (Ne.symm htf) (Ne.symm hZf)
  refine ⟨T₅, (s3.seq hh1).seq hh2, by simp only [T₅, T₄, Tapes.setHead_tp]; exact hF,
    ht.congr (by simp only [T₅, T₄, Tapes.setHead_tp]; exact hT₃tp t htf)
      (by simp [T₅, T₄, Tapes.setHead_hd_ne _ _ htZ, ht.2.2.2]),
    hZ.congr (by simp only [T₅, T₄, Tapes.setHead_tp]; exact hT₃tp tZ hZf)
      (by simp [T₅, hZ.2.2.2]), ?_, hfhd, ?_, Tapes.within_setHead hW₄ (by omega)⟩
  · intro i hi
    refine ⟨by simp only [T₅, T₄, Tapes.setHead_tp]; exact hT₃tp i hi, ?_⟩
    by_cases hiZ : i = tZ
    · subst hiZ; simp [T₅, hZ.2.2.2]
    · by_cases hit : i = t
      · subst hit; simp [T₅, T₄, Tapes.setHead_hd_ne _ _ htZ, ht.2.2.2]
      · simp only [T₅, T₄, Tapes.setHead_hd_ne _ _ hiZ, Tapes.setHead_hd_ne _ _ hit]
        exact c6 i hit hiZ
  · show T₃.ih = T.ih; rw [c7]; rfl

/-! ### The loop -/

def Lo₃ (i : Fin NT) : Prop := i.val < 22 ∨ i = tW ∨ i = tEsc ∨ i = tAcc ∨ i = tC₅

instance : DecidablePred Lo₃ := fun i =>
  inferInstanceAs (Decidable (i.val < 22 ∨ i = tW ∨ i = tEsc ∨ i = tAcc ∨ i = tC₅))

noncomputable def vBody [NeZero (nR Λ Γ)] (M : NTM Λ Γ) : Code NT (Sym Λ Γ) :=
  perVertex M ++ incBlk tW ++ cmpZ tW tC₅

noncomputable def vLoop [NeZero (nR Λ Γ)] (M : NTM Λ Γ) : Code NT (Sym Λ Γ) :=
  zipPass tW tZ .mk isRec (fun _ b => b) ++ [Instr.write tEsc .no] ++ [Instr.write tAcc .no] ++
    [Instr.write tC₅ .no] ++ whileDo (.tape tC₅ (fun g => decide (g = .no))) (vBody M)

section

open Classical

variable (M : NTM Λ Γ) (hL : 0 < L) (a : Fin (nV Λ Γ L))

/-- Vertex `u` is reachable and escapes. -/
def EscV (u : Fin (nV Λ Γ L)) : Prop :=
  Relation.ReflTransGen (M.GEdge x hL) a u ∧ M.Escapes x (decV (n := x.length) hL u)

/-- Vertex `u` is reachable and accepting. -/
def AccV (u : Fin (nV Λ Γ L)) : Prop :=
  Relation.ReflTransGen (M.GEdge x hL) a u ∧ (decV (n := x.length) hL u).1 = M.accept

end

open Classical in
theorem vloop_aux [NeZero (nV Λ Γ L)] [NeZero (nR Λ Γ)] (M : NTM Λ Γ) (hL : 0 < L)
    (hfit : x.length + 1 < 2 ^ L) {K WK : ℕ} (hWK : K < 2 ^ WK) (hN : nV Λ Γ L ≤ 2 ^ K)
    (a : Fin (nV Λ Γ L)) (hB : (K + 1) * (L + 1) + WK + 8 ≤ B) (hE hA : ℕ) :
    ∀ (m : ℕ) (c : Fin (nV Λ Γ L)), nV Λ Γ L - c.val = m → ∀ (T : Tapes NT (Sym Λ Γ)) (r₀ : Bool),
      Rep L x K WK T (.done r₀) → Regs K WK a c T → T.read tC₅ = .no →
      T.hd tEsc = hE → T.hd tAcc = hA →
      T.tp tEsc hE = (if ∃ u : Fin (nV Λ Γ L), u.val < c.val ∧ EscV (x := x) M hL a u then .yes
        else .no) →
      T.tp tAcc hA = (if ∃ u : Fin (nV Λ Γ L), u.val < c.val ∧ AccV (x := x) M hL a u then .yes
        else .no) →
      T.Within B →
      ∃ T' r, Loop (.tape tC₅ (fun g => decide (g = (Sym.no : Sym Λ Γ)))) (vBody M) x B T T' ∧
        Rep L x K WK T' (.done r) ∧ (∃ v', Regs K WK a v' T') ∧
        T'.tp tEsc hE = (if ∃ u, EscV (x := x) M hL a u then .yes else .no) ∧
        T'.tp tAcc hA = (if ∃ u, AccV (x := x) M hL a u then .yes else .no) ∧
        T'.hd tEsc = hE ∧ T'.hd tAcc = hA ∧
        T.Agree Lo₃ T' ∧ T'.Within B
  | 0, c, hc, _, _, _, _, _, _, _, _, _, _ => by have := c.isLt; omega
  | m + 1, c, hc, T, r₀, hR, hG, hC, hEh, hAh, hEv, hAv, hT => by
    have hLB : L + 2 ≤ B := by
      have := Nat.le_mul_of_pos_left (L + 1) (show 0 < K + 1 by omega); omega
    -- process `c`
    obtain ⟨T₁, r₁, s1, hR₁, hG₁, hE₁, hA₁, hEhd₁, hAhd₁, ag1, hW₁⟩ :=
      Spec.perVertex (B := B) M hL hfit hWK hN hR hG hT hB
    -- increment `tW`
    obtain ⟨hI₁, hWl₁, hKK₁⟩ := hG₁
    obtain ⟨T₂, s2, hWl₂, ag2, ih2, hW₂⟩ := Spec.incBlk (x := x) tW hWl₁ hW₁
      (by rw [digs_length]; exact hLB)
    -- test for wraparound
    obtain ⟨T₃, s3, hC₃, hWl₃, hZ₃, ag3, hChd₃, ih3, hW₃⟩ := Spec.cmpZ (x := x) (t := tW)
      (f := tC₅) (by decide) (by decide) (by decide) (by rw [dinc_length, digs_length]) hWl₂
      (agree_lay ag2 (by decide) hR₁.2.2.2.2.2.1) hW₂ hLB
    have ag13 : T₁.Agree (fun i => i = tW ∨ i = tC₅) T₃ :=
      (ag2.mono (fun _ h => Or.inl h)).trans (ag3.mono (fun _ h => Or.inr h))
    have hR₃ : Rep L x K WK T₃ (.done r₁) := by
      obtain ⟨hMd, ⟨a₁, hU⟩, ⟨b₁, hV⟩, ⟨w₁, hK⟩, hS, hZ, hEI⟩ := hR₁
      refine ⟨?_, ⟨a₁, agree_lay ag13 (by decide) hU⟩, ⟨b₁, agree_lay ag13 (by decide) hV⟩,
        ⟨w₁, hK.agree ag13 (by decide)⟩, hS.agree ag13 (by decide) (by decide) (by decide)
          (by decide), agree_lay ag13 (by decide) hZ,
        hEI.agree ag13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by rw [ih3, ih2])⟩
      rw [Tapes.read, (ag13 tMd (by decide)).1, (ag13 tMd (by decide)).2]; exact hMd
    have hI₃ := agree_lay ag13 (by decide) hI₁
    have hKK₃ : ∃ l : List Bool, Holds tKK .mk .z .o T₃ l ∧ l.length = WK ∧ bval l = K := by
      obtain ⟨l, h1, h2, h3⟩ := hKK₁
      exact ⟨l, h1.congr (ag13 tKK (by decide)).1 (ag13 tKK (by decide)).2, h2, h3⟩
    -- the flags now cover `c` too
    have hsplit : ∀ P : Fin (nV Λ Γ L) → Prop,
        (∃ u : Fin (nV Λ Γ L), u.val < c.val + 1 ∧ P u) ↔
          (∃ u : Fin (nV Λ Γ L), u.val < c.val ∧ P u) ∨ P c := by
      intro P
      constructor
      · rintro ⟨u, hu, hp⟩
        by_cases h : u.val < c.val
        · exact Or.inl ⟨u, h, hp⟩
        · have : u = c := Fin.ext (by omega)
          exact Or.inr (this ▸ hp)
      · rintro (⟨u, hu, hp⟩ | hp)
        · exact ⟨u, by omega, hp⟩
        · exact ⟨c, by omega, hp⟩
    have hE₃hd : T₃.hd tEsc = hE := by rw [(ag13 tEsc (by decide)).2, hEhd₁, hEh]
    have hA₃hd : T₃.hd tAcc = hA := by rw [(ag13 tAcc (by decide)).2, hAhd₁, hAh]
    have hE₃ : T₃.tp tEsc hE = (if ∃ u : Fin (nV Λ Γ L), u.val < c.val + 1 ∧
        EscV (x := x) M hL a u then .yes else .no) := by
      rw [(ag13 tEsc (by decide)).1, ← hEh, hE₁, hEh, hEv]
      by_cases h1 : EscV (x := x) M hL a c
      · rw [ite_pos' (show Relation.ReflTransGen (M.GEdge x hL) a c ∧
          M.Escapes x (decV (n := x.length) hL c) from h1), ite_pos' ((hsplit _).2 (Or.inr h1))]
      · rw [ite_neg' (show ¬ (Relation.ReflTransGen (M.GEdge x hL) a c ∧
          M.Escapes x (decV (n := x.length) hL c)) from h1)]
        by_cases h2 : ∃ u : Fin (nV Λ Γ L), u.val < c.val ∧ EscV (x := x) M hL a u
        · rw [ite_pos' h2, ite_pos' ((hsplit _).2 (Or.inl h2))]
        · rw [ite_neg' h2, ite_neg' (fun h => ((hsplit _).1 h).elim h2 h1)]
    have hA₃ : T₃.tp tAcc hA = (if ∃ u : Fin (nV Λ Γ L), u.val < c.val + 1 ∧
        AccV (x := x) M hL a u then .yes else .no) := by
      rw [(ag13 tAcc (by decide)).1, ← hAh, hA₁, hAh, hAv]
      by_cases h1 : AccV (x := x) M hL a c
      · rw [ite_pos' (show Relation.ReflTransGen (M.GEdge x hL) a c ∧
          (decV (n := x.length) hL c).1 = M.accept from h1), ite_pos' ((hsplit _).2 (Or.inr h1))]
      · rw [ite_neg' (show ¬ (Relation.ReflTransGen (M.GEdge x hL) a c ∧
          (decV (n := x.length) hL c).1 = M.accept) from h1)]
        by_cases h2 : ∃ u : Fin (nV Λ Γ L), u.val < c.val ∧ AccV (x := x) M hL a u
        · rw [ite_pos' h2, ite_pos' ((hsplit _).2 (Or.inl h2))]
        · rw [ite_neg' h2, ite_neg' (fun h => ((hsplit _).1 h).elim h2 h1)]
    have hread : T₃.read tC₅ =
        if dinc (digs c) = digs (Gen.zero : Fin (nV Λ Γ L)) then .yes else .no := by
      rw [Tapes.read, hChd₃]; exact hC₃
    have ag03 : T.Agree Lo₃ T₃ :=
      (ag1.mono (fun i h => by revert i h; decide)).trans (ag13.mono (fun i h => by
        rcases h with h | h <;> simp [h, Lo₃]))
    have hbody : Spec (vBody M) x B T T₃ := (s1.seq s2).seq s3
    have hcT : Cond.eval x T (.tape tC₅ (fun g => decide (g = (Sym.no : Sym Λ Γ)))) = true := by
      simp [Cond.eval, hC]
    by_cases hlt : c.val + 1 < nV Λ Γ L
    · -- continue with `c + 1`
      have hne : dinc (digs c) ≠ digs (Gen.zero : Fin (nV Λ Γ L)) := fun h => (wrap_iff c).1 h hlt
      rw [next_digs c hlt] at hWl₃
      obtain ⟨T', r', hl, hR', hG', hE', hA', hEhd', hAhd', ag', hW'⟩ :=
        vloop_aux M hL hfit hWK hN a hB hE hA m ⟨c.val + 1, hlt⟩ (by simp only; omega) T₃ r₁ hR₃
          ⟨hI₃, hWl₃, hKK₃⟩ (by rw [hread, ite_neg' hne]) hE₃hd hA₃hd hE₃ hA₃ hW₃
      exact ⟨T', r', .iter hcT hT hbody hl, hR', hG', hE', hA', hEhd', hAhd', ag03.trans ag', hW'⟩
    · -- wrapped around: done
      have heq : dinc (digs c) = digs (Gen.zero : Fin (nV Λ Γ L)) := (wrap_iff c).2 hlt
      have hall : ∀ P : Fin (nV Λ Γ L) → Prop,
          (∃ u : Fin (nV Λ Γ L), u.val < c.val + 1 ∧ P u) ↔ ∃ u, P u := fun P =>
        ⟨fun ⟨u, _, hp⟩ => ⟨u, hp⟩, fun ⟨u, hp⟩ => ⟨u, by have := u.isLt; omega, hp⟩⟩
      rw [heq] at hWl₃
      refine ⟨T₃, r₁, .iter hcT hT hbody (.stop (by simp [Cond.eval, hread, heq]) hW₃), hR₃,
        ⟨Gen.zero, hI₃, hWl₃, hKK₃⟩, ?_, ?_, hE₃hd, hA₃hd, ag03, hW₃⟩
      · rw [hE₃]; exact if_congr (hall _) rfl rfl
      · rw [hA₃]; exact if_congr (hall _) rfl rfl

open Classical in
/-- **The vertex loop.** -/
theorem Spec.vLoop [NeZero (nV Λ Γ L)] [NeZero (nR Λ Γ)] (M : NTM Λ Γ) (hL : 0 < L)
    (hfit : x.length + 1 < 2 ^ L) {K WK : ℕ} (hWK : K < 2 ^ WK) (hN : nV Λ Γ L ≤ 2 ^ K)
    (a : Fin (nV Λ Γ L)) (hB : (K + 1) * (L + 1) + WK + 8 ≤ B) {v₀ : Fin (nV Λ Γ L)} {r₀ : Bool}
    {T : Tapes NT (Sym Λ Γ)} (hR : Rep L x K WK T (.done r₀)) (hG : Regs K WK a v₀ T)
    (hT : T.Within B) :
    ∃ T' r, Spec (vLoop M) x B T T' ∧ Rep L x K WK T' (.done r) ∧ (∃ v', Regs K WK a v' T') ∧
      T'.tp tEsc (T.hd tEsc) = (if ∃ u, EscV (x := x) M hL a u then .yes else .no) ∧
      T'.tp tAcc (T.hd tAcc) = (if ∃ u, AccV (x := x) M hL a u then .yes else .no) ∧
      T'.hd tEsc = T.hd tEsc ∧ T'.hd tAcc = T.hd tAcc ∧
      T.Agree Lo₃ T' ∧ T'.Within B := by
  have hmb : (Sym.mk : Sym Λ Γ) ≠ .blank := fun h => by cases h
  have hLB : L + 2 ≤ B := by
    have := Nat.le_mul_of_pos_left (L + 1) (show 0 < K + 1 by omega); omega
  obtain ⟨hI, hWl, hKK⟩ := hG
  have hZ := hR.2.2.2.2.2.1
  -- `tW` := zero
  obtain ⟨T₁, s1, hWl₁, _, ag1, ih1, hW₁⟩ := Spec.zipPass (x := x) (a := tW) (b := tZ)
    (p := isRec) (F := fun _ b => b) (by decide) hmb hWl (hZ.toW hmb)
    (by rw [cellsOf_length, cellsOf_length, digs_length, digs_length]) (cellsOf_rec _) rfl
    (cellsOf_not_mk _)
    (by rw [zipWith_snd _ _ (by rw [cellsOf_length, cellsOf_length, digs_length, digs_length])]
        exact cellsOf_not_mk _)
    hT (by rw [cellsOf_length, digs_length]; exact hLB)
  rw [zipWith_snd _ _ (by rw [cellsOf_length, cellsOf_length, digs_length, digs_length])] at hWl₁
  -- clear the flags
  have s2 := Spec.write (x := x) (t := tEsc) (g := (Sym.no : Sym Λ Γ)) hW₁
  have hW₂ := Tapes.within_write (t := tEsc) (g := (Sym.no : Sym Λ Γ)) hW₁
  have s3 := Spec.write (x := x) (t := tAcc) (g := (Sym.no : Sym Λ Γ)) hW₂
  have hW₃ := Tapes.within_write (t := tAcc) (g := (Sym.no : Sym Λ Γ)) hW₂
  have s4 := Spec.write (x := x) (t := tC₅) (g := (Sym.no : Sym Λ Γ)) hW₃
  have hW₄ := Tapes.within_write (t := tC₅) (g := (Sym.no : Sym Λ Γ)) hW₃
  set T₄ := ((T₁.write tEsc .no).write tAcc .no).write tC₅ .no
  have ag14 : T₁.Agree (fun i => i = tEsc ∨ i = tAcc ∨ i = tC₅) T₄ := fun i hi => by
    have h1 : i ≠ tEsc := fun e => hi (Or.inl e)
    have h2 : i ≠ tAcc := fun e => hi (Or.inr (Or.inl e))
    have h3 : i ≠ tC₅ := fun e => hi (Or.inr (Or.inr e))
    exact ⟨by simp [T₄, Tapes.write, h1, h2, h3], rfl⟩
  have ag04 : T.Agree (fun i => i = tW ∨ i = tEsc ∨ i = tAcc ∨ i = tC₅) T₄ :=
    (ag1.mono (fun _ h => Or.inl h)).trans (ag14.mono (fun _ h => Or.inr h))
  have hR₄ : Rep L x K WK T₄ (.done r₀) := by
    obtain ⟨hMd, ⟨a₁, hU⟩, ⟨b₁, hV⟩, ⟨w₁, hK⟩, hS, hZ', hEI⟩ := hR
    refine ⟨?_, ⟨a₁, agree_lay ag04 (by decide) hU⟩, ⟨b₁, agree_lay ag04 (by decide) hV⟩,
      ⟨w₁, hK.agree ag04 (by decide)⟩, hS.agree ag04 (by decide) (by decide) (by decide)
        (by decide), agree_lay ag04 (by decide) hZ',
      hEI.agree ag04 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by simp [T₄, ih1])⟩
    rw [Tapes.read, (ag04 tMd (by decide)).1, (ag04 tMd (by decide)).2]; exact hMd
  have hhE : T₄.hd tEsc = T.hd tEsc := by simp [T₄, (ag1 tEsc (by decide)).2]
  have hhA : T₄.hd tAcc = T.hd tAcc := by simp [T₄, (ag1 tAcc (by decide)).2]
  have hG₄ : Regs K WK a Gen.zero T₄ := by
    refine ⟨agree_lay ag04 (by decide) hI, agree_lay ag14 (by decide) hWl₁, ?_⟩
    obtain ⟨l, h1, h2, h3⟩ := hKK
    exact ⟨l, h1.congr (ag04 tKK (by decide)).1 (ag04 tKK (by decide)).2, h2, h3⟩
  obtain ⟨T', r, hl, hR', hG', hE', hA', hEhd', hAhd', ag', hW'⟩ :=
    vloop_aux M hL hfit hWK hN a hB (T.hd tEsc) (T.hd tAcc) _ Gen.zero rfl T₄ r₀ hR₄ hG₄
      (by simp [T₄, Tapes.read, Tapes.write_tp_self]) hhE hhA
      (by rw [ite_neg' (by rintro ⟨u, hu, _⟩; simp [Gen.zero] at hu)]
          simp [T₄, Tapes.write, show tEsc ≠ tAcc by decide,
            show tEsc ≠ tC₅ by decide, (ag1 tEsc (by decide)).2])
      (by rw [ite_neg' (by rintro ⟨u, hu, _⟩; simp [Gen.zero] at hu)]
          simp [T₄, Tapes.write, show tAcc ≠ tC₅ by decide, show tAcc ≠ tEsc by decide,
            (ag1 tAcc (by decide)).2])
      hW₄
  refine ⟨T', r, (((s1.seq s2).seq s3).seq s4).seq (Spec.whileDo hl), hR', hG', hE', hA',
    hEhd', hAhd', ?_, hW'⟩
  exact (ag04.mono (fun i h => by rcases h with h | h | h | h <;> simp [h, Lo₃])).trans ag'

end Savitch.Edge
