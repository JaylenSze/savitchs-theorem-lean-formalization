import Savitch.Edge.Build

/-!
# Marking the work head of `dec u`

Phase 4b-4 of the Savitch formalization (see `PLAN.md`).

`markFirst U A` writes, on tape `A`, the bit block with a single `o` at the
decoded work head of the block on `U` (its first flagged cell, or cell 0 if none),
exactly as `decR` decodes it (`Spec.markFirst`).

Pure facts:
* `seg_ofFn`: a tape segment as `List.ofFn`.
* `leadUnf l`: the number of leading unflagged records, and `firstFlag_eq`, which
  identifies `decR`'s `firstFlag` with it.
-/

set_option linter.unusedSectionVars false

namespace Savitch.Edge

open TM Machine Machine.NTM

variable {Λ Γ : Type} [Fintype Λ] [Fintype Γ] [DecidableEq Λ] [DecidableEq Γ]

theorem seg_ofFn {α : Type} (g : ℕ → α) : ∀ (s n : ℕ), seg g s n = List.ofFn (fun j : Fin n => g (s + j))
  | _, 0 => rfl
  | s, n + 1 => by
    show g s :: seg g (s + 1) n = List.ofFn (fun j : Fin (n + 1) => g (s + j))
    rw [List.ofFn_succ, seg_ofFn g (s + 1) n]
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ, List.cons.injEq, true_and]
    exact congrArg List.ofFn (funext fun j => by congr 1; omega)

/-! ### Leading unflagged records -/

def leadUnf : List (Rec Λ Γ) → ℕ
  | [] => 0
  | r :: rs => if r.2.1 then 0 else leadUnf rs + 1

theorem leadUnf_le : ∀ l : List (Rec Λ Γ), leadUnf l ≤ l.length
  | [] => le_rfl
  | r :: rs => by
    unfold leadUnf; split_ifs
    · exact Nat.zero_le _
    · simp only [List.length_cons]; have := leadUnf_le rs; omega

theorem leadUnf_unflagged : ∀ (l : List (Rec Λ Γ)) (j : ℕ) (hj : j < leadUnf l),
    (l[j]'(lt_of_lt_of_le hj (leadUnf_le l))).2.1 = false
  | [], _, hj => absurd hj (Nat.not_lt_zero _)
  | r :: rs, j, hj => by
    unfold leadUnf at hj
    split_ifs at hj with hr
    · exact absurd hj (Nat.not_lt_zero _)
    · rcases j with _ | j
      · simpa using hr
      · simp only [List.getElem_cons_succ]
        exact leadUnf_unflagged rs j (by omega)

theorem leadUnf_flagged : ∀ (l : List (Rec Λ Γ)) (h : leadUnf l < l.length),
    (l[leadUnf l]'h).2.1 = true
  | [], h => absurd h (Nat.not_lt_zero _)
  | r :: rs, h => by
    by_cases hr : r.2.1 = true
    · simp [leadUnf, hr]
    · have hr' : r.2.1 = false := by simpa using hr
      have : leadUnf (r :: rs) = leadUnf rs + 1 := by simp [leadUnf, hr']
      simp only [this, List.getElem_cons_succ]
      exact leadUnf_flagged rs (by simp [this] at h; omega)

/-- `decR`'s work head is the number of leading unflagged records (or 0 if all are). -/
theorem firstFlag_eq {L : ℕ} (hL : 0 < L) (f : Fin L → Rec Λ Γ) :
    (firstFlag hL f).val = if leadUnf (List.ofFn f) < L then leadUnf (List.ofFn f) else 0 := by
  have hlen : (List.ofFn f).length = L := List.length_ofFn
  have hunf : ∀ j : Fin L, j.val < leadUnf (List.ofFn f) → (f j).2.1 = false := fun j hj => by
    have := leadUnf_unflagged (List.ofFn f) j hj
    simpa using this
  unfold firstFlag
  split_ifs with hne hlt hlt
  · -- some flagged cell, found at `leadUnf`
    have hfl : (f ⟨leadUnf (List.ofFn f), hlt⟩).2.1 = true := by
      have := leadUnf_flagged (List.ofFn f) (by rw [hlen]; exact hlt)
      simpa using this
    have hmem : (⟨leadUnf (List.ofFn f), hlt⟩ : Fin L) ∈
        Finset.univ.filter (fun j => (f j).2.1 = true) := by simp [hfl]
    have heq : (Finset.univ.filter (fun j => (f j).2.1 = true)).min' hne =
        ⟨leadUnf (List.ofFn f), hlt⟩ := by
      apply le_antisymm (Finset.min'_le _ _ hmem)
      apply Finset.le_min' _ _ _
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      rw [Fin.le_def]
      by_contra hlt'
      have := hunf y (by simp at hlt'; exact hlt')
      rw [this] at hy; exact Bool.false_ne_true hy
    rw [heq]
  · -- every cell unflagged, contradiction with `hne`
    exfalso
    obtain ⟨y, hy⟩ := hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have := hunf y (by have := leadUnf_le (List.ofFn f); rw [hlen] at this; omega)
    rw [this] at hy; exact Bool.false_ne_true hy
  · exfalso
    apply hne
    have hfl : (f ⟨leadUnf (List.ofFn f), hlt⟩).2.1 = true := by
      have := leadUnf_flagged (List.ofFn f) (by rw [hlen]; exact hlt)
      simpa using this
    exact ⟨⟨leadUnf (List.ofFn f), hlt⟩, by simp [hfl]⟩
  · rfl

/-! ### The marking routine -/

variable {k : ℕ} {x : List Bool} {B : ℕ}

/-- Is this an unflagged record? -/
def isUnflag : Sym Λ Γ → Bool
  | .rc r => !r.2.1
  | _ => false

/-- Write a single `o` on tape `A` at the decoded work head of the block on `U`. -/
noncomputable def markFirst (U A : Fin k) : Code k (Sym Λ Γ) :=
  copyPass U A .mk isRec (fun _ => .z) ++
  zipWhile U A isUnflag (fun a _ => a) ++
  ifElse (.tape U isRec) [Instr.write A .o] (TM.home A .mk ++ [Instr.write A .o]) ++
  TM.home U .mk ++ TM.home A .mk

theorem zipRes_fst {a b : Fin k} (T : Tapes k (Sym Λ Γ)) (m : ℕ) :
    (T.zipRes a b (fun g _ => g) m).tp a = T.tp a := by
  funext j
  simp only [Tapes.zipRes, Function.update_self]
  split_ifs <;> rfl

theorem Spec.markFirst {U A : Fin k} (hUA : U ≠ A) {L : ℕ} (hL : 0 < L) (f : Fin L → Rec Λ Γ)
    {la : List (Sym Λ Γ)} {T : Tapes k (Sym Λ Γ)}
    (hU : Lay U .mk .blank T ((List.ofFn f).map .rc)) (hA : Lay A .mk .blank T la)
    (hla : la.length = L) (hT : T.Within B) (hB : L + 2 ≤ B) :
    ∃ T', Spec (Edge.markFirst U A) x B T T' ∧ Lay U .mk .blank T' ((List.ofFn f).map .rc) ∧
      Lay A .mk .blank T'
        ((List.ofFn fun j : Fin L => decide (j = firstFlag hL f)).map bit) ∧
      T.Agree (fun i => i = A) T' ∧ T'.ih = T.ih ∧ T'.Within B := by
  have hmb : (Sym.mk : Sym Λ Γ) ≠ .blank := fun h => by cases h
  set lu := (List.ofFn f).map (Sym.rc (Λ := Λ) (Γ := Γ)) with hlu
  have hlul : lu.length = L := by simp [lu]
  -- 1. clear `A`
  obtain ⟨T₁, s1, hU₁, hA₁, ag1, ih1, hW₁⟩ := Spec.copyPass (x := x) (p := isRec)
    (h := fun _ => (Sym.z : Sym Λ Γ)) hUA hmb hU hA (by rw [hla, hlul]) isRec_rec rfl
    not_mk_rec (fun _ _ h => by cases h) hT (by rw [hlul]; exact hB)
  -- cell values
  have hUcell : ∀ j : Fin L, T₁.tp U (1 + j) = .rc (f j) := by
    have h := hU₁.2.1
    rw [hlul, seg_ofFn, hlu, List.map_ofFn] at h
    intro j; exact congrFun (List.ofFn_injective h) j
  have hUend : T₁.tp U (L + 1) = .blank := by have := hU₁.2.2.1; rwa [hlul] at this
  have hAcell : ∀ j : Fin L, T₁.tp A (1 + j) = .z := by
    have h := hA₁.2.1
    rw [List.length_map, hlul, seg_ofFn, hlu, List.map_map, List.map_ofFn] at h
    intro j; exact congrFun (List.ofFn_injective h) j
  have hAend : T₁.tp A (L + 1) = .blank := by
    have := hA₁.2.2.1; rwa [List.length_map, hlul] at this
  -- 2. advance both heads past the leading unflagged records
  set m := leadUnf (List.ofFn f) with hm
  have hmL : m ≤ L := by have := leadUnf_le (List.ofFn f); simpa using this
  have hcond : ∀ j < m, isUnflag (T₁.tp U (T₁.hd U + j)) = true := by
    intro j hj
    rw [hU₁.2.2.2, hUcell ⟨j, by omega⟩]
    have := leadUnf_unflagged (List.ofFn f) j hj
    simp only [List.getElem_ofFn] at this
    simp [isUnflag, this]
  have hstop : isUnflag (T₁.tp U (T₁.hd U + m)) = false := by
    rw [hU₁.2.2.2]
    by_cases hlt : m < L
    · rw [hUcell ⟨m, hlt⟩]
      have := leadUnf_flagged (List.ofFn f) (by simp; exact hlt)
      simp only [List.getElem_ofFn, ← hm] at this
      simp [isUnflag, this]
    · rw [show 1 + m = L + 1 by omega, hUend]; rfl
  have s2 := Spec.zipWhile (x := x) hUA isUnflag (fun g _ => g) m T₁ hcond hstop hW₁
    (by rw [hU₁.2.2.2]; omega) (by rw [hA₁.2.2.2]; omega)
  set T₂ := T₁.zipRes U A (fun g _ => g) m
  have hT₂U : T₂.tp U = T₁.tp U := zipRes_fst T₁ m
  have hT₂A : T₂.tp A = T₁.tp A := Tapes.zipRes_tp_ne (Ne.symm hUA) T₁ m
  have hT₂hU : T₂.hd U = 1 + m := by rw [Tapes.zipRes_hd_a hUA, hU₁.2.2.2]
  have hT₂hA : T₂.hd A = 1 + m := by rw [Tapes.zipRes_hd_b, hA₁.2.2.2]
  have hW₂ : T₂.Within B := s2.target_within
  -- the marked position
  set p := 1 + (firstFlag hL f).val with hp
  have hpval : p = 1 + (if m < L then m else 0) := by rw [hp, firstFlag_eq]
  -- 3. write the mark
  have hT₃ : ∃ T₃, Spec (ifElse (.tape U isRec) [Instr.write A .o]
      (TM.home A .mk ++ [Instr.write A .o])) x B T₂ T₃ ∧ T₃.tp A = Function.update (T₁.tp A) p .o ∧
      T₃.tp U = T₁.tp U ∧ T₃.hd U = 1 + m ∧ T₃.hd A ≤ L + 1 ∧ T₂.Agree (fun i => i = A) T₃ ∧
      T₃.ih = T₂.ih ∧ T₃.Within B := by
    by_cases hlt : m < L
    · have hc : Cond.eval x T₂ (.tape U isRec) = true := by
        simp only [Cond.eval, Tapes.read, hT₂U, hT₂hU]
        rw [hUcell ⟨m, hlt⟩]; rfl
      refine ⟨T₂.write A .o, Spec.ifElse_true hc hW₂ (Spec.write hW₂), ?_, ?_, hT₂hU, ?_,
        fun i hi => ⟨by simp [Tapes.write, hi], rfl⟩, rfl, Tapes.within_write hW₂⟩
      · funext j; simp only [Tapes.write_tp_self, Function.update_apply, hT₂A, hT₂hA, hpval,
          hlt, ite_true]
      · simp [Tapes.write, hUA, hT₂U]
      · simp only [Tapes.write_hd, hT₂hA]; omega
    · have hmL' : m = L := by omega
      have hc : Cond.eval x T₂ (.tape U isRec) = false := by
        simp only [Cond.eval, Tapes.read, hT₂U, hT₂hU]
        rw [show 1 + m = L + 1 by omega, hUend]; rfl
      have hh := Spec.home (x := x) A .mk (T := T₂) (by rw [hT₂A]; exact hA₁.1)
        (fun j h1 h2 => by
          rw [hT₂A]
          by_cases hj : j ≤ L
          · rw [show j = 1 + (j - 1) by omega, hAcell ⟨j - 1, by omega⟩]
            exact fun h => by cases h
          · rw [show j = L + 1 by omega, hAend]; exact fun h => by cases h)
        hW₂ (by omega)
      have hW' : (T₂.setHead A 1).Within B := Tapes.within_setHead hW₂ (by omega)
      refine ⟨(T₂.setHead A 1).write A .o,
        Spec.ifElse_false hc hW₂ (hh.seq (Spec.write hW')), ?_, ?_, ?_, ?_, ?_, rfl,
        Tapes.within_write hW'⟩
      · funext j
        simp only [Tapes.write_tp_self, Tapes.setHead_tp, Tapes.setHead_hd_self,
          Function.update_apply, hT₂A, hpval, hlt, ite_false]
      · simp [Tapes.write, hUA, hT₂U]
      · simp [Tapes.write, Tapes.setHead_hd_ne _ _ hUA, hT₂hU]
      · simp
      · intro i hi
        exact ⟨by simp [Tapes.write, hi], by simp [Tapes.write, Tapes.setHead_hd_ne _ _ hi]⟩
  obtain ⟨T₃, s3, hT₃A, hT₃U, hT₃hU, hT₃hA, ag3, ih3, hW₃⟩ := hT₃
  -- 4. send both heads home
  have hU₃end : T₃.tp U (L + 1) = .blank := by rw [hT₃U]; exact hUend
  have hh1 := Spec.home (x := x) U .mk (T := T₃) (by rw [hT₃U]; exact hU₁.1)
    (fun j h1 h2 => by
      rw [hT₃U]
      by_cases hj : j ≤ L
      · rw [show j = 1 + (j - 1) by omega, hUcell ⟨j - 1, by omega⟩]; exact fun h => by cases h
      · rw [show j = L + 1 by omega, hUend]; exact fun h => by cases h)
    hW₃ (by omega)
  set T₄ := T₃.setHead U 1
  have hW₄ : T₄.Within B := Tapes.within_setHead hW₃ (by omega)
  have hp1 : 1 ≤ p ∧ p ≤ L := by
    have := (firstFlag hL f).isLt; constructor <;> omega
  have hh2 := Spec.home (x := x) A .mk (T := T₄)
    (by simp only [T₄, Tapes.setHead_tp, hT₃A]; rw [Function.update_of_ne (by omega)]
        exact hA₁.1)
    (fun j h1 h2 => by
      simp only [T₄, Tapes.setHead_tp, hT₃A, Function.update_apply]
      rw [Tapes.setHead_hd_ne _ _ (Ne.symm hUA)] at h2
      split_ifs
      · exact fun h => by cases h
      · by_cases hj : j ≤ L
        · rw [show j = 1 + (j - 1) by omega, hAcell ⟨j - 1, by omega⟩]
          exact fun h => by cases h
        · rw [show j = L + 1 by omega, hAend]; exact fun h => by cases h)
    hW₄ (by omega)
  refine ⟨T₄.setHead A 1, (((s1.seq s2).seq s3).seq hh1).seq hh2, ?_, ?_, ?_, ?_,
    Tapes.within_setHead hW₄ (by omega)⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Tapes.setHead_tp, T₄, hT₃U]; exact hU₁.1
    · simp only [Tapes.setHead_tp, T₄, hT₃U]; exact hU₁.2.1
    · simp only [Tapes.setHead_tp, T₄, hT₃U]; exact hU₁.2.2.1
    · rw [Tapes.setHead_hd_ne _ _ hUA]; simp [T₄]
  · refine ⟨?_, ?_, ?_, by simp⟩
    · simp only [Tapes.setHead_tp, T₄, hT₃A]; rw [Function.update_of_ne (by omega)]
      exact hA₁.1
    · simp only [Tapes.setHead_tp, T₄, hT₃A, List.length_map, List.length_ofFn]
      rw [seg_ofFn, List.map_ofFn]
      congr 1
      funext j
      simp only [Function.comp_apply, Function.update_apply, hAcell j]
      by_cases hj : j = firstFlag hL f
      · subst hj; simp [hp, bsym]
      · have : 1 + j.val ≠ p := fun e => hj (Fin.ext (by omega))
        simp [this, hj, bsym]
    · simp only [Tapes.setHead_tp, T₄, hT₃A, List.length_map, List.length_ofFn]
      rw [Function.update_of_ne (by omega)]; exact hAend
  · intro i hi
    have g1 := ag1 i hi
    have g3 := ag3 i hi
    refine ⟨?_, ?_⟩
    · simp only [Tapes.setHead_tp, T₄]
      by_cases hiU : i = U
      · subst hiU; rw [hT₃U]; exact g1.1
      · rw [g3.1]
        rw [Tapes.zipRes_tp_ne hiU]; exact g1.1
    · rw [Tapes.setHead_hd_ne _ _ hi]
      by_cases hiU : i = U
      · subst hiU; simp [T₄, hU.2.2.2]
      · simp only [T₄]; rw [Tapes.setHead_hd_ne _ _ hiU, g3.2,
          Tapes.zipRes_hd_ne hiU hi]; exact g1.2
  · show T₃.ih = T.ih
    rw [ih3]; simp [T₂, Tapes.zipRes, ih1]

end Savitch.Edge
