import Savitch.Edge.Moves

/-!
# The key cell: `(state, input symbol, work symbol)` of `dec u`

Phase 4b-4 of the Savitch formalization (see `PLAN.md`).

`buildKey g₀ U K A₁` writes `key q i g` under head `K`, where `q` is the decoded
state of the block on `U` (record 0), `i` is the input symbol under the input
head, and `g` is the work symbol at the cell marked on `A₁` (`Spec.buildKey`).
A single case split on this cell then selects `δ q i g`.
-/

set_option linter.unusedSectionVars false

namespace Savitch.Edge

open TM Machine Machine.NTM

variable {Λ Γ : Type} [Fintype Λ] [Fintype Γ] [DecidableEq Λ] [DecidableEq Γ]
variable {k : ℕ} {x : List Bool} {B : ℕ}

def kq (g₀ : Γ) : Sym Λ Γ → Sym Λ Γ
  | .rc r => .key r.2.2.2 none g₀
  | g => g

def setG : Sym Λ Γ → Sym Λ Γ → Sym Λ Γ
  | .key q i _, .rc r => .key q i r.1
  | g, _ => g

def setI (i : Option Bool) : Sym Λ Γ → Sym Λ Γ
  | .key q _ g => .key q i g
  | g => g

/-- Record the input symbol under the input head in the key cell. -/
noncomputable def setInput (K : Fin k) : Code k (Sym Λ Γ) :=
  ifElse (.input (fun i => decide (i = none))) (mapSym K K (setI none))
    (ifElse (.input (fun i => decide (i = some false))) (mapSym K K (setI (some false)))
      (mapSym K K (setI (some true))))

/-- Build the key cell under head `K`. -/
noncomputable def buildKey (g₀ : Γ) (U K A₁ : Fin k) : Code k (Sym Λ Γ) :=
  mapSym U K (kq g₀) ++ zipWhile A₁ U isZs (fun a _ => a) ++ mapSym2 K U setG ++
    TM.home U .mk ++ TM.home A₁ .mk ++ setInput K

theorem Spec.setInput {K : Fin k} {T : Tapes k (Sym Λ Γ)} (hT : T.Within B) :
    Spec (Edge.setInput K) x B T (T.write K (setI (inputSym x T.ih) (T.read K))) := by
  cases h : inputSym x T.ih with
  | none =>
    exact Spec.ifElse_true (by simp [Cond.eval, h]) hT (Spec.mapSym K K _ hT)
  | some b =>
    cases b
    · exact Spec.ifElse_false (by simp [Cond.eval, h]) hT
        (Spec.ifElse_true (by simp [Cond.eval, h]) hT (Spec.mapSym K K _ hT))
    · exact Spec.ifElse_false (by simp [Cond.eval, h]) hT
        (Spec.ifElse_false (by simp [Cond.eval, h]) hT (Spec.mapSym K K _ hT))

theorem Spec.buildKey (g₀ : Γ) {U K A₁ : Fin k} (hUK : U ≠ K) (hU1 : U ≠ A₁) (hK1 : K ≠ A₁)
    {L : ℕ} (hL : 0 < L) (f : Fin L → Rec Λ Γ) {T : Tapes k (Sym Λ Γ)}
    (hU : Lay U .mk .blank T ((List.ofFn f).map .rc))
    (hA₁ : Lay A₁ .mk .blank T
      ((List.ofFn fun j : Fin L => decide (j = firstFlag hL f)).map bit))
    (hT : T.Within B) (hB : L + 2 ≤ B) :
    ∃ T', Spec (Edge.buildKey g₀ U K A₁) x B T T' ∧
      T'.tp K (T.hd K) = .key (f ⟨0, hL⟩).2.2.2 (inputSym x T.ih) (f (firstFlag hL f)).1 ∧
      Lay U .mk .blank T' ((List.ofFn f).map .rc) ∧
      Lay A₁ .mk .blank T' ((List.ofFn fun j : Fin L => decide (j = firstFlag hL f)).map bit) ∧
      T.Agree (fun i => i = K) T' ∧ T'.hd K = T.hd K ∧ T'.ih = T.ih ∧ T'.Within B := by
  have hmb : (Sym.mk : Sym Λ Γ) ≠ .blank := fun h => by cases h
  set w := firstFlag hL f
  have hlul : ((List.ofFn f).map (Sym.rc (Λ := Λ) (Γ := Γ))).length = L := by simp
  have hUcell : ∀ j : Fin L, T.tp U (1 + j) = .rc (f j) := by
    have h := hU.2.1
    rw [hlul, seg_ofFn, List.map_ofFn] at h
    intro j; exact congrFun (List.ofFn_injective h) j
  have hUend : T.tp U (L + 1) = .blank := by have := hU.2.2.1; rwa [hlul] at this
  have hlal : ((List.ofFn fun j : Fin L => decide (j = w)).map (bit (Λ := Λ) (Γ := Γ))).length
      = L := by simp
  have hAcell : ∀ j : Fin L, T.tp A₁ (1 + j) = bit (decide (j = w)) := by
    have h := hA₁.2.1
    rw [hlal, seg_ofFn, List.map_ofFn] at h
    intro j; exact congrFun (List.ofFn_injective h) j
  have hAend : T.tp A₁ (L + 1) = .blank := by have := hA₁.2.2.1; rwa [hlal] at this
  have hw := w.isLt
  -- 1. the state, from record 0
  have s1 := Spec.mapSym (x := x) U K (kq g₀) hT
  set T₁ := T.write K (kq g₀ (T.read U))
  have hT₁U : T₁.tp U = T.tp U := by simp [T₁, Tapes.write, hUK]
  have hT₁A : T₁.tp A₁ = T.tp A₁ := by simp [T₁, Tapes.write, hK1.symm]
  have hW₁ : T₁.Within B := Tapes.within_write hT
  have hkey₁ : T₁.tp K (T.hd K) = .key (f ⟨0, hL⟩).2.2.2 none g₀ := by
    simp only [T₁, Tapes.write_tp_self, ite_true, Tapes.read, hU.2.2.2]
    rw [show (1 : ℕ) = 1 + (⟨0, hL⟩ : Fin L).val from rfl, hUcell]; rfl
  -- 2. move `U` to the marked cell, in lockstep with `A₁`
  have s2 := Spec.zipWhile (x := x) (Ne.symm hU1) isZs (fun g _ => g) w.val T₁
    (fun j hj => by
      rw [show T₁.hd A₁ = 1 by simp [T₁, hA₁.2.2.2], hT₁A, hAcell ⟨j, by omega⟩]
      have : (⟨j, by omega⟩ : Fin L) ≠ w := fun e => by rw [← e] at hj; exact lt_irrefl _ hj
      simp [this, isZs, bit, bsym])
    (by rw [show T₁.hd A₁ = 1 by simp [T₁, hA₁.2.2.2], hT₁A, hAcell w]; simp [isZs, bit, bsym])
    hW₁ (by simp [T₁, hA₁.2.2.2]; omega) (by simp [T₁, hU.2.2.2]; omega)
  set T₂ := T₁.zipRes A₁ U (fun g _ => g) w.val
  have hT₂A : T₂.tp A₁ = T.tp A₁ := by rw [zipRes_fst]; exact hT₁A
  have hT₂U : T₂.tp U = T.tp U := by rw [Tapes.zipRes_tp_ne hU1]; exact hT₁U
  have hT₂hU : T₂.hd U = 1 + w.val := by
    rw [Tapes.zipRes_hd_b]; simp [T₁, hU.2.2.2]
  have hT₂hA : T₂.hd A₁ = 1 + w.val := by
    rw [Tapes.zipRes_hd_a (Ne.symm hU1)]; simp [T₁, hA₁.2.2.2]
  have hT₂hK : T₂.hd K = T.hd K := by
    rw [Tapes.zipRes_hd_ne hK1 hUK.symm]; rfl
  have hT₂K : T₂.tp K = T₁.tp K := Tapes.zipRes_tp_ne hK1 T₁ _
  have hW₂ : T₂.Within B := s2.target_within
  -- 3. the work symbol
  have s3 := Spec.mapSym2 (x := x) K U setG hW₂
  set T₃ := T₂.write K (setG (T₂.read K) (T₂.read U))
  have hkey₃ : T₃.tp K (T.hd K) = .key (f ⟨0, hL⟩).2.2.2 none (f w).1 := by
    simp only [T₃, Tapes.write_tp_self, hT₂hK, ite_true, Tapes.read, hT₂K, hkey₁, hT₂U, hT₂hU]
    rw [hUcell w]; rfl
  have hW₃ : T₃.Within B := Tapes.within_write hW₂
  have hT₃U : T₃.tp U = T.tp U := by simp [T₃, Tapes.write, hUK, hT₂U]
  have hT₃A : T₃.tp A₁ = T.tp A₁ := by simp [T₃, Tapes.write, hK1.symm, hT₂A]
  -- 4. heads home
  have hh1 := Spec.home (x := x) U .mk (T := T₃) (by rw [hT₃U]; exact hU.1)
    (by rw [hT₃U]; exact home_ok hmb not_mk_rec hU.2.1 hU.2.2.1
          (by simp [T₃, hT₂hU]; omega))
    hW₃ (by omega)
  set T₄ := T₃.setHead U 1
  have hW₄ : T₄.Within B := Tapes.within_setHead hW₃ (by omega)
  have hh2 := Spec.home (x := x) A₁ .mk (T := T₄)
    (by simp only [T₄, Tapes.setHead_tp]; rw [hT₃A]; exact hA₁.1)
    (by simp only [T₄, Tapes.setHead_tp]; rw [hT₃A]
        exact home_ok hmb (fun g hg => by
          obtain ⟨b, _, rfl⟩ := List.mem_map.1 hg; exact bit_ne_mk b) hA₁.2.1 hA₁.2.2.1
          (by simp [Tapes.setHead_hd_ne _ _ (Ne.symm hU1), T₃, hT₂hA]; omega))
    hW₄ (by omega)
  set T₅ := T₄.setHead A₁ 1
  have hW₅ : T₅.Within B := Tapes.within_setHead hW₄ (by omega)
  -- 5. the input symbol
  have s5 := Spec.setInput (x := x) (K := K) hW₅
  have hih₅ : T₅.ih = T.ih := by simp [T₅, T₄, T₃, T₂, Tapes.zipRes, T₁]
  have hK₅ : T₅.hd K = T.hd K := by
    simp [T₅, T₄, Tapes.setHead_hd_ne _ _ hK1, Tapes.setHead_hd_ne _ _ hUK.symm, T₃, hT₂hK]
  have hK₅tp : T₅.tp K (T.hd K) = .key (f ⟨0, hL⟩).2.2.2 none (f w).1 := by
    simp only [T₅, T₄, Tapes.setHead_tp]; exact hkey₃
  refine ⟨T₅.write K (setI (inputSym x T₅.ih) (T₅.read K)),
    ((((s1.seq s2).seq s3).seq hh1).seq hh2).seq s5, ?_, ?_, ?_, ?_, by simp [hK₅], ?_,
    Tapes.within_write hW₅⟩
  · simp only [Tapes.write_tp_self, hK₅, ite_true, Tapes.read, hK₅tp, hih₅]; rfl
  · refine hU.congr ?_ ?_
    · simp [Tapes.write, hUK, T₅, T₄, hT₃U]
    · simp [T₅, Tapes.setHead_hd_ne _ _ hU1, T₄, hU.2.2.2]
  · refine hA₁.congr ?_ ?_
    · simp [Tapes.write, hK1.symm, T₅, T₄, hT₃A]
    · simp [T₅, hA₁.2.2.2]
  · intro i hi
    refine ⟨?_, ?_⟩
    · simp only [Tapes.write, Function.update_apply, hi, ite_false, T₅, T₄,
        Tapes.setHead_tp]
      by_cases hiU : i = U
      · subst hiU; exact hT₃U
      · by_cases hiA : i = A₁
        · subst hiA; exact hT₃A
        · simp [T₃, Tapes.write, hi, T₂, Tapes.zipRes_tp_ne hiA, T₁]
    · simp only [Tapes.write_hd]
      by_cases hiA : i = A₁
      · subst hiA; simp [T₅, hA₁.2.2.2]
      · rw [show T₅.hd i = T₄.hd i from Tapes.setHead_hd_ne _ _ hiA _]
        by_cases hiU : i = U
        · subst hiU; simp [T₄, hU.2.2.2]
        · rw [show T₄.hd i = T₃.hd i from Tapes.setHead_hd_ne _ _ hiU _]
          simp [T₃, T₂, Tapes.zipRes_hd_ne hiA hiU, T₁]
  · simp [hih₅]

end Savitch.Edge
