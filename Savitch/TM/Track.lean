import Savitch.TM.Counter

/-!
# Copying with a symbol map (extracting tracks)

A record block carries several tracks: symbol, head flag, input-head bit, state.
To compute with one track, the Savitch TM copies the block onto a scratch tape
through a map `h`, for example `h r = bsym z o r.ihBit`.

* `mapSym a b h`: write `h (symbol under a)` under head `b` (`Spec.mapSym`).
* `copyMapWhile a b p h`: lockstep copy through `h` while `p` holds on tape `a`
  (`Spec.copyMapWhile`, `Tapes.seg_copyMapRes`).
-/

namespace Savitch.TM

variable {k : ℕ} {Γ : Type} {x : List Bool} {B : ℕ}

section Map

variable [DecidableEq Γ] [Fintype Γ]

/-- Write `h g` under head `b`, where `g` is the symbol under head `a`. -/
noncomputable def mapSym (a b : Fin k) (h : Γ → Γ) : Code k Γ :=
  TM.cases a (fun g => [Instr.write b (h g)]) Finset.univ.toList

theorem Spec.mapSym (a b : Fin k) (h : Γ → Γ) {T : Tapes k Γ} (hT : T.Within B) :
    Spec (TM.mapSym a b h) x B T (T.write b (h (T.read a))) :=
  Spec.cases a _ _ (by simp) hT (Spec.write hT)

end Map

/-- Tapes after copying `m` cells from `a` to `b` through `h`, both heads advanced. -/
def Tapes.copyMapRes (T : Tapes k Γ) (a b : Fin k) (h : Γ → Γ) (m : ℕ) : Tapes k Γ where
  ih := T.ih
  hd := Function.update (Function.update T.hd a (T.hd a + m)) b (T.hd b + m)
  tp := Function.update T.tp b (fun j =>
    if T.hd b ≤ j ∧ j < T.hd b + m then h (T.tp a (T.hd a + (j - T.hd b))) else T.tp b j)

def Tapes.copyMapStep (T : Tapes k Γ) (a b : Fin k) (h : Γ → Γ) : Tapes k Γ :=
  ((T.write b (h (T.read a))).setHead a (T.hd a + 1)).setHead b (T.hd b + 1)

variable {a b : Fin k} {h : Γ → Γ}

theorem Tapes.copyMapRes_zero (T : Tapes k Γ) : T.copyMapRes a b h 0 = T := by
  ext i
  · rfl
  · by_cases hb : i = b
    · subst hb; simp [copyMapRes]
    · by_cases ha : i = a
      · subst ha; simp [copyMapRes]
      · simp [copyMapRes]
  · rename_i j
    by_cases hb : i = b
    · subst hb
      simp only [copyMapRes, Function.update_self]
      split_ifs with h'
      · omega
      · rfl
    · simp [copyMapRes, hb]

theorem Tapes.copyMapStep_hd_a (hab : a ≠ b) (T : Tapes k Γ) :
    (T.copyMapStep a b h).hd a = T.hd a + 1 := by
  simp [copyMapStep, setHead, hab]

theorem Tapes.copyMapStep_hd_b (T : Tapes k Γ) : (T.copyMapStep a b h).hd b = T.hd b + 1 := by
  simp [copyMapStep, setHead]

theorem Tapes.copyMapStep_tp_a (hab : a ≠ b) (T : Tapes k Γ) :
    (T.copyMapStep a b h).tp a = T.tp a := by
  simp [copyMapStep, write, hab]

theorem Tapes.copyMapRes_succ (hab : a ≠ b) (T : Tapes k Γ) (m : ℕ) :
    (T.copyMapStep a b h).copyMapRes a b h m = T.copyMapRes a b h (m + 1) := by
  ext i
  · rfl
  · simp only [copyMapRes, copyMapStep, setHead, write, Function.update_apply]
    split_ifs <;> omega
  · rename_i j
    by_cases hb : i = b
    · subst hb
      simp only [copyMapRes, copyMapStep, setHead, write, read, Function.update_apply, ite_true,
        Ne.symm hab, ite_false, hab]
      split_ifs <;> first | rfl | omega | (congr 2; omega)
    · simp [copyMapRes, copyMapStep, write, hb]

theorem Tapes.within_copyMapStep {T : Tapes k Γ} (hT : T.Within B)
    (ha : T.hd a + 1 < B) (hb : T.hd b + 1 < B) : (T.copyMapStep a b h).Within B :=
  Tapes.within_setHead (Tapes.within_setHead (Tapes.within_write hT) ha) hb

/-- The copied block, as a segment. -/
theorem Tapes.seg_copyMapRes (T : Tapes k Γ) (m : ℕ) :
    seg ((T.copyMapRes a b h m).tp b) (T.hd b) m = (seg (T.tp a) (T.hd a) m).map h := by
  have key : ∀ (n i : ℕ), i + n ≤ m →
      seg ((T.copyMapRes a b h m).tp b) (T.hd b + i) n = (seg (T.tp a) (T.hd a + i) n).map h := by
    intro n
    induction n with
    | zero => intro _ _; rfl
    | succ n ih =>
      intro i hi
      simp only [seg, List.map]
      rw [show T.hd b + i + 1 = T.hd b + (i + 1) by omega,
        show T.hd a + i + 1 = T.hd a + (i + 1) by omega, ih (i + 1) (by omega)]
      congr 1
      simp only [copyMapRes, Function.update_self]
      rw [ite_pos' (by omega)]
      congr 2; omega
  simpa using key m 0 (by omega)

theorem Tapes.copyMapRes_tp_ne {i : Fin k} (hi : i ≠ b) (T : Tapes k Γ) (m : ℕ) :
    (T.copyMapRes a b h m).tp i = T.tp i := by
  simp [copyMapRes, hi]

theorem Tapes.copyMapRes_hd_a (hab : a ≠ b) (T : Tapes k Γ) (m : ℕ) :
    (T.copyMapRes a b h m).hd a = T.hd a + m := by
  simp [copyMapRes, hab]

theorem Tapes.copyMapRes_hd_b (T : Tapes k Γ) (m : ℕ) :
    (T.copyMapRes a b h m).hd b = T.hd b + m := by
  simp [copyMapRes]

theorem Tapes.copyMapRes_hd_ne {i : Fin k} (hia : i ≠ a) (hib : i ≠ b) (T : Tapes k Γ) (m : ℕ) :
    (T.copyMapRes a b h m).hd i = T.hd i := by
  simp [copyMapRes, hia, hib]

section Copy

variable [DecidableEq Γ] [Fintype Γ]

noncomputable def copyMapBody (a b : Fin k) (h : Γ → Γ) : Code k Γ :=
  TM.mapSym a b h ++ [Instr.move a .right] ++ [Instr.move b .right]

theorem Spec.copyMapBody (hab : a ≠ b) {T : Tapes k Γ} (hT : T.Within B)
    (ha : T.hd a + 1 < B) (hb : T.hd b + 1 < B) :
    Spec (TM.copyMapBody a b h) x B T (T.copyMapStep a b h) := by
  have h1 := Spec.mapSym (x := x) a b h hT
  have h2 := Spec.moveRight (x := x) (t := a)
    (Tapes.within_write (g := h (T.read a)) (t := b) hT) (by simpa using ha)
  have h3 := Spec.moveRight (x := x) (t := b)
    (Tapes.within_setHead (n := T.hd a + 1) (t := a)
      (Tapes.within_write (g := h (T.read a)) (t := b) hT) ha)
    (by rw [Tapes.setHead_hd_ne _ _ (Ne.symm hab)]; simpa using hb)
  rw [Tapes.setHead_hd_ne _ _ (Ne.symm hab), Tapes.write_hd] at h3
  exact (h1.seq h2).seq h3

/-- Copy from `a` to `b` through `h`, cell by cell, while `p` holds on tape `a`. -/
noncomputable def copyMapWhile (a b : Fin k) (p : Γ → Bool) (h : Γ → Γ) : Code k Γ :=
  whileDo (.tape a p) (TM.copyMapBody a b h)

theorem Spec.copyMapWhile (hab : a ≠ b) (p : Γ → Bool) (h : Γ → Γ) :
    ∀ (m : ℕ) (T : Tapes k Γ), (∀ j < m, p (T.tp a (T.hd a + j)) = true) →
      p (T.tp a (T.hd a + m)) = false → T.Within B → T.hd a + m < B → T.hd b + m < B →
      Spec (TM.copyMapWhile a b p h) x B T (T.copyMapRes a b h m) := by
  intro m T hp hq hT hBa hBb
  apply Spec.whileDo
  induction m generalizing T with
  | zero =>
    rw [Tapes.copyMapRes_zero]
    exact .stop (by simpa [Cond.eval, Tapes.read] using hq) hT
  | succ m ih =>
    refine .iter (by simpa [Cond.eval, Tapes.read] using hp 0 (by omega)) hT
      (Spec.copyMapBody hab hT (by omega) (by omega)) ?_
    rw [← Tapes.copyMapRes_succ hab]
    apply ih
    · intro j hj
      rw [Tapes.copyMapStep_tp_a hab, Tapes.copyMapStep_hd_a hab]
      have := hp (j + 1) (by omega)
      rwa [show T.hd a + (j + 1) = T.hd a + 1 + j by omega] at this
    · rw [Tapes.copyMapStep_tp_a hab, Tapes.copyMapStep_hd_a hab]
      rwa [show T.hd a + (m + 1) = T.hd a + 1 + m by omega] at hq
    · exact Tapes.within_copyMapStep hT (by omega) (by omega)
    · rw [Tapes.copyMapStep_hd_a hab]; omega
    · rw [Tapes.copyMapStep_hd_b]; omega

end Copy

end Savitch.TM
