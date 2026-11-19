import Savitch.TM.Block

/-!
# Primitive tape routines with proved specifications

Phase 4b-2 of the Savitch formalization (see `PLAN.md`).

* `Spec.single`, `Spec.nil`: one instruction / no instruction.
* `scanRight t p`, `scanLeft t p`: move the head of tape `t` while `p` holds of
  the symbol under it (`Spec.scanRight`, `Spec.scanLeft`).
* `rewind t mk`: move the head of tape `t` back to the left-end marker `mk` in cell 0.
* `cases t gs f`: a finite case split on the symbol under head `t`, running
  `f g` when it reads `g` (`Spec.cases`). This is how finite tables (such as an
  NTM's transition function) get compiled into code.
* `copySym a b`: write the symbol under head `a` onto tape `b`.
-/

namespace Savitch.TM

open Machine (Dir)

variable {k : ℕ} {Γ : Type}

/-! ### Head positions -/

namespace Tapes

def setHead (T : Tapes k Γ) (t : Fin k) (n : ℕ) : Tapes k Γ :=
  { T with hd := Function.update T.hd t n }

variable (T : Tapes k Γ) (t : Fin k)

theorem move_right : T.move t .right = T.setHead t (T.hd t + 1) := rfl
theorem move_left : T.move t .left = T.setHead t (T.hd t - 1) := rfl

@[simp] theorem setHead_hd_self (n : ℕ) : (T.setHead t n).hd t = n := by simp [setHead]
@[simp] theorem setHead_tp (n : ℕ) : (T.setHead t n).tp = T.tp := rfl
@[simp] theorem setHead_ih (n : ℕ) : (T.setHead t n).ih = T.ih := rfl

theorem setHead_hd_ne {i : Fin k} (h : i ≠ t) (n : ℕ) : (T.setHead t n).hd i = T.hd i := by
  simp [setHead, h]

@[simp] theorem setHead_setHead (n m : ℕ) : (T.setHead t n).setHead t m = T.setHead t m := by
  ext <;> simp [setHead]

@[simp] theorem setHead_self : T.setHead t (T.hd t) = T := by
  ext <;> simp [setHead]

theorem within_setHead {B : ℕ} {T : Tapes k Γ} {t : Fin k} {n : ℕ} (hT : T.Within B)
    (hn : n < B) : (T.setHead t n).Within B := by
  intro i
  by_cases hi : i = t
  · subst hi; simpa using hn
  · rw [setHead_hd_ne T t hi]; exact hT i

@[simp] theorem write_hd (g : Γ) : (T.write t g).hd = T.hd := rfl
@[simp] theorem write_ih (g : Γ) : (T.write t g).ih = T.ih := rfl

theorem within_write {B : ℕ} {T : Tapes k Γ} {t : Fin k} {g : Γ} (hT : T.Within B) :
    (T.write t g).Within B := hT

end Tapes

/-! ### Trivial blocks -/

variable {x : List Bool} {B : ℕ}

theorem Spec.nil {T : Tapes k Γ} (hT : T.Within B) : Spec ([] : Code k Γ) x B T T :=
  .refl hT

theorem Spec.single {i : Instr k Γ} {T T' : Tapes k Γ} (h : i.exec x 0 T = .run 1 T')
    (hT : T.Within B) (hT' : T'.Within B) : Spec [i] x B T T' := by
  refine .step le_rfl (by simp) hT ?_
  rw [show Code.step [i] x (.run 0 T) = i.exec x 0 T from rfl, h]
  exact Seg.refl_of_eq (by simp) hT'

theorem Spec.write {t : Fin k} {g : Γ} {T : Tapes k Γ} (hT : T.Within B) :
    Spec [Instr.write t g] x B T (T.write t g) :=
  Spec.single rfl hT (Tapes.within_write hT)

theorem Spec.moveRight {t : Fin k} {T : Tapes k Γ} (hT : T.Within B) (hB : T.hd t + 1 < B) :
    Spec [Instr.move t .right] x B T (T.setHead t (T.hd t + 1)) :=
  Spec.single rfl hT (Tapes.within_setHead hT hB)

theorem Spec.moveLeft {t : Fin k} {T : Tapes k Γ} (hT : T.Within B) :
    Spec [Instr.move t .left] x B T (T.setHead t (T.hd t - 1)) :=
  Spec.single rfl hT (Tapes.within_setHead hT (by have := hT t; omega))

/-! ### Scanning -/

/-- Move right on tape `t` while `p` holds of the symbol under the head. -/
def scanRight (t : Fin k) (p : Γ → Bool) : Code k Γ :=
  whileDo (.tape t p) [Instr.move t .right]

/-- Move left on tape `t` while `p` holds of the symbol under the head. -/
def scanLeft (t : Fin k) (p : Γ → Bool) : Code k Γ :=
  whileDo (.tape t p) [Instr.move t .left]

theorem Spec.scanRight (t : Fin k) (p : Γ → Bool) :
    ∀ (m : ℕ) (T : Tapes k Γ), (∀ j < m, p (T.tp t (T.hd t + j)) = true) →
      p (T.tp t (T.hd t + m)) = false → T.Within B → T.hd t + m < B →
      Spec (TM.scanRight t p) x B T (T.setHead t (T.hd t + m)) := by
  intro m T hp hq hT hB
  apply Spec.whileDo
  induction m generalizing T with
  | zero =>
    rw [Nat.add_zero, Tapes.setHead_self]
    exact .stop (by simpa [Cond.eval, Tapes.read] using hq) hT
  | succ m ih =>
    have hT' : (T.setHead t (T.hd t + 1)).Within B := Tapes.within_setHead hT (by omega)
    refine .iter (by simpa [Cond.eval, Tapes.read] using hp 0 (by omega)) hT
      (Spec.moveRight hT (by omega)) ?_
    have := ih (T.setHead t (T.hd t + 1))
      (fun j hj => by
        have := hp (j + 1) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 j] using this)
      (by simpa [Nat.add_assoc, Nat.add_comm 1 m] using hq) hT' (by simp; omega)
    simpa [Nat.add_assoc, Nat.add_comm 1 m] using this

theorem Spec.scanLeft (t : Fin k) (p : Γ → Bool) :
    ∀ (m : ℕ) (T : Tapes k Γ), m ≤ T.hd t → (∀ j < m, p (T.tp t (T.hd t - j)) = true) →
      p (T.tp t (T.hd t - m)) = false → T.Within B →
      Spec (TM.scanLeft t p) x B T (T.setHead t (T.hd t - m)) := by
  intro m T hm hp hq hT
  apply Spec.whileDo
  induction m generalizing T with
  | zero =>
    rw [Nat.sub_zero, Tapes.setHead_self]
    exact .stop (by simpa [Cond.eval, Tapes.read] using hq) hT
  | succ m ih =>
    have hT' : (T.setHead t (T.hd t - 1)).Within B :=
      Tapes.within_setHead hT (by have := hT t; omega)
    refine .iter (by simpa [Cond.eval, Tapes.read] using hp 0 (by omega)) hT
      (Spec.moveLeft hT) ?_
    have := ih (T.setHead t (T.hd t - 1)) (by simp; omega)
      (fun j hj => by
        have := hp (j + 1) (by omega)
        simpa [show T.hd t - 1 - j = T.hd t - (j + 1) by omega] using this)
      (by simpa [show T.hd t - 1 - m = T.hd t - (m + 1) by omega] using hq) hT'
    simpa [show T.hd t - 1 - m = T.hd t - (m + 1) by omega] using this

section Marker

variable [DecidableEq Γ]

/-- Return the head of tape `t` to cell 0, which holds the left-end marker `mk`. -/
def rewind (t : Fin k) (mk : Γ) : Code k Γ := TM.scanLeft t (fun g => decide (g ≠ mk))

/-- `rewind` works when cell 0 holds the marker and no cell `1 … hd` does. -/
theorem Spec.rewind (t : Fin k) (mk : Γ) {T : Tapes k Γ} (h0 : T.tp t 0 = mk)
    (hne : ∀ j, 0 < j → j ≤ T.hd t → T.tp t j ≠ mk) (hT : T.Within B) :
    Spec (TM.rewind t mk) x B T (T.setHead t 0) := by
  have := Spec.scanLeft (x := x) t (fun g => decide (g ≠ mk)) (T.hd t) T le_rfl
    (fun j hj => by simpa using hne (T.hd t - j) (by omega) (by omega))
    (by simpa using h0) hT
  rw [Nat.sub_self] at this
  exact this

end Marker

/-! ### Finite case splits -/

section Cases

variable [DecidableEq Γ]

/-- Run `f g` where `g` is the symbol under head `t` (assumed to be in `gs`). -/
def cases (t : Fin k) (f : Γ → Code k Γ) : List Γ → Code k Γ
  | [] => []
  | g :: gs => ifElse (.tape t (fun h => decide (h = g))) (f g) (cases t f gs)

theorem Spec.cases (t : Fin k) (f : Γ → Code k Γ) :
    ∀ (gs : List Γ) {T T' : Tapes k Γ}, T.read t ∈ gs → T.Within B →
      Spec (f (T.read t)) x B T T' → Spec (TM.cases t f gs) x B T T'
  | [], _, _, hmem, _, _ => absurd hmem (List.not_mem_nil)
  | g :: gs, T, T', hmem, hT, h => by
    by_cases hg : T.read t = g
    · refine Spec.ifElse_true (by simp [Cond.eval, hg]) hT ?_
      rwa [← hg]
    · refine Spec.ifElse_false (by simp [Cond.eval, hg]) hT ?_
      exact Spec.cases t f gs (List.mem_of_ne_of_mem hg hmem) hT h

/-- Copy the symbol under head `a` to the cell under head `b`. -/
noncomputable def copySym [Fintype Γ] (a b : Fin k) : Code k Γ :=
  TM.cases a (fun g => [Instr.write b g]) Finset.univ.toList

theorem Spec.copySym [Fintype Γ] (a b : Fin k) {T : Tapes k Γ} (hT : T.Within B) :
    Spec (TM.copySym a b) x B T (T.write b (T.read a)) :=
  Spec.cases a _ _ (by simp) hT (Spec.write hT)

end Cases

/-! ### Lockstep copy -/

section Copy

/-- Tapes after copying `m` cells from tape `a` (starting at its head) to tape `b`
(starting at its head), with both heads advanced by `m`. -/
def Tapes.copyRes (T : Tapes k Γ) (a b : Fin k) (m : ℕ) : Tapes k Γ where
  ih := T.ih
  hd := Function.update (Function.update T.hd a (T.hd a + m)) b (T.hd b + m)
  tp := Function.update T.tp b (fun j =>
    if T.hd b ≤ j ∧ j < T.hd b + m then T.tp a (T.hd a + (j - T.hd b)) else T.tp b j)

/-- Tapes after one iteration of the copy loop. -/
def Tapes.copyStep (T : Tapes k Γ) (a b : Fin k) : Tapes k Γ :=
  ((T.write b (T.read a)).setHead a (T.hd a + 1)).setHead b (T.hd b + 1)

theorem Tapes.copyRes_zero (T : Tapes k Γ) (a b : Fin k) : T.copyRes a b 0 = T := by
  ext i
  · rfl
  · by_cases hb : i = b
    · subst hb; simp [copyRes]
    · by_cases ha : i = a
      · subst ha; simp [copyRes]
      · simp [copyRes]
  · rename_i j
    by_cases hb : i = b
    · subst hb
      simp only [copyRes, Function.update_self]
      split_ifs with h
      · omega
      · rfl
    · simp [copyRes, hb]

variable {a b : Fin k}

theorem Tapes.copyStep_hd_a (hab : a ≠ b) (T : Tapes k Γ) :
    (T.copyStep a b).hd a = T.hd a + 1 := by
  simp [copyStep, setHead, hab]

theorem Tapes.copyStep_hd_b (T : Tapes k Γ) : (T.copyStep a b).hd b = T.hd b + 1 := by
  simp [copyStep, setHead]

theorem Tapes.copyStep_tp_a (hab : a ≠ b) (T : Tapes k Γ) :
    (T.copyStep a b).tp a = T.tp a := by
  simp [copyStep, write, hab]

theorem Tapes.copyRes_succ (hab : a ≠ b) (T : Tapes k Γ) (m : ℕ) :
    (T.copyStep a b).copyRes a b m = T.copyRes a b (m + 1) := by
  ext i
  · rfl
  · simp only [copyRes, copyStep, setHead, write, Function.update_apply]
    split_ifs <;> omega
  · rename_i j
    by_cases hb : i = b
    · subst hb
      simp only [copyRes, copyStep, setHead, write, read, Function.update_apply, ite_true,
        Ne.symm hab, ite_false, hab]
      split_ifs <;> first | rfl | omega | (congr 1; omega)
    · simp [copyRes, copyStep, write, hb]

theorem Tapes.within_copyStep {B : ℕ} {T : Tapes k Γ} (hT : T.Within B)
    (ha : T.hd a + 1 < B) (hb : T.hd b + 1 < B) : (T.copyStep a b).Within B :=
  Tapes.within_setHead (Tapes.within_setHead (Tapes.within_write hT) ha) hb

variable [DecidableEq Γ] [Fintype Γ]

/-- One copy iteration: copy the symbol, then advance both heads. -/
noncomputable def copyBody (a b : Fin k) : Code k Γ :=
  TM.copySym a b ++ [Instr.move a .right] ++ [Instr.move b .right]

theorem Spec.copyBody (hab : a ≠ b) {T : Tapes k Γ} (hT : T.Within B)
    (ha : T.hd a + 1 < B) (hb : T.hd b + 1 < B) :
    Spec (TM.copyBody a b) x B T (T.copyStep a b) := by
  have h1 := Spec.copySym (x := x) a b hT
  have h2 := Spec.moveRight (x := x) (t := a) (Tapes.within_write (g := T.read a) (t := b) hT)
    (by simpa using ha)
  have h3 := Spec.moveRight (x := x) (t := b)
    (Tapes.within_setHead (n := T.hd a + 1) (t := a) (Tapes.within_write (g := T.read a) (t := b) hT) ha)
    (by rw [Tapes.setHead_hd_ne _ _ (Ne.symm hab)]; simpa using hb)
  rw [Tapes.setHead_hd_ne _ _ (Ne.symm hab), Tapes.write_hd] at h3
  exact (h1.seq h2).seq h3

/-- Copy from tape `a` to tape `b`, cell by cell, while `p` holds on tape `a`. -/
noncomputable def copyWhile (a b : Fin k) (p : Γ → Bool) : Code k Γ :=
  whileDo (.tape a p) (TM.copyBody a b)

theorem Spec.copyWhile (hab : a ≠ b) (p : Γ → Bool) :
    ∀ (m : ℕ) (T : Tapes k Γ), (∀ j < m, p (T.tp a (T.hd a + j)) = true) →
      p (T.tp a (T.hd a + m)) = false → T.Within B → T.hd a + m < B → T.hd b + m < B →
      Spec (TM.copyWhile a b p) x B T (T.copyRes a b m) := by
  intro m T hp hq hT hBa hBb
  apply Spec.whileDo
  induction m generalizing T with
  | zero =>
    rw [Tapes.copyRes_zero]
    exact .stop (by simpa [Cond.eval, Tapes.read] using hq) hT
  | succ m ih =>
    refine .iter (by simpa [Cond.eval, Tapes.read] using hp 0 (by omega)) hT
      (Spec.copyBody hab hT (by omega) (by omega)) ?_
    rw [← Tapes.copyRes_succ hab]
    apply ih
    · intro j hj
      rw [Tapes.copyStep_tp_a hab, Tapes.copyStep_hd_a hab]
      have := hp (j + 1) (by omega)
      rwa [show T.hd a + (j + 1) = T.hd a + 1 + j by omega] at this
    · rw [Tapes.copyStep_tp_a hab, Tapes.copyStep_hd_a hab]
      rwa [show T.hd a + (m + 1) = T.hd a + 1 + m by omega] at hq
    · exact Tapes.within_copyStep hT (by omega) (by omega)
    · rw [Tapes.copyStep_hd_a hab]; omega
    · rw [Tapes.copyStep_hd_b]; omega

end Copy

end Savitch.TM
