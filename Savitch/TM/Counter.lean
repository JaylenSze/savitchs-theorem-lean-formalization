import Savitch.TM.Binary
import Savitch.TM.Frame

/-!
# Binary counters: decrement and zero test

Phase 4b-4 groundwork (see `PLAN.md`).

* `bdec l`: little-endian decrement; `bval_bdec` shows it subtracts one.
* `decr t z o`: in-place decrement. It is literally `incr` with the two bit symbols
  swapped, and `Spec.decr` is derived from `Spec.incr` (`binc_map_not`).
* `isZeroB t f z o yes no`: write `yes` under head `f` iff the block under head `t`
  is all zeros (`Spec.isZeroB`).
-/

set_option linter.unusedSectionVars false

namespace Savitch.TM

/-! ### Decrement -/

def bdec : List Bool → List Bool
  | [] => []
  | false :: l => true :: bdec l
  | true :: l => false :: l

theorem bdec_length : ∀ l : List Bool, (bdec l).length = l.length
  | [] => rfl
  | false :: l => by simp [bdec, bdec_length l]
  | true :: l => rfl

theorem bval_bdec : ∀ l : List Bool, 0 < bval l → bval (bdec l) = bval l - 1
  | [], h => by simp [bval] at h
  | false :: l, h => by
    have : 0 < bval l := by simp [bval] at h; omega
    simp [bdec, bval, bval_bdec l this]; omega
  | true :: l, _ => by simp [bdec, bval]

theorem binc_map_not : ∀ l : List Bool, binc (l.map not) = (bdec l).map not
  | [] => rfl
  | false :: l => by simp [binc, bdec, binc_map_not l]
  | true :: l => by simp [binc, bdec]

theorem bval_eq_zero_iff : ∀ l : List Bool, bval l = 0 ↔ ∀ b ∈ l, b = false
  | [] => by simp [bval]
  | b :: l => by
    have := bval_eq_zero_iff l
    cases b <;> simp [bval, this]

variable {k : ℕ} {Γ : Type} [DecidableEq Γ] {x : List Bool} {B : ℕ}

theorem bsym_not (z o : Γ) (b : Bool) : bsym o z (!b) = bsym z o b := by
  cases b <;> rfl

/-- In-place binary decrement: `incr` with the bit symbols swapped. -/
def decr (t : Fin k) (z o : Γ) : Code k Γ := incr t o z

/-- **Binary decrement on tape.** -/
theorem Spec.decr (t : Fin k) (z o : Γ) (hzo : z ≠ o) (l : List Bool) (T : Tapes k Γ)
    (hseg : seg (T.tp t) (T.hd t) l.length = l.map (bsym z o))
    (hz : T.tp t (T.hd t + l.length) ≠ z) (ho : T.tp t (T.hd t + l.length) ≠ o)
    (hT : T.Within B) (hB : T.hd t + l.length < B) :
    ∃ T', Spec (TM.decr t z o) x B T T' ∧
      seg (T'.tp t) (T.hd t) l.length = (bdec l).map (bsym z o) ∧
      (∀ j, (j < T.hd t ∨ T.hd t + l.length ≤ j) → T'.tp t j = T.tp t j) ∧
      T.Frame t T' ∧ T'.hd t ≤ T.hd t + l.length := by
  have hmap : ∀ l' : List Bool, (l'.map not).map (bsym o z) = l'.map (bsym z o) := fun l' => by
    rw [List.map_map]; congr 1; funext b; exact bsym_not z o b
  obtain ⟨T', h, p1, p2, p3, p4⟩ := Spec.incr (x := x) t o z (Ne.symm hzo) (l.map not) T
    (by rw [List.length_map, hseg, hmap]) (by rw [List.length_map]; exact ho)
    (by rw [List.length_map]; exact hz) hT (by rw [List.length_map]; exact hB)
  rw [List.length_map, binc_map_not, hmap] at p1
  rw [List.length_map] at p2 p4
  exact ⟨T', h, p1, p2, p3, p4⟩

/-! ### Zero test -/

/-- Is `g` one of the two bit symbols? -/
def isBit (z o : Γ) (g : Γ) : Bool := decide (g = z) || decide (g = o)

def isZeroBody (t f : Fin k) (o no : Γ) : Code k Γ :=
  ifElse (.tape t (fun g => decide (g = o))) [Instr.write f no] [] ++ [Instr.move t .right]

/-- Write `yes` under head `f` iff the bit block under head `t` is all zeros. -/
def isZeroB (t f : Fin k) (z o yes no : Γ) : Code k Γ :=
  [Instr.write f yes] ++ whileDo (.tape t (isBit z o)) (isZeroBody t f o no)

theorem isZero_aux {t f : Fin k} (htf : t ≠ f) {z o no : Γ} (hzo : z ≠ o) :
    ∀ (l : List Bool) (T : Tapes k Γ),
      seg (T.tp t) (T.hd t) l.length = l.map (bsym z o) →
      T.tp t (T.hd t + l.length) ≠ z → T.tp t (T.hd t + l.length) ≠ o →
      T.Within B → T.hd t + l.length < B →
      ∃ T', Loop (.tape t (isBit z o)) (isZeroBody t f o no) x B T T' ∧
        T'.tp f (T.hd f) = (if bval l = 0 then T.read f else no) ∧
        (∀ j, j ≠ T.hd f → T'.tp f j = T.tp f j) ∧
        T'.tp t = T.tp t ∧ T'.hd t = T.hd t + l.length ∧ T'.hd f = T.hd f ∧
        T.Agree (fun i => i = t ∨ i = f) T' ∧ T'.ih = T.ih
  | [], T, _, hz, ho, hT, _ => by
    have hz' : T.read t ≠ z := by simpa [Tapes.read] using hz
    have ho' : T.read t ≠ o := by simpa [Tapes.read] using ho
    refine ⟨T, .stop (by simp [Cond.eval, isBit, hz', ho']) hT, ?_⟩
    exact ⟨by simp [bval, Tapes.read], fun _ _ => rfl, rfl, by simp, rfl,
      Tapes.Agree.refl _ T, rfl⟩
  | b :: l, T, hseg, hz, ho, hT, hB => by
    simp only [seg, List.map, List.length_cons] at hseg hz ho hB
    obtain ⟨h0, hrest⟩ := List.cons.inj hseg
    have hr : T.read t = bsym z o b := h0
    set T₀ := if b then T.write f no else T with hT₀def
    have hT₀hd : T₀.hd = T.hd := by cases b <;> simp [T₀]
    have hT₀ih : T₀.ih = T.ih := by cases b <;> simp [T₀]
    have hT₀t : T₀.tp t = T.tp t := by cases b <;> simp [T₀, Tapes.write, htf]
    have hT₀f : ∀ j, j ≠ T.hd f → T₀.tp f j = T.tp f j := fun j hj => by
      cases b
      · rfl
      · simp only [T₀, ite_true]; rw [Tapes.write_tp_self, ite_neg' hj]
    have hT₀flag : T₀.tp f (T.hd f) = if b then no else T.read f := by
      cases b <;> simp [T₀, Tapes.read, Tapes.write_tp_self]
    have hT₀others : ∀ i, i ≠ f → T₀.tp i = T.tp i := fun i hi => by
      cases b <;> simp [T₀, Tapes.write, hi]
    have hT₀W : T₀.Within B := fun i => by rw [hT₀hd]; exact hT i
    have hif : Spec (ifElse (.tape t (fun g => decide (g = o))) [Instr.write f no] [])
        x B T T₀ := by
      cases b
      · exact Spec.ifElse_false (by simp [Cond.eval, hr, bsym, hzo]) hT (Spec.nil hT)
      · exact Spec.ifElse_true (by simp [Cond.eval, hr, bsym]) hT (Spec.write hT)
    set T₁ := T₀.setHead t (T₀.hd t + 1) with hT₁def
    have hT₁hd_t : T₁.hd t = T.hd t + 1 := by simp [T₁, hT₀hd]
    have hT₁hd : ∀ i, i ≠ t → T₁.hd i = T.hd i := fun i hi => by
      simp [T₁, Tapes.setHead_hd_ne _ _ hi, hT₀hd]
    have hT₁W : T₁.Within B := Tapes.within_setHead hT₀W (by rw [hT₀hd]; omega)
    have hbody : Spec (isZeroBody t f o no) x B T T₁ :=
      hif.seq (Spec.moveRight hT₀W (by rw [hT₀hd]; omega))
    obtain ⟨T', hloop, hP1, hP2, hP3, hP4, hP5, hP6, hP7⟩ :=
      isZero_aux htf hzo l T₁
        (by rw [hT₁hd_t]; simp only [T₁, Tapes.setHead_tp, hT₀t]; exact hrest)
        (by rw [hT₁hd_t]; simp only [T₁, Tapes.setHead_tp, hT₀t]
            rwa [Nat.add_assoc, Nat.add_comm 1])
        (by rw [hT₁hd_t]; simp only [T₁, Tapes.setHead_tp, hT₀t]
            rwa [Nat.add_assoc, Nat.add_comm 1])
        hT₁W (by rw [hT₁hd_t]; omega)
    have hcond : Cond.eval x T (.tape t (isBit z o)) = true := by
      simp only [Cond.eval, isBit, hr]; cases b <;> simp [bsym]
    have hf : T₁.hd f = T.hd f := hT₁hd f (Ne.symm htf)
    refine ⟨T', .iter hcond hT hbody hloop, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hf] at hP1
      rw [hP1]
      simp only [Tapes.read, hf, T₁, Tapes.setHead_tp, hT₀flag]
      cases b <;> simp [bval]
    · intro j hj
      rw [hP2 j (by rw [hf]; exact hj)]
      simp only [T₁, Tapes.setHead_tp]
      exact hT₀f j hj
    · rw [hP3]; simp only [T₁, Tapes.setHead_tp, hT₀t]
    · rw [hP4, hT₁hd_t]; simp only [List.length_cons]; omega
    · rw [hP5, hf]
    · intro i hi
      have hit : i ≠ t := fun e => hi (Or.inl e)
      have hif' : i ≠ f := fun e => hi (Or.inr e)
      refine ⟨(hP6 i hi).1.trans ?_, (hP6 i hi).2.trans (hT₁hd i hit)⟩
      simp only [T₁, Tapes.setHead_tp]
      exact hT₀others i hif'
    · rw [hP7]; simp [T₁, hT₀ih]

/-- **Zero test on tape.** -/
theorem Spec.isZeroB {t f : Fin k} (htf : t ≠ f) {z o yes no : Γ} (hzo : z ≠ o)
    (l : List Bool) (T : Tapes k Γ)
    (hseg : seg (T.tp t) (T.hd t) l.length = l.map (bsym z o))
    (hz : T.tp t (T.hd t + l.length) ≠ z) (ho : T.tp t (T.hd t + l.length) ≠ o)
    (hT : T.Within B) (hB : T.hd t + l.length < B) :
    ∃ T', Spec (TM.isZeroB t f z o yes no) x B T T' ∧
      T'.tp f (T.hd f) = (if bval l = 0 then yes else no) ∧
      (∀ j, j ≠ T.hd f → T'.tp f j = T.tp f j) ∧
      T'.tp t = T.tp t ∧ T'.hd t = T.hd t + l.length ∧ T'.hd f = T.hd f ∧
      T.Agree (fun i => i = t ∨ i = f) T' ∧ T'.ih = T.ih := by
  have hW := Tapes.within_write (t := f) (g := yes) hT
  have hwt : (T.write f yes).tp t = T.tp t := by simp [Tapes.write, htf]
  obtain ⟨T', hloop, p1, p2, p3, p4, p5, p6, p7⟩ := isZero_aux (x := x) (no := no) htf hzo l
    (T.write f yes) (by simp only [Tapes.write_hd, hwt]; exact hseg)
    (by simp only [Tapes.write_hd, hwt]; exact hz) (by simp only [Tapes.write_hd, hwt]; exact ho)
    hW hB
  simp only [Tapes.write_hd] at p1 p2 p4 p5
  refine ⟨T', (Spec.write hT).seq (Spec.whileDo hloop), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p1]; simp [Tapes.read, Tapes.write_tp_self]
  · intro j hj; rw [p2 j hj, Tapes.write_tp_self, ite_neg' hj]
  · rw [p3, hwt]
  · exact p4
  · exact p5
  · intro i hi
    have hif : i ≠ f := fun e => hi (Or.inr e)
    exact ⟨(p6 i hi).1.trans (by simp [Tapes.write, hif]), (p6 i hi).2⟩
  · exact p7

end Savitch.TM
