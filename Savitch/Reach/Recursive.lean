import Savitch.Reach.Basic
import Mathlib.Data.Nat.Log

/-!
# The recursive Savitch procedure

`savitch R k a b` decides whether `b` is reachable from `a` within `2 ^ k` steps,
by guessing every midpoint `c` and recursing on both halves.

This is the *mathematical* algorithm only: Lean's own recursion has no space
measure. The space-accounted version is Phase 2 (see `PLAN.md`).

Main results:
* `savitch_spec`: `savitch R k a b = true ↔ ReachIn R (2 ^ k) a b`.
* `savitch_correct`: with depth `Nat.clog 2 (Fintype.card α)`, `savitch` decides
  ordinary reachability (`Relation.ReflTransGen R`).
-/

namespace Savitch

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Is `b` reachable from `a` within `2 ^ k` steps? Midpoint recursion. -/
def savitch (R : α → α → Prop) [DecidableRel R] : ℕ → α → α → Bool
  | 0, a, b => decide (a = b) || decide (R a b)
  | k + 1, a, b => decide (∃ c, savitch R k a c = true ∧ savitch R k c b = true)

variable {R : α → α → Prop} [DecidableRel R]

theorem savitch_spec (k : ℕ) (a b : α) :
    savitch R k a b = true ↔ ReachIn R (2 ^ k) a b := by
  induction k generalizing a b with
  | zero => simp [savitch, ReachIn.one_iff]
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_two, ReachIn.add_iff]
    simp [savitch, ih]

/-- **Correctness of Savitch's procedure.** Recursion depth `⌈log₂ |α|⌉` suffices. -/
theorem savitch_correct (a b : α) :
    savitch R (Nat.clog 2 (Fintype.card α)) a b = true ↔ Relation.ReflTransGen R a b := by
  rw [savitch_spec]
  constructor
  · exact ReachIn.to_reflTransGen
  · intro h
    exact (ReachIn.of_reflTransGen_card h).mono (Nat.le_pow_clog (by decide) _)

/-! ### Sanity checks -/

/-- The path graph `0 → 1 → 2 → 3`. -/
private def pathRel : Fin 4 → Fin 4 → Prop := fun a b => b.val = a.val + 1

private instance : DecidableRel pathRel := fun a b =>
  inferInstanceAs (Decidable (b.val = a.val + 1))

#guard savitch pathRel 2 0 3       -- 3 steps ≤ 2^2
#guard !(savitch pathRel 1 0 3)    -- 3 steps > 2^1
#guard !(savitch pathRel 2 3 0)    -- edges go one way

end Savitch
