import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Card

/-!
# Bounded reachability

Phase 1 of the Savitch formalization (see `PLAN.md`).

`ReachIn R n a b` says that `b` is reachable from `a` by at most `n` steps of `R`.

Main results:
* `ReachIn.add_iff`: midpoint splitting, `≤ m + n` steps ↔ `≤ m` steps then `≤ n` steps.
* `ReachIn.reflTransGen_iff_card`: on a finite type, reachability is equivalent
  to reachability within `Fintype.card α` steps.
-/

namespace Savitch

variable {α : Type*}

/-- `ReachIn R n a b`: `b` is reachable from `a` in at most `n` steps of `R`. -/
inductive ReachIn (R : α → α → Prop) : ℕ → α → α → Prop
  | refl (n : ℕ) (a : α) : ReachIn R n a a
  | step {n : ℕ} {a b c : α} : R a b → ReachIn R n b c → ReachIn R (n + 1) a c

namespace ReachIn

variable {R : α → α → Prop}

theorem zero_iff {a b : α} : ReachIn R 0 a b ↔ a = b := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .refl 0 a

/-- First-step characterization. -/
theorem succ_iff {n : ℕ} {a c : α} :
    ReachIn R (n + 1) a c ↔ a = c ∨ ∃ b, R a b ∧ ReachIn R n b c := by
  constructor
  · intro h
    cases h with
    | refl => exact Or.inl rfl
    | step hab hbc => exact Or.inr ⟨_, hab, hbc⟩
  · rintro (rfl | ⟨b, hab, hbc⟩)
    · exact .refl _ _
    · exact .step hab hbc

theorem one_iff {a b : α} : ReachIn R 1 a b ↔ a = b ∨ R a b := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, succ_iff]
  simp only [zero_iff, exists_eq_right]

theorem mono {m n : ℕ} {a b : α} (h : ReachIn R m a b) (hmn : m ≤ n) : ReachIn R n a b := by
  induction h generalizing n with
  | refl _ a => exact .refl n a
  | step hab _ ih =>
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact .step hab (ih (n := k) (by omega))

theorem trans {m n : ℕ} {a b c : α} (hab : ReachIn R m a b) (hbc : ReachIn R n b c) :
    ReachIn R (m + n) a c := by
  revert hbc
  induction hab with
  | refl k _ =>
    intro hbc
    exact hbc.mono (by omega)
  | step hab' _ ih =>
    intro hbc
    have := ReachIn.step hab' (ih hbc)
    rwa [Nat.add_right_comm] at this

/-- **Midpoint lemma**: a path of length `≤ m + n` splits at some midpoint. -/
theorem add_iff {m n : ℕ} {a c : α} :
    ReachIn R (m + n) a c ↔ ∃ b, ReachIn R m a b ∧ ReachIn R n b c := by
  constructor
  · intro h
    induction m generalizing a with
    | zero => exact ⟨a, .refl 0 a, by simpa using h⟩
    | succ m ih =>
      rw [Nat.add_right_comm] at h
      rcases succ_iff.1 h with rfl | ⟨b, hab, hbc⟩
      · exact ⟨_, .refl _ _, .refl _ _⟩
      · obtain ⟨d, hbd, hdc⟩ := ih (a := b) hbc
        exact ⟨d, .step hab hbd, hdc⟩
  · rintro ⟨b, hab, hbc⟩
    exact hab.trans hbc

/-- Last-step characterization. -/
theorem succ_iff' {n : ℕ} {a c : α} :
    ReachIn R (n + 1) a c ↔ ∃ b, ReachIn R n a b ∧ (b = c ∨ R b c) := by
  rw [add_iff]
  simp only [one_iff]

theorem to_reflTransGen {n : ℕ} {a b : α} (h : ReachIn R n a b) :
    Relation.ReflTransGen R a b := by
  induction h with
  | refl => exact .refl
  | step hab _ ih => exact ih.head hab

theorem exists_of_reflTransGen {a b : α} (h : Relation.ReflTransGen R a b) :
    ∃ n, ReachIn R n a b := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .refl 0 _⟩
  | head hac _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .step hac hn⟩

/-! ### The card bound -/

section Card

variable [Fintype α]

open Classical in
/-- The (finite) set of vertices reachable from `a` within `k` steps. -/
noncomputable def reachSet (R : α → α → Prop) (a : α) (k : ℕ) : Finset α :=
  Finset.univ.filter (fun x => ReachIn R k a x)

theorem mem_reachSet {a x : α} {k : ℕ} : x ∈ reachSet R a k ↔ ReachIn R k a x := by
  simp [reachSet]

/-- `reachSet` at step `k + 1` is determined by `reachSet` at step `k`. -/
theorem reachSet_succ_congr {a : α} {m n : ℕ} (h : reachSet R a m = reachSet R a n) :
    reachSet R a (m + 1) = reachSet R a (n + 1) := by
  have hmn : ∀ y, ReachIn R m a y ↔ ReachIn R n a y := fun y => by
    simpa only [mem_reachSet] using Finset.ext_iff.1 h y
  ext x
  simp only [mem_reachSet, succ_iff', hmn]

/-- Once `reachSet` stops growing, it stays fixed forever. -/
theorem reachSet_stable {a : α} {k : ℕ} (h : reachSet R a (k + 1) = reachSet R a k) :
    ∀ j, reachSet R a (k + j) = reachSet R a k := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← Nat.add_assoc, reachSet_succ_congr ih, h]

/-- Pigeonhole: `reachSet` must stop growing before step `Fintype.card α`. -/
theorem exists_stable (a : α) :
    ∃ k < Fintype.card α, reachSet R a (k + 1) = reachSet R a k := by
  by_contra hcon
  push Not at hcon
  have hgrow : ∀ k ≤ Fintype.card α, k + 1 ≤ (reachSet R a k).card := by
    intro k
    induction k with
    | zero =>
      intro _
      have hne : (reachSet R a 0).Nonempty := ⟨a, mem_reachSet.2 (.refl 0 a)⟩
      have := Finset.card_pos.2 hne
      omega
    | succ k ih =>
      intro hk
      have hss : reachSet R a k ⊂ reachSet R a (k + 1) := by
        refine Finset.ssubset_iff_subset_ne.2 ⟨?_, (hcon k (by omega)).symm⟩
        intro x hx
        exact mem_reachSet.2 ((mem_reachSet.1 hx).mono (Nat.le_succ k))
      have h1 := Finset.card_lt_card hss
      have h2 := ih (by omega)
      omega
  have h1 := hgrow _ le_rfl
  have h2 := Finset.card_le_univ (reachSet R a (Fintype.card α))
  omega

theorem of_reflTransGen_card {a b : α} (h : Relation.ReflTransGen R a b) :
    ReachIn R (Fintype.card α) a b := by
  obtain ⟨n, hn⟩ := exists_of_reflTransGen h
  obtain ⟨k, hk, hstab⟩ := exists_stable (R := R) a
  have h1 : ReachIn R (k + n) a b := hn.mono (by omega)
  have h2 : ReachIn R k a b := by
    rw [← mem_reachSet, ← reachSet_stable hstab n]
    exact mem_reachSet.2 h1
  exact h2.mono hk.le

/-- On a finite type, reachability is reachability within `Fintype.card α` steps. -/
theorem reflTransGen_iff_card {a b : α} :
    Relation.ReflTransGen R a b ↔ ReachIn R (Fintype.card α) a b :=
  ⟨of_reflTransGen_card, to_reflTransGen⟩

end Card

end ReachIn

end Savitch
