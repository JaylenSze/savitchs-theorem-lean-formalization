import Savitch.Reach.Recursive

/-!
# The Savitch stack machine over an arbitrary vertex type `Fin N`

Phase 4b-3 of the Savitch formalization (see `PLAN.md`).

This is the Phase 2 machine (`Savitch/Space/StackMachine.lean`) with vertices
`Fin N` for any `N > 0` instead of `Fin (2 ^ w)`. The Turing machine of
Phase 4b refines *this* machine. It needs only:

* `run_correct` / `decides`: with depth `K` and `N ≤ 2 ^ K`, the machine halts
  with the answer to reachability;
* `reachable_stack_le`: every reachable state has at most `K` frames.

The bit-level space measure of Phase 2 is not needed here: the Turing machine's
space is measured on its own tapes.
-/

namespace Savitch.Gen

inductive Phase
  | left
  | right
  deriving DecidableEq

structure Frame (N : ℕ) where
  k : ℕ
  a : Fin N
  b : Fin N
  c : Fin N
  phase : Phase

inductive State (N : ℕ) where
  | call (k : ℕ) (a b : Fin N) (stack : List (Frame N))
  | ret (r : Bool) (stack : List (Frame N))
  | done (r : Bool)

variable {N : ℕ} [NeZero N]

def zero : Fin N := ⟨0, Nat.pos_of_neZero N⟩

def advance (k : ℕ) (a b c : Fin N) (st : List (Frame N)) : State N :=
  if h : c.val + 1 < N then
    .call k a ⟨c.val + 1, h⟩ (⟨k, a, b, ⟨c.val + 1, h⟩, .left⟩ :: st)
  else
    .ret false st

variable (E : Fin N → Fin N → Bool)

def step : State N → State N
  | .call 0 a b st => .ret (decide (a = b) || E a b) st
  | .call (k + 1) a b st => .call k a zero (⟨k, a, b, zero, .left⟩ :: st)
  | .ret r [] => .done r
  | .ret true (⟨k, a, b, c, .left⟩ :: st) => .call k c b (⟨k, a, b, c, .right⟩ :: st)
  | .ret false (⟨k, a, b, c, .left⟩ :: st) => advance k a b c st
  | .ret true (⟨_, _, _, _, .right⟩ :: st) => .ret true st
  | .ret false (⟨k, a, b, c, .right⟩ :: st) => advance k a b c st
  | .done r => .done r

def init (K : ℕ) (a b : Fin N) : State N := .call K a b []

def StepRel (s t : State N) : Prop := step E s = t

def Rel (s t : Fin N) : Prop := E s t = true

instance : DecidableRel (Rel E) := fun s t => inferInstanceAs (Decidable (E s t = true))

def Found (k : ℕ) (a b c : Fin N) : Prop :=
  ∃ c', c ≤ c' ∧ savitch (Rel E) k a c' = true ∧ savitch (Rel E) k c' b = true

instance (k : ℕ) (a b c : Fin N) : Decidable (Found E k a b c) := by
  unfold Found; infer_instance

theorem zero_le' (c : Fin N) : (zero : Fin N) ≤ c := Fin.le_def.2 (Nat.zero_le _)

theorem found_zero (k : ℕ) (a b : Fin N) :
    decide (Found E k a b zero) = savitch (Rel E) (k + 1) a b := by
  simp [Found, savitch, zero_le']

omit [NeZero N] in
theorem found_iff_next {k : ℕ} {a b c : Fin N} (h : c.val + 1 < N)
    (hfail : ¬ (savitch (Rel E) k a c = true ∧ savitch (Rel E) k c b = true)) :
    Found E k a b c ↔ Found E k a b ⟨c.val + 1, h⟩ := by
  constructor
  · rintro ⟨c', hc', h₁, h₂⟩
    refine ⟨c', ?_, h₁, h₂⟩
    rw [Fin.le_def] at hc' ⊢
    by_contra hlt
    have : c' = c := Fin.ext (by simp only at hlt; omega)
    exact hfail (this ▸ ⟨h₁, h₂⟩)
  · rintro ⟨c', hc', h₁, h₂⟩
    refine ⟨c', ?_, h₁, h₂⟩
    rw [Fin.le_def] at hc' ⊢
    simp only at hc'
    omega

omit [NeZero N] in
theorem not_found_last {k : ℕ} {a b c : Fin N} (h : ¬ c.val + 1 < N)
    (hfail : ¬ (savitch (Rel E) k a c = true ∧ savitch (Rel E) k c b = true)) :
    ¬ Found E k a b c := by
  rintro ⟨c', hc', h₁, h₂⟩
  rw [Fin.le_def] at hc'
  have : c' = c := Fin.ext (by have := c'.isLt; omega)
  exact hfail (this ▸ ⟨h₁, h₂⟩)

local notation "RTG" => Relation.ReflTransGen

theorem loop {k : ℕ} {a b : Fin N} {st : List (Frame N)}
    (hk : ∀ a b st, RTG (StepRel E) (.call k a b st) (.ret (savitch (Rel E) k a b) st)) :
    ∀ m (c : Fin N), N - c.val = m →
      RTG (StepRel E) (.call k a c (⟨k, a, b, c, .left⟩ :: st))
        (.ret (decide (Found E k a b c)) st) := by
  have hadv : ∀ m (c : Fin N), N - c.val = m + 1 →
      (∀ c' : Fin N, N - c'.val = m →
        RTG (StepRel E) (.call k a c' (⟨k, a, b, c', .left⟩ :: st))
          (.ret (decide (Found E k a b c')) st)) →
      ¬ (savitch (Rel E) k a c = true ∧ savitch (Rel E) k c b = true) →
      RTG (StepRel E) (advance k a b c st) (.ret (decide (Found E k a b c)) st) := by
    intro m c hm ih hfail
    by_cases hlt : c.val + 1 < N
    · simp only [advance, hlt, ↓reduceDIte]
      rw [decide_eq_decide.2 (found_iff_next E hlt hfail)]
      exact ih _ (by simp only; omega)
    · simp only [advance, hlt, ↓reduceDIte]
      rw [decide_eq_false (not_found_last E hlt hfail)]
  intro m
  induction m with
  | zero =>
    intro c hc
    have := c.isLt
    omega
  | succ m ih =>
    intro c hc
    refine (hk a c _).trans ?_
    cases hac : savitch (Rel E) k a c
    · exact .head rfl (hadv m c hc ih (by simp [hac]))
    · refine .head rfl ((hk c b _).trans ?_)
      cases hcb : savitch (Rel E) k c b
      · exact .head rfl (hadv m c hc ih (by simp [hcb]))
      · have hfound : decide (Found E k a b c) = true :=
          decide_eq_true ⟨c, le_refl c, hac, hcb⟩
        rw [hfound]
        exact .single rfl

theorem call_correct :
    ∀ k (a b : Fin N) st, RTG (StepRel E) (.call k a b st) (.ret (savitch (Rel E) k a b) st) := by
  intro k
  induction k with
  | zero =>
    intro a b st
    have hsav : savitch (Rel E) 0 a b = (decide (a = b) || E a b) := by
      show (decide (a = b) || decide (Rel E a b)) = _
      cases h : E a b <;> simp [Rel, h]
    rw [hsav]
    exact .single rfl
  | succ k ih =>
    intro a b st
    rw [← found_zero]
    exact .head rfl (loop E ih _ zero rfl)

/-- **Correctness.** The machine halts with the answer of `savitch`. -/
theorem run_correct (K : ℕ) (a b : Fin N) :
    RTG (StepRel E) (init K a b) (.done (savitch (Rel E) K a b)) :=
  (call_correct E K a b []).tail rfl

omit [NeZero N] in
/-- With depth `K ≥ log₂ N`, the answer is reachability. -/
theorem decides {K : ℕ} (hK : N ≤ 2 ^ K) (a b : Fin N) :
    savitch (Rel E) K a b = true ↔ RTG (Rel E) a b := by
  rw [savitch_spec]
  constructor
  · exact ReachIn.to_reflTransGen
  · intro h
    exact (ReachIn.of_reflTransGen_card h).mono (by simpa using hK)

/-! ### Stack depth -/

def StackOK (K : ℕ) : List (Frame N) → Prop
  | [] => True
  | f :: st => f.k + (st.length + 1) = K ∧ StackOK K st

def DepthInv (K : ℕ) : State N → Prop
  | .call k _ _ st => StackOK K st ∧ k + st.length = K
  | .ret _ st => StackOK K st
  | .done _ => True

def State.stack : State N → List (Frame N)
  | .call _ _ _ st => st
  | .ret _ st => st
  | .done _ => []

omit [NeZero N] in
theorem depthInv_advance {K k : ℕ} {a b c : Fin N} {st : List (Frame N)}
    (h : k + (st.length + 1) = K) (hst : StackOK K st) : DepthInv K (advance k a b c st) := by
  unfold advance
  split_ifs
  · exact ⟨⟨h, hst⟩, h⟩
  · exact hst

theorem depthInv_step {K : ℕ} : ∀ {s : State N}, DepthInv K s → DepthInv K (step E s)
  | .call 0 _ _ _, h => h.1
  | .call (k + 1) _ _ st, h => by
    obtain ⟨h₁, h₂⟩ := h
    refine ⟨⟨?_, h₁⟩, ?_⟩ <;> simp only [List.length_cons] <;> omega
  | .ret _ [], _ => trivial
  | .ret true (⟨_, _, _, _, .left⟩ :: _), h => ⟨⟨h.1, h.2⟩, h.1⟩
  | .ret false (⟨_, _, _, _, .left⟩ :: _), h => depthInv_advance h.1 h.2
  | .ret true (⟨_, _, _, _, .right⟩ :: _), h => h.2
  | .ret false (⟨_, _, _, _, .right⟩ :: _), h => depthInv_advance h.1 h.2
  | .done _, _ => trivial

omit [NeZero N] in
theorem stackOK_length {K : ℕ} : ∀ {st : List (Frame N)}, StackOK K st → st.length ≤ K
  | [], _ => Nat.zero_le _
  | _ :: _, h => by simp only [List.length_cons]; have := h.1; omega

theorem reachable_depthInv (K : ℕ) (a b : Fin N) {s : State N}
    (hs : RTG (StepRel E) (init K a b) s) : DepthInv K s := by
  induction hs with
  | refl => exact ⟨trivial, by simp⟩
  | tail _ hst ih => exact hst ▸ depthInv_step E ih

/-- **Stack depth.** Every state reachable from `init K a b` has at most `K` frames. -/
theorem reachable_stack_le (K : ℕ) (a b : Fin N) {s : State N}
    (hs : RTG (StepRel E) (init K a b) s) : s.stack.length ≤ K := by
  have h := reachable_depthInv E K a b hs
  cases s with
  | call _ _ _ st => exact stackOK_length h.1
  | ret _ st => exact stackOK_length h
  | done _ => exact Nat.zero_le _

end Savitch.Gen
