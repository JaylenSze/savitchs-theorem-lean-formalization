import Savitch.Reach.Recursive
import Mathlib.Data.Nat.Size

/-!
# Savitch's procedure as an explicit, space-accounted stack machine

Phase 2 of the Savitch formalization (see `PLAN.md`).

Lean's own recursion has no space measure, so we implement the midpoint
recursion of `Savitch.savitch` as a deterministic small-step machine with an
**explicit stack of frames**, and measure space as a number of bits.

* Vertices are `Fin (2 ^ w)`: each vertex costs `w` bits.
* The graph is a deterministic edge oracle `E : Fin (2^w) → Fin (2^w) → Bool`.
  (The oracle's own working space is accounted for in Phase 4.)
* A frame for a call at level `k + 1` stores `k`, the endpoints `a b`, the
  current midpoint candidate `c` and a one-bit phase: `3 * w + size k + 1` bits.

Main results:
* `run_correct`: the machine started at `init K a b` halts in `done (savitch _ K a b)`.
* `run_space`: every state reachable from `init K a b` uses at most
  `(K + 1) * (3 * w + size K + 1)` bits.
* `savitch_machine`: with `K = w`, the machine decides reachability in space
  `(w + 1) * (4 * w + 1) = O(w²)`.
-/

namespace Savitch.Space

/-- Which recursive call of the current midpoint `c` we are waiting on. -/
inductive Phase
  | left   -- waiting on `savitch k a c`
  | right  -- waiting on `savitch k c b`
  deriving DecidableEq

/-- A suspended call at level `k + 1` that is iterating over midpoints `c`. -/
structure Frame (w : ℕ) where
  k : ℕ
  a : Fin (2 ^ w)
  b : Fin (2 ^ w)
  c : Fin (2 ^ w)
  phase : Phase

inductive State (w : ℕ) where
  /-- About to evaluate `savitch k a b`, then return to `stack`. -/
  | call (k : ℕ) (a b : Fin (2 ^ w)) (stack : List (Frame w))
  /-- Returning the Boolean `r` to the top frame of `stack`. -/
  | ret (r : Bool) (stack : List (Frame w))
  /-- Halted with answer `r`. -/
  | done (r : Bool)

variable {w : ℕ}

/-! ### Space measure (in bits) -/

def frameCost (f : Frame w) : ℕ := 3 * w + Nat.size f.k + 1

def stackCost : List (Frame w) → ℕ
  | [] => 0
  | f :: st => frameCost f + stackCost st

def space : State w → ℕ
  | .call k _ _ st => 2 * w + Nat.size k + stackCost st
  | .ret _ st => 1 + stackCost st
  | .done _ => 1

/-- The per-level space budget for a run of depth `K`. -/
def levelCost (w K : ℕ) : ℕ := 3 * w + Nat.size K + 1

/-! ### The machine -/

def zero : Fin (2 ^ w) := ⟨0, Nat.two_pow_pos w⟩

variable (E : Fin (2 ^ w) → Fin (2 ^ w) → Bool)

/-- Move on to the next midpoint candidate after `c`, or fail if there is none. -/
def advance (k : ℕ) (a b c : Fin (2 ^ w)) (st : List (Frame w)) : State w :=
  if h : c.val + 1 < 2 ^ w then
    .call k a ⟨c.val + 1, h⟩ (⟨k, a, b, ⟨c.val + 1, h⟩, .left⟩ :: st)
  else
    .ret false st

/-- One deterministic step. -/
def step : State w → State w
  | .call 0 a b st => .ret (decide (a = b) || E a b) st
  | .call (k + 1) a b st => .call k a zero (⟨k, a, b, zero, .left⟩ :: st)
  | .ret r [] => .done r
  | .ret true (⟨k, a, b, c, .left⟩ :: st) => .call k c b (⟨k, a, b, c, .right⟩ :: st)
  | .ret false (⟨k, a, b, c, .left⟩ :: st) => advance k a b c st
  | .ret true (⟨_, _, _, _, .right⟩ :: st) => .ret true st
  | .ret false (⟨k, a, b, c, .right⟩ :: st) => advance k a b c st
  | .done r => .done r

def init (K : ℕ) (a b : Fin (2 ^ w)) : State w := .call K a b []

/-- The step relation, for use with `Relation.ReflTransGen`. -/
def StepRel (s t : State w) : Prop := step E s = t

/-! ### Space-bounded runs -/

/-- `Bounded E B s t`: the machine goes from `s` to `t`, and every state on the
way (both endpoints included) uses at most `B` bits. -/
inductive Bounded (B : ℕ) : State w → State w → Prop
  | refl {s} : space s ≤ B → Bounded B s s
  | head {s t} : space s ≤ B → Bounded B (step E s) t → Bounded B s t

namespace Bounded

variable {E} {B B' : ℕ} {s t u : State w}

theorem mono (h : Bounded E B s t) (hB : B ≤ B') : Bounded E B' s t := by
  induction h with
  | refl hs => exact .refl (hs.trans hB)
  | head hs _ ih => exact .head (hs.trans hB) ih

theorem trans (h₁ : Bounded E B s t) (h₂ : Bounded E B t u) : Bounded E B s u := by
  revert h₂
  induction h₁ with
  | refl _ => exact id
  | head hs _ ih => exact fun h₂ => .head hs (ih h₂)

theorem target_le (h : Bounded E B s t) : space t ≤ B := by
  induction h with
  | refl hs => exact hs
  | head _ _ ih => exact ih

theorem toReflTransGen (h : Bounded E B s t) : Relation.ReflTransGen (StepRel E) s t := by
  induction h with
  | refl _ => exact .refl
  | head _ _ ih => exact ih.head rfl

theorem fixed_reach (hfix : step E s = s) {u : State w}
    (hu : Relation.ReflTransGen (StepRel E) s u) : u = s := by
  induction hu with
  | refl => rfl
  | tail _ hyz ih => rw [← hyz, ih, hfix]

/-- Determinism: if a bounded run ends in a fixed point, then *every* state
reachable from its start is within the bound. -/
theorem reachable (h : Bounded E B s t) :
    step E t = t → ∀ u, Relation.ReflTransGen (StepRel E) s u → space u ≤ B := by
  induction h with
  | refl hs =>
    intro hfix u hu
    rw [fixed_reach hfix hu]
    exact hs
  | head hs _ ih =>
    intro hfix u hu
    rcases Relation.ReflTransGen.cases_head hu with rfl | ⟨v, hv, hvu⟩
    · exact hs
    · exact ih hfix u (hv ▸ hvu)

end Bounded

/-! ### Correctness and space of a call -/

/-- The edge relation of the oracle, as a `Prop`. -/
def Rel (s t : Fin (2 ^ w)) : Prop := E s t = true

instance : DecidableRel (Rel E) := fun s t => inferInstanceAs (Decidable (E s t = true))

/-- Some midpoint `c' ≥ c` works for `savitch k a b` at level `k + 1`. -/
def Found (k : ℕ) (a b c : Fin (2 ^ w)) : Prop :=
  ∃ c', c ≤ c' ∧ savitch (Rel E) k a c' = true ∧ savitch (Rel E) k c' b = true

instance (k : ℕ) (a b c : Fin (2 ^ w)) : Decidable (Found E k a b c) := by
  unfold Found; infer_instance

theorem zero_le' (c : Fin (2 ^ w)) : (zero : Fin (2 ^ w)) ≤ c :=
  Fin.le_def.2 (Nat.zero_le _)

theorem found_zero (k : ℕ) (a b : Fin (2 ^ w)) :
    decide (Found E k a b zero) = savitch (Rel E) (k + 1) a b := by
  simp [Found, savitch, zero_le']

theorem found_iff_next {k : ℕ} {a b c : Fin (2 ^ w)} (h : c.val + 1 < 2 ^ w)
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

theorem not_found_last {k : ℕ} {a b c : Fin (2 ^ w)} (h : ¬ c.val + 1 < 2 ^ w)
    (hfail : ¬ (savitch (Rel E) k a c = true ∧ savitch (Rel E) k c b = true)) :
    ¬ Found E k a b c := by
  rintro ⟨c', hc', h₁, h₂⟩
  rw [Fin.le_def] at hc'
  have : c' = c := Fin.ext (by have := c'.isLt; omega)
  exact hfail (this ▸ ⟨h₁, h₂⟩)

theorem frameCost_le {K : ℕ} {f : Frame w} (hk : f.k ≤ K) : frameCost f ≤ levelCost w K := by
  have := Nat.size_le_size hk
  simp only [frameCost, levelCost]
  omega

theorem levelCost_pos (K : ℕ) : 1 ≤ levelCost w K := by
  simp only [levelCost]
  omega

/-- The midpoint loop of a level-`k+1` call, starting from candidate `c`. -/
theorem loop {K k : ℕ} (hkK : k ≤ K) {a b : Fin (2 ^ w)} {st : List (Frame w)}
    (hk : ∀ a b st, Bounded E (stackCost st + (k + 1) * levelCost w K)
      (.call k a b st) (.ret (savitch (Rel E) k a b) st)) :
    ∀ m (c : Fin (2 ^ w)), 2 ^ w - c.val = m →
      Bounded E (stackCost st + (k + 1 + 1) * levelCost w K)
        (.call k a c (⟨k, a, b, c, .left⟩ :: st)) (.ret (decide (Found E k a b c)) st) := by
  have hmul : (k + 1 + 1) * levelCost w K = (k + 1) * levelCost w K + levelCost w K :=
    Nat.succ_mul _ _
  have hpos := levelCost_pos (w := w) K
  -- pushing any level-`k` frame keeps the inner run within the outer budget
  have hpush : ∀ f : Frame w, f.k = k →
      stackCost (f :: st) + (k + 1) * levelCost w K ≤
        stackCost st + (k + 1 + 1) * levelCost w K := by
    intro f hf
    have := frameCost_le (K := K) (f := f) (hf ▸ hkK)
    simp only [stackCost]
    omega
  -- what happens after the current candidate `c` has failed
  have hadv : ∀ m (c : Fin (2 ^ w)), 2 ^ w - c.val = m + 1 →
      (∀ c' : Fin (2 ^ w), 2 ^ w - c'.val = m →
        Bounded E (stackCost st + (k + 1 + 1) * levelCost w K)
          (.call k a c' (⟨k, a, b, c', .left⟩ :: st)) (.ret (decide (Found E k a b c')) st)) →
      ¬ (savitch (Rel E) k a c = true ∧ savitch (Rel E) k c b = true) →
      Bounded E (stackCost st + (k + 1 + 1) * levelCost w K)
        (advance k a b c st) (.ret (decide (Found E k a b c)) st) := by
    intro m c hm ih hfail
    by_cases hlt : c.val + 1 < 2 ^ w
    · simp only [advance, hlt, ↓reduceDIte]
      rw [decide_eq_decide.2 (found_iff_next E hlt hfail)]
      exact ih _ (by simp only; omega)
    · simp only [advance, hlt, ↓reduceDIte]
      rw [decide_eq_false (not_found_last E hlt hfail)]
      refine .refl ?_
      simp only [space]
      omega
  intro m
  induction m with
  | zero =>
    intro c hc
    have := c.isLt
    omega
  | succ m ih =>
    intro c hc
    have h₁ := (hk a c (⟨k, a, b, c, .left⟩ :: st)).mono (hpush _ rfl)
    refine h₁.trans ?_
    cases hac : savitch (Rel E) k a c
    · -- left half failed: next candidate
      rw [hac] at h₁
      exact .head h₁.target_le (hadv m c hc ih (by simp [hac]))
    · rw [hac] at h₁
      have h₂ := (hk c b (⟨k, a, b, c, .right⟩ :: st)).mono (hpush _ rfl)
      refine .head h₁.target_le (h₂.trans ?_)
      cases hcb : savitch (Rel E) k c b
      · -- right half failed: next candidate
        rw [hcb] at h₂
        exact .head h₂.target_le (hadv m c hc ih (by simp [hcb]))
      · -- both halves succeeded: `c` is a midpoint
        rw [hcb] at h₂
        have hfound : decide (Found E k a b c) = true :=
          decide_eq_true ⟨c, le_refl c, hac, hcb⟩
        rw [hfound]
        refine .head h₂.target_le (.refl ?_)
        show space (State.ret true st) ≤ _
        simp only [space]
        omega

/-- **Key lemma.** Evaluating `savitch k a b` on top of `st` returns the right
answer, using at most `(k + 1) * levelCost w K` bits beyond `st`. -/
theorem call_bounded {K : ℕ} :
    ∀ k ≤ K, ∀ a b st, Bounded E (stackCost st + (k + 1) * levelCost w K)
      (.call k a b st) (.ret (savitch (Rel E) k a b) st) := by
  have hsize : ∀ k ≤ K, 2 * w + Nat.size k ≤ levelCost w K := by
    intro k hk
    have := Nat.size_le_size hk
    simp only [levelCost]
    omega
  intro k
  induction k with
  | zero =>
    intro _ a b st
    have hs := hsize 0 (Nat.zero_le _)
    have hsav : savitch (Rel E) 0 a b = (decide (a = b) || E a b) := by
      show (decide (a = b) || decide (Rel E a b)) = _
      cases h : E a b <;> simp [Rel, h]
    rw [hsav, Nat.zero_add, Nat.one_mul]
    refine .head ?_ (.refl ?_)
    · simp only [space]; omega
    · show space (State.ret _ st) ≤ _
      have := levelCost_pos (w := w) K
      simp only [space]
      omega
  | succ k ih =>
    intro hk a b st
    have hs := hsize (k + 1) hk
    have hmul : (k + 1 + 1) * levelCost w K = (k + 1) * levelCost w K + levelCost w K :=
      Nat.succ_mul _ _
    rw [← found_zero]
    refine .head ?_ (loop E (by omega) (ih (by omega)) _ zero rfl)
    simp only [space]
    omega

/-! ### Whole runs -/

theorem run_bounded (K : ℕ) (a b : Fin (2 ^ w)) :
    Bounded E ((K + 1) * levelCost w K) (init K a b) (.done (savitch (Rel E) K a b)) := by
  have h := call_bounded E K le_rfl a b []
  simp only [stackCost, Nat.zero_add] at h
  have hpos : 1 ≤ (K + 1) * levelCost w K :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by have := levelCost_pos (w := w) K; omega))
  refine h.trans (.head ?_ (.refl ?_))
  · simp only [space, stackCost]; omega
  · exact hpos

/-- **Correctness.** The machine halts with the answer of `savitch`. -/
theorem run_correct (K : ℕ) (a b : Fin (2 ^ w)) :
    Relation.ReflTransGen (StepRel E) (init K a b) (.done (savitch (Rel E) K a b)) :=
  (run_bounded E K a b).toReflTransGen

/-- **Space bound.** Every reachable state uses at most `(K+1) * (3w + size K + 1)` bits. -/
theorem run_space (K : ℕ) (a b : Fin (2 ^ w)) :
    ∀ s, Relation.ReflTransGen (StepRel E) (init K a b) s →
      space s ≤ (K + 1) * levelCost w K :=
  (run_bounded E K a b).reachable rfl

/-- **Phase 2 headline.** With depth `K = w` the machine decides reachability in
the graph `E` on `2 ^ w` vertices, and never uses more than
`(w + 1) * (4 * w + 1)` bits, i.e. `O(w²)`. -/
theorem savitch_machine (a b : Fin (2 ^ w)) :
    (∃ r, Relation.ReflTransGen (StepRel E) (init w a b) (.done r) ∧
      (r = true ↔ Relation.ReflTransGen (Rel E) a b)) ∧
    ∀ s, Relation.ReflTransGen (StepRel E) (init w a b) s →
      space s ≤ (w + 1) * (4 * w + 1) := by
  refine ⟨⟨_, run_correct E w a b, ?_⟩, fun s hs => ?_⟩
  · have hdepth : Nat.clog 2 (Fintype.card (Fin (2 ^ w))) = w := by
      rw [Fintype.card_fin, Nat.clog_pow _ _ (by decide)]
    have := savitch_correct (R := Rel E) a b
    rwa [hdepth] at this
  · refine (run_space E w a b s hs).trans (Nat.mul_le_mul_left _ ?_)
    have : Nat.size w ≤ w := Nat.size_le.2 Nat.lt_two_pow_self
    simp only [levelCost]
    omega

/-! ### Stack depth: at most `K` frames -/

/-- Frames are stacked with consecutive levels: the top frame of a stack of
length `ℓ` stores level `K - ℓ`. -/
def StackOK (K : ℕ) : List (Frame w) → Prop
  | [] => True
  | f :: st => f.k + (st.length + 1) = K ∧ StackOK K st

/-- The depth invariant of a run started at `init K a b`. -/
def DepthInv (K : ℕ) : State w → Prop
  | .call k _ _ st => StackOK K st ∧ k + st.length = K
  | .ret _ st => StackOK K st
  | .done _ => True

def State.stack : State w → List (Frame w)
  | .call _ _ _ st => st
  | .ret _ st => st
  | .done _ => []

theorem depthInv_advance {K k : ℕ} {a b c : Fin (2 ^ w)} {st : List (Frame w)}
    (h : k + (st.length + 1) = K) (hst : StackOK K st) : DepthInv K (advance k a b c st) := by
  unfold advance
  split_ifs
  · exact ⟨⟨h, hst⟩, h⟩
  · exact hst

theorem depthInv_step {K : ℕ} : ∀ {s : State w}, DepthInv K s → DepthInv K (step E s)
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

theorem stackOK_length {K : ℕ} : ∀ {st : List (Frame w)}, StackOK K st → st.length ≤ K
  | [], _ => Nat.zero_le _
  | _ :: _, h => by simp only [List.length_cons]; have := h.1; omega

theorem depthInv_stack_le {K : ℕ} {s : State w} (h : DepthInv K s) : s.stack.length ≤ K := by
  cases s with
  | call _ _ _ st => exact stackOK_length h.1
  | ret _ st => exact stackOK_length h
  | done _ => exact Nat.zero_le _

/-- **Stack depth.** Every state reachable from `init K a b` has at most `K` frames,
and every frame on it stores a level `< K`. -/
theorem reachable_depthInv (K : ℕ) (a b : Fin (2 ^ w)) {s : State w}
    (hs : Relation.ReflTransGen (StepRel E) (init K a b) s) : DepthInv K s := by
  induction hs with
  | refl => exact ⟨trivial, by simp⟩
  | tail _ hst ih => exact hst ▸ depthInv_step E ih

theorem reachable_stack_le (K : ℕ) (a b : Fin (2 ^ w)) {s : State w}
    (hs : Relation.ReflTransGen (StepRel E) (init K a b) s) : s.stack.length ≤ K :=
  depthInv_stack_le (reachable_depthInv E K a b hs)

end Savitch.Space
