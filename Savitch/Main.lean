import Savitch.Space.StackMachine
import Savitch.Machine.NTM

/-!
# Savitch's theorem, relative to the step-relation oracle

Phase 4a of the Savitch formalization (see `PLAN.md`).

We connect the three earlier layers:

1. **Sink reduction.** Many accepting configurations are turned into a single
   target by adding one extra vertex (one extra bit, `w ↦ w + 1`).
2. **The oracle.** For an NTM `M` and input `x`, `M.oracle hM x` is the adjacency
   test of `M`'s configuration graph on `x` (plus the sink).
3. **Main result.** `savitch_relative`: for every `L ∈ NSPACE s` with
   `s n ≥ log n`, there is an NTM `M` for `L` and a constant `K` such that the
   deterministic Phase 2 machine, querying `M`'s own step oracle, decides
   `x ∈ L` and never holds more than `K * (s |x| + 1)²` bits.

**What is not yet accounted for:** the oracle's own working space, and how the
deterministic machine finds the width `w` (space constructibility). Both are
Phase 4b.
-/

namespace Savitch

/-! ### Reducing "some accepting vertex" to a single sink -/

section Sink

variable {w : ℕ}

def liftV (u : Fin (2 ^ w)) : Fin (2 ^ (w + 1)) :=
  ⟨u.val, by have := u.isLt; rw [Nat.pow_succ]; omega⟩

def sinkV : Fin (2 ^ (w + 1)) :=
  ⟨2 ^ w, by have := Nat.two_pow_pos w; rw [Nat.pow_succ]; omega⟩

/-- `E` on the low half, plus an edge from each accepting vertex to `sinkV`. -/
def sinkGraph (E : Fin (2 ^ w) → Fin (2 ^ w) → Bool) (Acc : Fin (2 ^ w) → Bool)
    (u v : Fin (2 ^ (w + 1))) : Bool :=
  if h : u.val < 2 ^ w then
    if h' : v.val < 2 ^ w then E ⟨u.val, h⟩ ⟨v.val, h'⟩
    else decide (v.val = 2 ^ w) && Acc ⟨u.val, h⟩
  else false

theorem reach_sink_iff (E : Fin (2 ^ w) → Fin (2 ^ w) → Bool) (Acc : Fin (2 ^ w) → Bool)
    (u : Fin (2 ^ w)) :
    Relation.ReflTransGen (Space.Rel (sinkGraph E Acc)) (liftV u) sinkV ↔
      ∃ v, Acc v = true ∧ Relation.ReflTransGen (Space.Rel E) u v := by
  constructor
  · intro h
    have key : ∀ t, Relation.ReflTransGen (Space.Rel (sinkGraph E Acc)) (liftV u) t →
        (∀ ht : t.val < 2 ^ w, Relation.ReflTransGen (Space.Rel E) u ⟨t.val, ht⟩) ∧
        (t.val = 2 ^ w → ∃ v, Acc v = true ∧ Relation.ReflTransGen (Space.Rel E) u v) := by
      intro t ht
      induction ht with
      | refl =>
        refine ⟨fun _ => .refl, fun h => ?_⟩
        have hu := u.isLt
        change u.val = 2 ^ w at h
        omega
      | @tail a b _ hab ih =>
        obtain ⟨ih₁, _⟩ := ih
        simp only [Space.Rel, sinkGraph] at hab
        by_cases ha : a.val < 2 ^ w
        · by_cases hb : b.val < 2 ^ w
          · simp only [ha, hb, ↓reduceDIte] at hab
            exact ⟨fun _ => (ih₁ ha).tail hab, fun h => absurd h (by omega)⟩
          · simp only [ha, hb, ↓reduceDIte, Bool.and_eq_true, decide_eq_true_eq] at hab
            exact ⟨fun h => absurd h hb, fun _ => ⟨_, hab.2, ih₁ ha⟩⟩
        · simp [ha] at hab
    exact (key _ h).2 rfl
  · rintro ⟨v, hv, hp⟩
    have h₁ : Relation.ReflTransGen (Space.Rel (sinkGraph E Acc)) (liftV u) (liftV v) :=
      hp.lift liftV (fun a b hab => by simpa [Space.Rel, sinkGraph, liftV] using hab)
    refine h₁.tail ?_
    simp [Space.Rel, sinkGraph, liftV, sinkV, hv]

end Sink

/-! ### The configuration-graph oracle of an NTM -/

namespace Machine.NTM

variable {Λ Γ : Type} [Fintype Λ] [Fintype Γ] (M : NTM Λ Γ) {s : ℕ → ℕ}

/-- The exact number of bits needed to name a bounded configuration on `x`. -/
noncomputable def cw (s : ℕ → ℕ) (x : List Bool) : ℕ :=
  Nat.clog 2 (Fintype.card (BCfg Λ Γ x.length (s x.length)))

theorem card_le_cw (s : ℕ → ℕ) (x : List Bool) :
    Fintype.card (BCfg Λ Γ x.length (s x.length)) ≤ 2 ^ cw (Λ := Λ) (Γ := Γ) s x :=
  Nat.le_pow_clog (by decide) _

theorem cw_le {x : List Bool} (hlog : Nat.log 2 x.length ≤ s x.length)
    (hs : 1 ≤ s x.length) : cw (Λ := Λ) (Γ := Γ) s x ≤ C Λ Γ * s x.length :=
  (Nat.clog_le_iff_le_pow (by decide)).2 (card_BCfg_le hlog hs)

noncomputable def enc (s : ℕ → ℕ) (x : List Bool) :
    BCfg Λ Γ x.length (s x.length) ↪ Fin (2 ^ cw (Λ := Λ) (Γ := Γ) s x) :=
  encode (card_le_cw s x)

open Classical in
/-- Adjacency in `M`'s configuration graph on `x`. -/
noncomputable def edgeOracle (x : List Bool) :
    Fin (2 ^ cw (Λ := Λ) (Γ := Γ) s x) → Fin (2 ^ cw (Λ := Λ) (Γ := Γ) s x) → Bool :=
  fun u v => decide (MapRel (enc s x) (M.BStep x) u v)

open Classical in
/-- Is a vertex an accepting configuration? -/
noncomputable def accOracle (x : List Bool) : Fin (2 ^ cw (Λ := Λ) (Γ := Γ) s x) → Bool :=
  fun v => decide (∃ b, enc s x b = v ∧ b.1 = M.accept)

/-- The oracle queried by the deterministic machine: `M`'s step relation on `x`,
plus edges from accepting configurations to a sink. -/
noncomputable def oracle (s : ℕ → ℕ) (x : List Bool) :
    Fin (2 ^ (cw (Λ := Λ) (Γ := Γ) s x + 1)) → Fin (2 ^ (cw (Λ := Λ) (Γ := Γ) s x + 1)) → Bool :=
  sinkGraph (M.edgeOracle x) (M.accOracle x)

/-- The deterministic machine's start state: reach the sink from the encoded
initial configuration, with recursion depth = vertex width. -/
noncomputable def startState (hM : M.SpaceBounded s) (x : List Bool) :
    Space.State (cw (Λ := Λ) (Γ := Γ) s x + 1) :=
  Space.init (cw (Λ := Λ) (Γ := Γ) s x + 1) (liftV (enc s x (M.initB (hM.pos x)))) sinkV

theorem reach_oracle_iff (hM : M.SpaceBounded s) (x : List Bool) :
    Relation.ReflTransGen (Space.Rel (M.oracle s x))
      (liftV (enc s x (M.initB (hM.pos x)))) sinkV ↔ M.Accepts x := by
  have hrel : Space.Rel (M.edgeOracle x) = MapRel (enc s x) (M.BStep x) := by
    funext u v
    simp [Space.Rel, edgeOracle]
  rw [oracle, reach_sink_iff, hrel]
  simp only [accOracle, decide_eq_true_eq]
  exact (M.accepts_iff_cfgGraph hM x (card_le_cw s x)).symm

/-- **The Savitch machine decides acceptance** of a space-bounded NTM, using at
most `(w + 1)(4w + 1)` bits where `w = cw + 1`. -/
theorem savitch_decides (hM : M.SpaceBounded s) (x : List Bool) :
    (∃ r, Relation.ReflTransGen (Space.StepRel (M.oracle s x)) (M.startState hM x) (.done r) ∧
      (r = true ↔ M.Accepts x)) ∧
    ∀ st, Relation.ReflTransGen (Space.StepRel (M.oracle s x)) (M.startState hM x) st →
      Space.space st ≤
        (cw (Λ := Λ) (Γ := Γ) s x + 1 + 1) * (4 * (cw (Λ := Λ) (Γ := Γ) s x + 1) + 1) := by
  obtain ⟨⟨r, hr, hiff⟩, hspace⟩ :=
    Space.savitch_machine (M.oracle s x) (liftV (enc s x (M.initB (hM.pos x)))) sinkV
  exact ⟨⟨r, hr, hiff.trans (M.reach_oracle_iff hM x)⟩, hspace⟩

end Machine.NTM

/-! ### The language-level statement -/

open Machine

/-- **Savitch's theorem, relative to the step oracle.**

If `log n ≤ s n` and `L ∈ NSPACE s`, then some NTM `M` for `L` and some constant
`K` satisfy: on every input `x`, the deterministic Phase 2 machine, querying
`M`'s own configuration-graph oracle, halts with the answer to `x ∈ L`, and
every state it passes through uses at most `K * (s |x| + 1)²` bits. -/
theorem savitch_relative {s : ℕ → ℕ} (hlog : ∀ n, Nat.log 2 n ≤ s n)
    {L : Set (List Bool)} (hL : L ∈ NSPACE s) :
    ∃ (Λ Γ : Type) (_ : Fintype Λ) (_ : Fintype Γ) (M : NTM Λ Γ) (c K : ℕ)
      (hM : M.SpaceBounded (fun n => c * (s n + 1))),
      ∀ x : List Bool,
        (∃ r, Relation.ReflTransGen (Space.StepRel (M.oracle _ x)) (M.startState hM x)
            (.done r) ∧ (r = true ↔ x ∈ L)) ∧
        ∀ st, Relation.ReflTransGen (Space.StepRel (M.oracle _ x)) (M.startState hM x) st →
          Space.space st ≤ K * (s x.length + 1) ^ 2 := by
  obtain ⟨Λ, Γ, iΛ, iΓ, M, c, hM, hLM⟩ := hL
  have hc : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · have := hM.pos []
      simp at this
    · exact hc
  refine ⟨Λ, Γ, iΛ, iΓ, M, c, (NTM.C Λ Γ * c + 2) * (4 * (NTM.C Λ Γ * c) + 5), hM, fun x => ?_⟩
  obtain ⟨⟨r, hr, hiff⟩, hspace⟩ := M.savitch_decides hM x
  refine ⟨⟨r, hr, hiff.trans (hLM x).symm⟩, fun st hst => (hspace st hst).trans ?_⟩
  -- arithmetic: `cw ≤ C * c * (s + 1)` turns `(w+1)(4w+1)` into `K * (s+1)²`
  have hlog' : Nat.log 2 x.length ≤ c * (s x.length + 1) :=
    (hlog _).trans ((Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ hc))
  have hw := NTM.cw_le (Λ := Λ) (Γ := Γ) (s := fun n => c * (s n + 1)) hlog' (hM.pos x)
  set cwx := NTM.cw (Λ := Λ) (Γ := Γ) (fun n => c * (s n + 1)) x
  set T := s x.length + 1
  set D := NTM.C Λ Γ * c
  have hw' : cwx ≤ D * T := by
    have e : NTM.C Λ Γ * (c * T) = D * T := by simp only [D]; ring
    exact hw.trans_eq e
  have hT : 1 ≤ T := by omega
  have h₁ : cwx + 1 + 1 ≤ (D + 2) * T := by
    have e : (D + 2) * T = D * T + 2 * T := by ring
    omega
  have h₂ : 4 * (cwx + 1) + 1 ≤ (4 * D + 5) * T := by
    have e : (4 * D + 5) * T = 4 * (D * T) + 5 * T := by ring
    omega
  calc (cwx + 1 + 1) * (4 * (cwx + 1) + 1)
      ≤ ((D + 2) * T) * ((4 * D + 5) * T) := Nat.mul_le_mul h₁ h₂
    _ = (D + 2) * (4 * D + 5) * T ^ 2 := by ring

end Savitch
