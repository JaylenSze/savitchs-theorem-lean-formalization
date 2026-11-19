import Savitch.Machine.NTM

/-!
# Deterministic multi-tape Turing machines and `DSPACE`

Phase 4b of the Savitch formalization (see `PLAN.md`).

A `DTM k Λ Γ` has a read-only binary input tape between two end markers (the
same convention as the NTMs of Phase 3: `inputSym`, `moveIn`) and `k` work
tapes over `Γ`. In each step it reads the input symbol and all `k` work symbols,
then writes all `k` work cells, moves every head and changes state. States
where `halt q = some b` are halting with answer `b`, and the machine stays put
there.

**Space** is measured by the work-head positions: `Tapes.Within B T` says that
every work head is below `B`. A machine whose heads always stay below `B`
touches at most `k * B` work cells, and `k` is a constant of the machine.
-/

namespace Savitch.TM

open Machine (Dir inputSym moveIn moveWork)

/-- Head positions and contents of the input head and `k` work tapes. -/
@[ext]
structure Tapes (k : ℕ) (Γ : Type) where
  ih : ℕ
  hd : Fin k → ℕ
  tp : Fin k → ℕ → Γ

namespace Tapes

variable {k : ℕ} {Γ : Type}

/-- The symbol under the head of work tape `t`. -/
def read (T : Tapes k Γ) (t : Fin k) : Γ := T.tp t (T.hd t)

/-- All tapes blank, all heads at position `0`. -/
def blank (g : Γ) : Tapes k Γ := ⟨0, fun _ => 0, fun _ _ => g⟩

/-- Every work head is below `B`. -/
def Within (B : ℕ) (T : Tapes k Γ) : Prop := ∀ i, T.hd i < B

end Tapes

/-- A deterministic TM with a read-only input tape and `k` work tapes. -/
structure DTM (k : ℕ) (Λ Γ : Type) where
  blank : Γ
  start : Λ
  /-- `some b`: halting state with answer `b`. -/
  halt : Λ → Option Bool
  /-- `(new state, symbols written on each work tape, input move, work moves)`. -/
  δ : Λ → Option Bool → (Fin k → Γ) → Λ × (Fin k → Γ) × Dir × (Fin k → Dir)

structure DCfg (k : ℕ) (Λ Γ : Type) where
  q : Λ
  T : Tapes k Γ

namespace DTM

variable {k : ℕ} {Λ Γ : Type} (M : DTM k Λ Γ) (x : List Bool)

/-- One deterministic step on input `x`. Halting configurations are fixed points. -/
def step (c : DCfg k Λ Γ) : DCfg k Λ Γ :=
  match M.halt c.q with
  | some _ => c
  | none =>
    let r := M.δ c.q (inputSym x c.T.ih) (fun i => c.T.read i)
    ⟨r.1, ⟨moveIn x.length c.T.ih r.2.2.1,
           fun i => moveWork (c.T.hd i) (r.2.2.2 i),
           fun i => Function.update (c.T.tp i) (c.T.hd i) (r.2.1 i)⟩⟩

def init : DCfg k Λ Γ := ⟨M.start, Tapes.blank M.blank⟩

def StepRel (c d : DCfg k Λ Γ) : Prop := M.step x c = d

/-- On input `x` the machine halts with answer `b`. -/
def Decides (b : Bool) : Prop :=
  ∃ d, Relation.ReflTransGen (M.StepRel x) M.init d ∧ M.halt d.q = some b

/-- On every input `x`, every reachable configuration keeps all work heads below `f |x|`. -/
def SpaceBounded (f : ℕ → ℕ) : Prop :=
  ∀ x d, Relation.ReflTransGen (M.StepRel x) M.init d → d.T.Within (f x.length)

end DTM

/-- `DSPACE f`: languages decided by a deterministic multi-tape TM in space `O(f)`.
The machine must halt on every input, with the right answer. -/
def DSPACE (f : ℕ → ℕ) : Set (Set (List Bool)) :=
  { L | ∃ (k : ℕ) (Λ Γ : Type) (_ : Fintype Λ) (_ : Fintype Γ) (M : DTM k Λ Γ) (c : ℕ),
      M.SpaceBounded (fun n => c * (f n + 1)) ∧
      ∀ x, ∃ b, M.Decides x b ∧ (b = true ↔ x ∈ L) }

end Savitch.TM
