# Savitch's Theorem in Lean 4

> [!WARNING]
> **This repository is AI-generated.** All Lean code, proofs, definitions,
> documentation and the plan in `PLAN.md`, including this README, were written
> by AI models (Anthropic's Claude and Google's Gemini). No human wrote or
> reviewed the proofs line by line.
>
> The Lean kernel *does* check every proof. `lake build` succeeds, there is no
> `sorry`, and the main theorems depend only on Lean's standard axioms
> (`propext`, `Classical.choice`, `Quot.sound`). That still only guarantees the
> theorems *as stated*. Whether the definitions (`NSPACE`, `DSPACE`, the machine
> models, the space measure) faithfully capture the textbook notions is a
> modelling question that a human should review.

A complete formalization of **Savitch's theorem** in Lean 4:

```lean
theorem savitch_theorem {s : ℕ → ℕ} (hlog : ∀ n, Nat.log 2 n ≤ s n) :
    NSPACE s ⊆ DSPACE (fun n => s n ^ 2)
```

## Status

| Phase | Result | File |
|---|---|---|
| 1. Abstract reachability | `savitch_correct`: the recursive midpoint procedure, at depth `⌈log₂ \|V\|⌉`, decides reachability in any finite graph | `Savitch/Reach/` |
| 2. Space-accounted machine | `Space.savitch_machine`: an explicit stack machine decides reachability on `2^w` vertices using at most `(w+1)(4w+1)` bits; `Gen.run_correct` / `Gen.reachable_stack_le` over any `Fin N` | `Savitch/Space/` |
| 3. NTMs and `NSPACE` | `NTM.accepts_iff_cfgGraph_Cs`, total record encoding (`Encode.lean`), generated-edge graph (`Next.lean`), width-closure (`Width.lean`) | `Savitch/Machine/` |
| 4a. Main theorem (oracle-relative) | `Savitch.savitch_relative` | `Savitch/Main.lean` |
| 4b. Full theorem via Turing machines | ✅ **Complete (`Savitch.savitch_theorem`)**: `NSPACE s ⊆ DSPACE (fun n => s n ^ 2)` over deterministic multi-tape Turing machines (`DTM`), with no space-constructibility assumption | `Savitch/TM/`, `Savitch/Edge/`, `Savitch/Sav/`, `Savitch/Outer/`, `Savitch/Final.lean` |

### What is proved

`Savitch.savitch_theorem` (`Savitch/Final.lean`): suppose `Nat.log 2 n ≤ s n` for all `n`. Then `NSPACE s ⊆ DSPACE (fun n => s n ^ 2)`, where:
- **`NSPACE s`** (`Savitch/Machine/NTM.lean`) is the class of languages accepted by a nondeterministic Turing machine with a read-only binary input tape (with end markers) and a one-way infinite work tape whose work head stays below `c * (s |x| + 1)` on every reachable configuration.
- **`DSPACE f`** (`Savitch/TM/DTM.lean`) is the class of languages decided by a deterministic multi-tape Turing machine (`DTM k Λ Γ`, with `k = 32` work tapes for the Savitch machine) that halts on every input `x` with the right answer and keeps every work head below `K * (f |x| + 1)` on every reachable configuration.
- **No space-constructibility hypothesis is required:** the deterministic TM searches widths `L = 1, 2, …`, checking both `|x| + 1 < 2 ^ L` (`fitTest`) and whether any reachable configuration in width `L` has a move that steps outside the `L`-cell block (`escTest`), stopping at the first closed width.

See [`PLAN.md`](PLAN.md) for the full architecture and design notes.

## Layout

```
Savitch/
  Reach/Basic.lean          ReachIn (bounded reachability), midpoint lemma, card bound
  Reach/Recursive.lean      recursive `savitch` function and its correctness
  Space/StackMachine.lean   explicit stack machine, bit-level space measure, O(w²) bound
  Space/Generic.lean        the Phase 2 stack machine over any Fin N (correctness, stack depth)
  Machine/NTM.lean          NTM model, NSPACE, configuration counting and encoding
  Machine/Encode.lean       total record encoding of configurations, acceptance as vertex reachability
  Machine/Next.lean         successor function nextB; generated-edge graph; accepts_iff_gen
  Machine/Width.lean        closure under steps: accepts_iff_gen_closed, no_escape_of_bounded
  Main.lean                 sink reduction, oracle, `savitch_relative`
  TM/DTM.lean               deterministic multi-tape TMs, DSPACE
  TM/Prog.lean              tape assembly language, compiled to DTMs (`Code.mem_DSPACE`)
  TM/Block.lean             verified composition: seq, ifElse, whileDo, space bounds
  TM/Macros.lean            tape routines: scans, rewind, case split, symbol and block copy
  TM/Binary.lean            binary blocks: value, increment, in-place increment and compare routines
  TM/Digits.lean            base-m digit blocks: value, increment, compare routines (vertices on tape)
  TM/Frame.lean             frame rule: code that does not touch a tape leaves it unchanged
  TM/Counter.lean           binary decrement and zero test
  TM/Track.lean             copying through a symbol map; in-place lockstep zip
  TM/Input.lean             counters with a home cell; position-tracked input head (inRight, inLeft, seekIn, rewindIn)
  TM/Layout.lean            block layout and whole-block copy / zip passes
  Edge/Build.lean           the Savitch TM alphabet; building a successor's encoding on tape
  Edge/Mark.lean            marking the decoded work head of a vertex block
  Edge/Moves.lean           per-move pieces: moved input position, moved head mark
  Edge/Key.lean             building the key cell (state, input symbol, work symbol)
  Edge/Check.lean           checking one move of M against the target vertex
  Edge/Test.lean            the complete edge-test subroutine (`Spec.edgeTest`)
  Sav/Stack.lean            block stacks and phase-bit stack on tape
  Sav/Rep.lean              representing the generic Phase 2 machine on tape
  Sav/Body.lean             one step of the generic Phase 2 machine on tape
  Sav/Loop.lean             the Savitch main loop (`loop_done`)
  Outer/Esc.lean            the escape test (`Spec.escTest`)
  Outer/Reach.lean          reachability from a fixed source as a subroutine (`Spec.reachSub`)
  Outer/Vertex.lean         processing one target vertex: reachability, escape, acceptance (`Spec.perVertex`)
  Outer/VLoop.lean          looping over all vertices at width L (`Spec.vLoop`)
  Outer/Build.lean          building L-cell and c·L-cell blocks from the ruler tape
  Outer/Step.lean           input-head reset, `|x| + 1 < 2^L` test (`fitTest`), depth initializer (`loadK`)
  Outer/Setup.lean          per-width tape initialization (`Spec.setupWidth`)
  Outer/WLoop.lean          outer width-search loop (`wBody`, `wLoop`, `savitchBody`)
  Final.lean                halting wrapper and final theorem `Savitch.savitch_theorem`
PLAN.md                     design plan and progress notes
```

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain (Lean v4.36.0) and Mathlib version are pinned.

```sh
lake exe cache get   # download prebuilt Mathlib
lake build
```

To check which axioms the final theorem depends on:

```lean
import Savitch
#print axioms Savitch.savitch_theorem
```
