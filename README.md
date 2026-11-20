# Savitch's Theorem in Lean 4

> [!WARNING]
> **This repository is entirely AI-generated.** All Lean code, proofs,
> definitions, documentation and the plan in `PLAN.md`, including this README,
> were written by an AI model (Anthropic's Claude, working through Claude Code).
> No human wrote or reviewed the proofs line by line.
>
> The Lean kernel *does* check every proof. `lake build` succeeds, there is no
> `sorry`, and the main theorems depend only on Lean's standard axioms
> (`propext`, `Classical.choice`, `Quot.sound`). That still only guarantees the
> theorems *as stated*. Whether the definitions (`NSPACE`, the machine models,
> the space measure) faithfully capture the textbook notions is a modelling
> question that a human should review. Treat this repo as an experiment, not a
> reference.

An attempted formalization of **Savitch's theorem**:

    NSPACE(s(n)) ⊆ DSPACE(s(n)²)    for s(n) ≥ log n

## Status

| Phase | Result | File |
|---|---|---|
| 1. Abstract reachability | `savitch_correct`: the recursive midpoint procedure, at depth `⌈log₂ \|V\|⌉`, decides reachability in any finite graph | `Savitch/Reach/` |
| 2. Space-accounted machine | `Space.savitch_machine`: an explicit stack machine decides reachability on `2^w` vertices using at most `(w+1)(4w+1)` bits | `Savitch/Space/StackMachine.lean` |
| 3. NTMs and `NSPACE` | `NTM.accepts_iff_cfgGraph_Cs`: acceptance by an `s`-space NTM is reachability in a configuration graph on `2^(C·s)` vertices | `Savitch/Machine/NTM.lean` |
| 4a. Main theorem (oracle-relative) | `savitch_relative` | `Savitch/Main.lean` |
| 4b. True `DSPACE` via Turing machines | **in progress**: DTM model, `DSPACE`, a tape assembly language proved to compile to DTMs (`Code.mem_DSPACE`), verified `seq` / `ifElse` / `whileDo` combinators, the basic tape routines (scan, rewind, case split, block copy, increment and compare for binary and base-m blocks), and the configuration encoding with total decoding (`accepts_iff_vertex`). plus the counter and input-head routines the edge test needs. The edge-test program itself and the Savitch TM are not written yet | `Savitch/TM/` |

### What is actually proved

`Savitch.savitch_relative`: suppose `log n ≤ s n` for all `n`, and `L ∈ NSPACE s`. Then there is an NTM `M` that accepts `L` and a constant `K` such that, on every input `x`:

- the deterministic stack machine, querying `M`'s own configuration-graph oracle, halts with the correct answer to `x ∈ L`;
- every state it passes through uses at most `K · (s|x| + 1)²` bits.

### What is *not* proved yet

This is **not yet the full theorem**:

1. **Oracle cost.** Each query to the step-relation oracle is free. A complete proof must show that each query (decode two configurations, check the transition table) takes `O(s)` space.
2. **Space constructibility.** The deterministic machine is handed the configuration width; it does not compute it itself.
3. **The Savitch Turing machine isn't built yet.** `DSPACE` is now defined over deterministic multi-tape Turing machines (`Savitch/TM/DTM.lean`), but the program that runs Savitch's algorithm on tapes, and its proof, are still to do (see the Phase 4b roadmap in `PLAN.md`).

See [`PLAN.md`](PLAN.md) for the full design, the design decisions made so far, and the remaining work.

## Layout

```
Savitch/
  Reach/Basic.lean          ReachIn (bounded reachability), midpoint lemma, card bound
  Reach/Recursive.lean      recursive `savitch` function and its correctness
  Space/StackMachine.lean   explicit stack machine, bit-level space measure, O(w²) bound
  Machine/NTM.lean          NTM model, NSPACE, configuration counting and encoding
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
  Space/Generic.lean        the Phase 2 stack machine over any Fin N (correctness, stack depth)
  Machine/Encode.lean       total record encoding of configurations, acceptance as vertex reachability
  Machine/Next.lean         successor function nextB; generated-edge graph; accepts_iff_gen
PLAN.md                     design plan and progress notes
```

## Building

Requires [elan](https://github.com/leanprover/elan). The toolchain (Lean v4.36.0) and Mathlib version are pinned.

```sh
lake exe cache get   # download prebuilt Mathlib
lake build
```

To check which axioms a theorem depends on:

```lean
import Savitch
#print axioms Savitch.savitch_relative
```
