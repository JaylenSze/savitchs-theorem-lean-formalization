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
| 4b. True `DSPACE` | **not done** | — |

### What is actually proved

`Savitch.savitch_relative`: suppose `log n ≤ s n` for all `n`, and `L ∈ NSPACE s`. Then there is an NTM `M` that accepts `L` and a constant `K` such that, on every input `x`:

- the deterministic stack machine, querying `M`'s own configuration-graph oracle, halts with the correct answer to `x ∈ L`;
- every state it passes through uses at most `K · (s|x| + 1)²` bits.

### What is *not* proved yet

This is **not yet the full theorem**:

1. **Oracle cost.** Each query to the step-relation oracle is free. A complete proof must show that each query (decode two configurations, check the transition table) takes `O(s)` space.
2. **Space constructibility.** The deterministic machine is handed the configuration width; it does not compute it itself.
3. **No `DSPACE` class yet.** `DSPACE` has to be defined over a restricted deterministic model, either Turing machines or a register machine, and the algorithm compiled to it.

See [`PLAN.md`](PLAN.md) for the full design, the design decisions made so far, and the remaining work.

## Layout

```
Savitch/
  Reach/Basic.lean          ReachIn (bounded reachability), midpoint lemma, card bound
  Reach/Recursive.lean      recursive `savitch` function and its correctness
  Space/StackMachine.lean   explicit stack machine, bit-level space measure, O(w²) bound
  Machine/NTM.lean          NTM model, NSPACE, configuration counting and encoding
  Main.lean                 sink reduction, oracle, `savitch_relative`
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
