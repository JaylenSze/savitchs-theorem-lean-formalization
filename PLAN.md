# Formalizing Savitch's Theorem in Lean 4: Plan

## Goal

**Savitch's theorem.** If `s(n) ≥ log n` and `s` is space-constructible, then

    NSPACE(s(n)) ⊆ DSPACE(s(n)²)

The proof has one mathematical core, the midpoint recursion for reachability. Most of the work around it is bookkeeping: machine models, encodings of configurations, and space accounting. The plan keeps these layers separate, so the core gets proved early and the costly parts are added one at a time.

## Progress

| Phase | Status | Where |
|---|---|---|
| 0 Setup | ✅ Lean v4.36.0 + Mathlib v4.36.0 | `lakefile.toml` |
| 1 Abstract reachability | ✅ `savitch_correct`, `ReachIn.reflTransGen_iff_card` | `Savitch/Reach/` |
| 2 Space-accounted machine | ✅ `Space.savitch_machine`: decides reachability on `2^w` vertices in ≤ `(w+1)(4w+1)` bits | `Savitch/Space/StackMachine.lean` |
| 3 NTM + NSPACE | ✅ `NTM.accepts_iff_cfgGraph_Cs`: acceptance ↔ reachability in a config graph on `Fin (2^(C·s))`; `card_BCfg_le`, `reachable_good` | `Savitch/Machine/NTM.lean` |
| 4a Final theorem, oracle-relative | ✅ `Savitch.savitch_relative` | `Savitch/Main.lean` |
| 4b Real `DSPACE` via Turing machines | 🚧 foundations done (4b-1); see roadmap below | `Savitch/TM/` |

### Phase 4b roadmap (Turing machines chosen)

| Step | Content | Status |
|---|---|---|
| 4b-1 | `DTM` (read-only input + `k` work tapes), `DSPACE`; tape assembly language; `Code.mem_DSPACE` (programs are DTMs, via a step-for-step simulation); verified `seq` / `ifElse` / `whileDo` with space bounds; `Seg.reachable` | ✅ |
| 4b-2 | Primitive routines with `Spec`s. `Savitch/TM/Macros.lean`: single instructions, `scanRight` / `scanLeft`, `rewind` to a left-end marker, finite case split `cases` (the pattern for compiling finite tables such as `δ`), `copySym`, lockstep block copy `copyWhile`. `Savitch/TM/Binary.lean`: little-endian binary values `bval` / `binc` with `bval_binc` (+1), `bval_inj`; in-place binary increment `incr`; block compare `cmpBits` into a flag cell. (Unary counters turned out unnecessary: recursion depth is tracked by the head position on a dedicated tape.) | ✅ |
| 4b-3 | Data layout. **Done.** *Design change:* a vertex is a block of `L` tape cells, one per work cell of `M`, each holding a **record** `(symbol, head flag, input-head bit, state)` (`Savitch/Machine/Encode.lean`). Decoding `decR` is **total**: state from record 0, work head = first flagged cell (else 0), input head = value of the bit track capped at `n+1`. With `decR (encR b) = b`, the edge test is just `BStep (dec u) (dec v)` and needs no validity checks (`accepts_iff_vertex`). Vertices are `Fin (|Rec|^L)` read as little-endian base-`|Rec|` digits (`finFunctionFinEquiv_val`), so the TM walks them with `incrD` and tests equality with `cmpD` (`Savitch/TM/Digits.lean`). Phase 2 was restated over any `Fin N` (`Savitch/Space/Generic.lean`: `run_correct`, `decides`, `reachable_stack_le`); the original Phase 2 file is unchanged | ✅ |
| 4b-4 | Edge-test program. **Design changed to generate-and-compare** (`Savitch/Machine/Next.lean`): `nextB b t` is the successor after move `t` (`none` if the work head leaves the block); `bstep_iff_nextB`; the Savitch graph is now `GEdge u v` = "`v` is the canonical encoding of a successor of `dec u`", with `accepts_iff_gen` and `gEdge_iff`. So the TM never decodes `v`: for each move it **builds** `encV (nextB (dec u) t)` on a scratch tape and compares with `v` (`cmpD`). **Done:** frame rule; counters (`Holds`, `incrH`, `decrH`, `isZeroH`); mapped copy (`copyMapWhile`); in-place zip (`zipWhile`, `a := F a b`); position-tracked input head (`inRight`, `inLeft`, `seekIn`). **Remaining program:** (1) copy `u`'s input-bit track to a counter, `seekIn` → `P = ih`; read `q` (record 0) and the input symbol; (2) mark track `A1` at `u`'s first flag (cell 0 if none), and read the work symbol `g` there; (3) case tree over `(q, i, g)`, then for each move `(q₂, g₂, di, dw) ∈ δ q i g`: counter `P' = moveIn ih di` (computed from `P` without moving the input head); mark track `A2` at `moveWork wh dw`, skipping the move if it leaves the block; build `S` in passes (`copyMapWhile` from `U` setting the state, then `zipWhile` passes to set the symbol at `A1`, the flag at `A2` and the bits of `P'`); `cmpD S V`; OR the results; (4) the theorem that the answer is `decide (GEdge u v)` | 🚧 |
| 4b-5 | The Savitch program. Prove it **refines the Phase 2 stack machine** (an abstraction map from tapes to `Space.State`), so correctness comes from Phase 2 instead of being re-proved. Space: `Space.reachable_stack_le` (**done**) shows every reachable Phase 2 state has at most `K` frames, so the tape length is `O(K · frame width)` | |
| 4b-6 | Choosing `L`: start at `bits(n+2)` (count the input) and use the "iterate `L` until nothing exceeds it" trick, which needs no constructibility hypothesis. Fallback: assume constructibility | |
| 4b-7 | Final theorem `NSPACE s ⊆ DSPACE (s²)` for `s ≥ log n` | |

Model notes: `DTM` has `k` work tapes; a left move at cell 0 stays put; the space bound is that every work head stays below `c·(f n + 1)`, so at most `k·c·(f n+1)` cells are used. Programs execute one tape action per step. Jumps are relative, so blocks concatenate without relocation.

**What `savitch_relative` says.** Assume `log n ≤ s n` and `L ∈ NSPACE s`. Then there is an NTM `M` for `L` and a constant `K` such that, on every `x`, the Phase 2 deterministic machine querying **`M`'s own configuration-graph oracle** halts with the answer to `x ∈ L`. Every state it passes through has at most `K·(s|x|+1)²` bits. Many accepting configurations are reduced to one target by adding a sink vertex, at the cost of one extra bit.

**What it does not yet account for (Phase 4b):**
1. *Oracle cost.* Each oracle query (decode two configurations, check `δ`) must be shown to take `O(s)` space. This needs an explicit bit-level encoding in place of `Fintype.equivFin`, and a deterministic model in which that space can be measured.
2. *Knowing `w`.* The machine is handed `w = cw s x`. A real `DSPACE` machine has to compute it, which is where space-constructibility (or the iterate-`s` trick) comes in.
3. *A `DSPACE` class.* It has to be defined over a restricted model; an unrestricted step function could decide anything in one step. Options:
   - (a) deterministic TMs of the Phase 3 shape. This is the gold standard, but it means compiling the stack machine to a TM.
   - (b) a small register machine with `O(1)` registers, a stack of register tuples, and primitive arithmetic. Its space is the total register bits, and it is TM-equivalent up to constants (assumed, not proved).

Phase 3 notes, which affect Phase 4:
- Input head moves are clamped to the end markers. Space bounds count work cells only: the work head stays below `s |x|` on every reachable configuration.
- `NSPACE s` allows space `c · (s n + 1)`, so `s n = 0` is harmless.
- There is no single-accept normalization. The theorem says "some accepting vertex is reachable", so Phase 4 needs an outer loop over target vertices.
- **The encoding `encode` is only an injection into `Fin (2^w)`, built from `Fintype.equivFin`.** It is the right size but not computable in small space. Phase 4 must replace it with an explicit bit-level encoding (state ‖ input head ‖ work head ‖ tape). Then the edge test, decode two configurations and check `δ`, can be shown to run in `O(s)` space.

There are no `sorry`s. The main theorems use only `propext`, `Classical.choice` and `Quot.sound`.

How Phase 2 differs from the sketch below: there is one file instead of two, and the vertex type is `Fin (2^w)` rather than `BitVec w`. The space bound is about *every reachable state*. That follows from determinism plus a run whose states all stay within the bound (`Bounded`) and that ends at a fixed point (`done`). The edge oracle `E` is still free: it costs nothing.

## Status of the ecosystem (check before starting)

- **Mathlib** has Turing machines (`Mathlib/Computability/TuringMachine.lean`: `TM0`, `TM1`, `TM2`) and **time** complexity (`Mathlib/Computability/TMComputable.lean`, `TM2ComputableInPolyTime`). As far as I know it has **no space complexity**: no `DSPACE`/`NSPACE` and no input-tape/work-tape separation. We will define our own.
- Related prior work worth skimming for design ideas: the Cook–Levin formalizations in Coq (Gäher & Kunze, ITP 2021) and Isabelle (Balbach, AFP 2023), and Forster–Kunze–Roth (POPL 2020) on space-faithful λ-calculus. **TODO:** search for an existing Savitch formalization in any proof assistant before committing to a design.
- **Local machine:** Lean is not installed yet (no `elan`, `lean` or `lake` on PATH).

## Architecture: four layers

```
Layer 1  Abstract reachability (pure math)       ← the real theorem
Layer 2  Space-accounted deterministic algorithm ← the "s²" part
Layer 3  Nondeterministic machine + NSPACE       ← the "2^O(s) configs" part
Layer 4  Glue / final theorem (+ optional TM compilation)
```

Each layer ends in one headline theorem, and later layers use only the headline theorems of earlier ones.

---

### Phase 0: Project setup

```powershell
# install elan (Lean toolchain manager), then:
lake new Savitch math
cd Savitch; lake exe cache get; lake build
```

Proposed layout:

```
Savitch/
  Reach/Basic.lean        -- ReachIn, midpoint lemma, card bound
  Reach/Recursive.lean    -- recursive savitch function + correctness
  Space/Model.lean        -- deterministic stack machine with bit-level space measure
  Space/SavitchImpl.lean  -- iterative Savitch on the stack machine, space bound
  Machine/NTM.lean        -- NTM with read-only input + work tape, configs, step
  Machine/Classes.lean    -- NSPACE / DSPACE definitions
  Machine/ConfigCount.lean-- #configs ≤ 2^(c·s(n)), config encoding as BitVec
  Main.lean               -- Savitch's theorem
```

---

### Phase 1: Abstract reachability (Layer 1)

Machine-independent: a relation `R` on a `Fintype α`.

```lean
/-- `ReachIn R n a b`: b is reachable from a in at most n steps. -/
inductive ReachIn (R : α → α → Prop) : ℕ → α → α → Prop
  | refl  (n a)     : ReachIn R n a a
  | step  {n a b c} : R a b → ReachIn R n b c → ReachIn R (n+1) a c

theorem reachIn_mono      : m ≤ n → ReachIn R m a b → ReachIn R n a b
theorem reachIn_add_iff   : ReachIn R (m+n) a c ↔ ∃ b, ReachIn R m a b ∧ ReachIn R n b c
theorem reflTransGen_iff_reachIn_card [Fintype α] :
    Relation.ReflTransGen R a b ↔ ReachIn R (Fintype.card α) a b   -- shortest paths, pigeonhole

def savitch [Fintype α] [DecidableEq α] [DecidableRel R] : ℕ → α → α → Bool
  | 0,   a, b => decide (a = b) || decide (R a b)
  | k+1, a, b => Finset.univ.any fun c => savitch k a c && savitch k c b

theorem savitch_spec : savitch R k a b = true ↔ ReachIn R (2^k) a b
theorem savitch_correct :
    savitch R (Nat.clog 2 (Fintype.card α)) a b = true ↔ Relation.ReflTransGen R a b
```

**Done when:** `savitch_correct` is proved. This should be the quickest phase and gives a good first milestone. The hardest lemma is the cycle-removal / card bound. Check whether Mathlib's `SimpleGraph.Walk` / `List.Chain` / `Relation` API already has it.

---

### Phase 2: Space-accounted deterministic algorithm (Layer 2)

The recursive Lean function in Phase 1 says nothing about space. Lean's own recursion is not measured. We need an explicit deterministic model in which space is a number we can bound.

**Model:** a small deterministic machine whose state is an explicit stack of frames over `BitVec w` vertices:

```lean
structure Frame (w : ℕ) where
  a b c : BitVec w   -- endpoints and current midpoint candidate
  k     : ℕ          -- remaining depth (stored in ≤ log k + 1 bits)
  phase : Phase      -- {checkLeft, checkRight, advance, ...}: O(1) bits

def space (st : State w) : ℕ := Σ frame bit-sizes   -- bit-faithful measure
def step  : State w → State w                         -- one deterministic step
```

The graph is given as a deterministic edge oracle `edge : BitVec w → BitVec w → Bool`. Its space cost is a parameter, to be filled with `O(s)` in Phase 4. Midpoints are enumerated by incrementing `c : BitVec w`, which is why `BitVec w` is a better vertex type than an arbitrary `Fintype`.

Headline theorems:

```lean
theorem impl_correct : run (init a b k) = some (savitch edge k a b)
theorem impl_space   : ∀ st ∈ trace (init a b k), space st ≤ (k+1) * (3*w + Nat.log 2 k + C)
```

With `k = w` (since `#vertices = 2^w`) this gives **O(w²)**. That is the "s²" of the theorem.

**Done when:** both theorems are proved. Expect this phase to be noticeably harder than Phase 1. The proof needs a simulation invariant relating the explicit stack to the recursive call tree, and it is the core of the whole project.

---

### Phase 3: Nondeterministic machines and NSPACE (Layer 3)

Define an NTM with a **read-only input tape** and **one work tape**. Without the input/work split, sublinear `s` (for example `s = log n`) makes no sense.

```lean
structure NTM (Γ Λ : Type) [Fintype Γ] [Fintype Λ] where
  δ      : Λ → Option Bool → Γ → Finset (Λ × Γ × Dir × Dir)   -- (input sym, work sym) ↦ choices
  start accept : Λ

structure Config (M) (n s : ℕ) where
  q    : Λ
  ih   : Fin (n+2)        -- input head (with end markers)
  wh   : Fin s            -- work head
  tape : Fin s → Γ        -- work tape, bounded to s cells

def NSPACE (s : ℕ → ℕ) : Set (Language Bool) :=
  { L | ∃ M c, ∀ x, (every reachable config of M on x uses ≤ c * s |x| cells)
                   ∧ (x ∈ L ↔ an accepting config is reachable) }
```

Headline theorems:

```lean
theorem card_config  : Fintype.card (Config M n s) ≤ |Λ| * (n+2) * s * |Γ|^s
theorem config_bits  : s ≥ Nat.log 2 n → ∃ w ≤ C * s, Config M n s ↪ BitVec w   -- encoding
theorem accept_iff_reach : accepts M x ↔ ReflTransGen (stepRel M x) (init x) acc
```

**Simplification to do early:** normalize every NTM so that it clears its work tape and parks its heads before accepting. Then there is a **single** accepting configuration and reachability becomes a single-target question. Prove this normalization preserves the language and the space bound up to a constant. The alternative is to quantify over all accepting configs in the deterministic algorithm (one more loop, also fine).

---

### Phase 4: Glue: the final theorem

1. For input `x`, the configuration graph of `M` on `x` is a relation on `BitVec w` with `w = O(s(|x|))` (Phase 3).
2. The edge oracle `stepRel M x u v` must be decidable *in space O(s)*: decode `u` and `v`, read one input symbol, check `δ`.
3. Run the Phase 2 algorithm with `k = w`. Correctness comes from Phases 1–3, and the space bound is `O(w²) = O(s²)`.
4. **Space-constructibility:** the deterministic machine has to know `s(|x|)` to set `w`. Either
   - (a) assume `s` is space-constructible (textbook statement; requires defining it), or
   - (b) use the trick of iterating `s = 1, 2, 3, …` until no reachable configuration exceeds the bound. This drops the constructibility assumption at the cost of an extra proof.

   **Recommendation:** (a) first, (b) as a stretch goal.

**Final statement (MVP):**

```lean
theorem savitch (s : ℕ → ℕ) (hs : ∀ n, Nat.log 2 n ≤ s n) (hc : SpaceConstructible s) :
    NSPACE s ⊆ DSPACE (fun n => s n ^ 2)
```

**Key design decision: what `DSPACE` means.**

- **MVP:** `DSPACE` is defined via the Phase 2 deterministic stack machine (bit-faithful space, with input read through an oracle). The theorem is honest about space, but the two sides of `⊆` use different machine models.
- **Gold standard (stretch):** `DSPACE` is defined by *deterministic TMs of the same Phase 3 shape*. This requires **compiling** the stack machine into a TM and proving the compilation preserves space up to a constant. It is the most labour-intensive part by far, because building concrete TMs in Lean is painful. Do it only after the MVP is done, and consider building a small verified "TM macro" library first: sequencing, loops, binary counters.

---

## Risks and how to mitigate them

| Risk | Mitigation |
|---|---|
| Space accounting is silently cheated (Lean values aren't measured) | Space is *only* ever read from the explicit `space` function of an explicit machine. Never reason about space of Lean terms. |
| Big-O bookkeeping becomes painful | Carry explicit constants (`∃ c, ∀ n, … ≤ c * s n + c`) internally; convert to `Asymptotics.IsBigO` only in the final statement, if at all. |
| `s(n) ≥ log n` subtleties (input head position) | Isolate in `config_bits`; everything downstream sees only `w ≤ C * s`. |
| Phase 2 simulation proof blows up | First prove it for a *recursive* small-step semantics with an abstract stack, then refine to the bit-level `space` measure. |
| TM compilation (stretch) is a sinkhole | Keep it out of the MVP; the MVP theorem is already a meaningful result. |

## Milestone order

1. Phase 0 setup, then Phase 1 `savitch_correct` *(first working result)*
2. Phase 2 `impl_correct` + `impl_space` *(the space bound)*
3. Phase 3 NTM, `NSPACE`, config counting/encoding
4. Phase 4 MVP `savitch` theorem
5. Stretch: drop space-constructibility (iterative trick)
6. Stretch: compile to TMs so that `DSPACE` uses TMs as well
