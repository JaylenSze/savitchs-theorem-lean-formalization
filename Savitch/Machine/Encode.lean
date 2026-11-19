import Savitch.Machine.NTM
import Savitch.TM.Binary
import Mathlib.Algebra.BigOperators.Fin

/-!
# An explicit, totally decodable encoding of NTM configurations

Phase 4b-3 of the Savitch formalization (see `PLAN.md`).

The Savitch Turing machine stores each bounded configuration of `M` as a block
of `L` tape cells, **one cell per work cell of `M`**. Each cell holds a
*record* `(symbol, head flag, one bit of the input-head position, state)`:

* `encR b`: the record block of a bounded configuration `b`.
* `decR f`: decodes **any** record block into a bounded configuration. The state
  is read from record 0, the work head is the first flagged cell (or 0), and the
  input head is the binary value of the bit track, capped at `n + 1`.
* `decR_encR`: `decR (encR b) = b`, provided `n + 1 < 2 ^ L`.

Because decoding is total, the Turing machine never has to check that a block
is a valid encoding. Its edge test is simply `BStep (decV u) (decV v)`.

Vertices of the generic Phase 2 machine are `Fin (|Rec| ^ L)`, read as `L`
little-endian base-`|Rec|` digits (`encV`, `decV`).

Main result, `accepts_iff_vertex`: if `s |x| ≤ L` and `|x| + 1 < 2 ^ L`, then `M`
accepts `x` iff some vertex decoding to an accepting configuration is reachable
from `encV (initB)` along `fun u v => BStep (decV u) (decV v)`.
-/

set_option linter.unusedSectionVars false

namespace Savitch.Machine

open TM (bval)

/-! ### Bits of a number -/

/-- The `L` low bits of `v`, little-endian. -/
def toBits (v : ℕ) : ℕ → List Bool
  | 0 => []
  | L + 1 => decide (v % 2 = 1) :: toBits (v / 2) L

theorem toBits_length (v : ℕ) : ∀ L, (toBits v L).length = L
  | 0 => rfl
  | L + 1 => by simp [toBits, toBits_length (v / 2) L]

theorem bval_toBits : ∀ (L v : ℕ), v < 2 ^ L → bval (toBits v L) = v
  | 0, v, h => by simp at h; simp [toBits, bval, h]
  | L + 1, v, h => by
    have ih := bval_toBits L (v / 2) (by rw [Nat.pow_succ] at h; omega)
    simp only [toBits, bval, ih]
    rcases Nat.mod_two_eq_zero_or_one v with h2 | h2 <;> simp [h2] <;> omega

theorem ofFn_getD (l : List Bool) {L : ℕ} (h : l.length = L) :
    List.ofFn (fun j : Fin L => l.getD j false) = l := by
  subst h
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD]

namespace NTM

variable {Λ Γ : Type} [Fintype Λ] [Fintype Γ] [DecidableEq Λ] [DecidableEq Γ]

/-- A record: `(work symbol, head here?, input-head bit, state)`. -/
abbrev Rec (Λ Γ : Type) := Γ × Bool × Bool × Λ

variable {n L : ℕ}

/-- The first flagged cell, or cell 0. -/
def firstFlag (hL : 0 < L) (f : Fin L → Rec Λ Γ) : Fin L :=
  if h : (Finset.univ.filter fun j => (f j).2.1 = true).Nonempty then
    (Finset.univ.filter fun j => (f j).2.1 = true).min' h
  else ⟨0, hL⟩

/-- Decode any record block (total). -/
def decR (hL : 0 < L) (f : Fin L → Rec Λ Γ) : BCfg Λ Γ n L :=
  ((f ⟨0, hL⟩).2.2.2,
   ⟨min (bval (List.ofFn fun j => (f j).2.2.1)) (n + 1), by omega⟩,
   firstFlag hL f,
   fun j => (f j).1)

/-- Encode a bounded configuration as a record block. -/
def encR (b : BCfg Λ Γ n L) : Fin L → Rec Λ Γ :=
  fun j => (b.2.2.2 j, decide (j = b.2.2.1), (toBits b.2.1.val L).getD j.val false, b.1)

theorem decR_encR (hL : 0 < L) (hih : n + 1 < 2 ^ L) (b : BCfg Λ Γ n L) :
    decR hL (encR b) = b := by
  obtain ⟨q, ih, wh, tape⟩ := b
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
  · apply Fin.ext
    simp only [decR, encR]
    rw [ofFn_getD _ (toBits_length _ _), bval_toBits L ih.val (by have := ih.isLt; omega)]
    have := ih.isLt
    omega
  · have hfilt : (Finset.univ.filter fun j => (encR (n := n) (q, ih, wh, tape) j).2.1 = true)
        = {wh} := by
      ext j; simp [encR]
    simp only [decR, firstFlag, hfilt, Finset.singleton_nonempty, ↓reduceDIte,
      Finset.min'_singleton]

/-! ### Vertices -/

/-- Number of vertices: record blocks of length `L`. -/
abbrev nV (Λ Γ : Type) [Fintype Λ] [Fintype Γ] (L : ℕ) : ℕ := Fintype.card (Rec Λ Γ) ^ L

/-- A vertex as a record block (little-endian digits in the order of `equivFin`). -/
noncomputable def recs (v : Fin (nV Λ Γ L)) : Fin L → Rec Λ Γ :=
  fun j => (Fintype.equivFin _).symm (finFunctionFinEquiv.symm v j)

/-- A record block as a vertex. -/
noncomputable def unrecs (f : Fin L → Rec Λ Γ) : Fin (nV Λ Γ L) :=
  finFunctionFinEquiv (fun j => Fintype.equivFin _ (f j))

theorem recs_unrecs (f : Fin L → Rec Λ Γ) : recs (unrecs f) = f := by
  funext j; simp [recs, unrecs]

noncomputable def decV (hL : 0 < L) (v : Fin (nV Λ Γ L)) : BCfg Λ Γ n L := decR hL (recs v)

noncomputable def encV (b : BCfg Λ Γ n L) : Fin (nV Λ Γ L) := unrecs (encR b)

theorem decV_encV (hL : 0 < L) (hih : n + 1 < 2 ^ L) (b : BCfg Λ Γ n L) : decV hL (encV b) = b := by
  rw [decV, encV, recs_unrecs, decR_encR hL hih]

/-! ### Acceptance as reachability among vertices -/

variable (M : NTM Λ Γ) {s : ℕ → ℕ}

/-- Phase 3's `accepts_iff_bounded`, with any width `L ≥ s |x|`. -/
theorem accepts_iff_boundedL (hM : M.SpaceBounded s) (x : List Bool) {L : ℕ}
    (hsL : s x.length ≤ L) (hL : 0 < L) :
    M.Accepts x ↔ ∃ b : BCfg Λ Γ x.length L,
      b.1 = M.accept ∧ Relation.ReflTransGen (M.BStep x) (M.initB hL) b := by
  have good : ∀ {d}, Relation.ReflTransGen (M.Step x) M.init d → M.Good x.length L d := by
    intro d hd
    obtain ⟨h1, h2, h3⟩ := M.reachable_good hM hd
    exact ⟨h1, lt_of_lt_of_le h2 hsL, fun j hj => h3 j (le_trans hsL hj)⟩
  constructor
  · rintro ⟨d, hd, hacc⟩
    have lift : ∀ d, Relation.ReflTransGen (M.Step x) M.init d →
        ∃ b : BCfg Λ Γ x.length L,
          M.toCfg b = d ∧ Relation.ReflTransGen (M.BStep x) (M.initB hL) b := by
      intro d hd
      induction hd with
      | refl => exact ⟨_, M.toCfg_initB _, .refl⟩
      | @tail c d hcd hstep ih =>
        obtain ⟨b, hb, hpath⟩ := ih
        obtain ⟨b', hb'⟩ := M.exists_toCfg (good (hcd.tail hstep))
        refine ⟨b', hb', hpath.tail ?_⟩
        unfold BStep
        rw [hb, hb']
        exact hstep
    obtain ⟨b, hb, hpath⟩ := lift d hd
    have : (M.toCfg b).q = M.accept := hb ▸ hacc
    exact ⟨b, this, hpath⟩
  · rintro ⟨b, hacc, hpath⟩
    have : Relation.ReflTransGen (M.Step x) (M.toCfg (M.initB hL)) (M.toCfg b) :=
      hpath.lift M.toCfg (fun _ _ h => h)
    rw [M.toCfg_initB] at this
    exact ⟨_, this, hacc⟩

/-- The edge relation on vertices: decode both ends and take one step of `M`. -/
def VEdge (x : List Bool) (hL : 0 < L) (u v : Fin (nV Λ Γ L)) : Prop :=
  M.BStep x (decV (n := x.length) hL u) (decV (n := x.length) hL v)

/-- **Acceptance as vertex reachability.** -/
theorem accepts_iff_vertex (hM : M.SpaceBounded s) (x : List Bool) {L : ℕ}
    (hsL : s x.length ≤ L) (hL : 0 < L) (hih : x.length + 1 < 2 ^ L) :
    M.Accepts x ↔ ∃ v : Fin (nV Λ Γ L), (decV (n := x.length) hL v).1 = M.accept ∧
      Relation.ReflTransGen (M.VEdge x hL) (encV (n := x.length) (M.initB hL)) v := by
  rw [M.accepts_iff_boundedL hM x hsL hL]
  constructor
  · rintro ⟨b, hacc, hp⟩
    refine ⟨encV b, by rw [decV_encV hL hih]; exact hacc, ?_⟩
    have : Relation.ReflTransGen (M.VEdge x hL) (encV (M.initB hL)) (encV b) :=
      hp.lift encV (fun a b h => by
        show M.BStep x (decV hL (encV a)) (decV hL (encV b))
        rw [decV_encV hL hih, decV_encV hL hih]
        exact h)
    exact this
  · rintro ⟨v, hacc, hp⟩
    have : Relation.ReflTransGen (M.BStep x) (decV (n := x.length) hL (encV (M.initB hL)))
        (decV hL v) := hp.lift (decV hL) (fun _ _ h => h)
    rw [decV_encV hL hih] at this
    exact ⟨_, hacc, this⟩

end NTM

end Savitch.Machine
