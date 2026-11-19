import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Log
import Mathlib.Logic.Relation
import Mathlib.Tactic.Ring

/-!
# Nondeterministic space-bounded Turing machines

Phase 3 of the Savitch formalization (see `PLAN.md`).

* `NTM Λ Γ`: a nondeterministic TM with a **read-only input tape** (binary input
  between two end markers) and **one work tape** over `Γ`.
* `Cfg`: unbounded configurations; `NTM.Step`: the one-step relation.
* `NTM.SpaceBounded M s`: on every input `x`, every reachable configuration keeps
  the work head below `s |x|`.
* `NSPACE s`: languages accepted by some NTM within space `O(s)`.

Main results:
* `NTM.reachable_good`: a space-bounded machine only ever reaches configurations
  in the finite region `Good`.
* `NTM.card_BCfg_le`: if `log n ≤ s` and `1 ≤ s`, the bounded configurations
  number at most `2 ^ (C * s)`, with `C` depending only on `|Λ|` and `|Γ|`.
* `NTM.accepts_iff_cfgGraph`: acceptance ↔ reachability of an accepting vertex
  in a graph on `Fin (2 ^ w)`, the vertex type consumed by Phase 2.
-/

namespace Savitch.Machine

inductive Dir
  | left | stay | right
  deriving DecidableEq

/-- A nondeterministic TM: read-only binary input tape + one work tape over `Γ`.
`δ q i g` lists the possible moves `(q', g', input dir, work dir)` when in
state `q`, reading input symbol `i` (`none` = end marker) and work symbol `g`. -/
structure NTM (Λ Γ : Type) where
  blank : Γ
  start : Λ
  accept : Λ
  δ : Λ → Option Bool → Γ → List (Λ × Γ × Dir × Dir)

/-- A configuration. The input head ranges over `0 … n+1`, the positions `0`
and `n+1` holding the end markers. -/
@[ext]
structure Cfg (Λ Γ : Type) where
  q : Λ
  ih : ℕ
  wh : ℕ
  tape : ℕ → Γ

variable {Λ Γ : Type}

/-- Input symbol under the input head: `none` on the end markers. -/
def inputSym (x : List Bool) (i : ℕ) : Option Bool :=
  if i = 0 then none else x[i - 1]?

/-- Input head moves are clamped to the end markers `0` and `n + 1`. -/
def moveIn (n i : ℕ) : Dir → ℕ
  | .left => i - 1
  | .stay => i
  | .right => min (i + 1) (n + 1)

def moveWork (j : ℕ) : Dir → ℕ
  | .left => j - 1
  | .stay => j
  | .right => j + 1

/-- The configuration after applying move `t` to `c` on input `x`. -/
def Cfg.next (x : List Bool) (c : Cfg Λ Γ) (t : Λ × Γ × Dir × Dir) : Cfg Λ Γ where
  q := t.1
  ih := moveIn x.length c.ih t.2.2.1
  wh := moveWork c.wh t.2.2.2
  tape := Function.update c.tape c.wh t.2.1

namespace NTM

variable (M : NTM Λ Γ)

def Step (x : List Bool) (c d : Cfg Λ Γ) : Prop :=
  ∃ t ∈ M.δ c.q (inputSym x c.ih) (c.tape c.wh), d = c.next x t

def init : Cfg Λ Γ := ⟨M.start, 0, 0, fun _ => M.blank⟩

def Accepts (x : List Bool) : Prop :=
  ∃ d, Relation.ReflTransGen (M.Step x) M.init d ∧ d.q = M.accept

/-- On every input `x`, the work head of every reachable configuration stays
below `s |x|`, i.e. at most `s |x|` work cells are ever used. -/
def SpaceBounded (s : ℕ → ℕ) : Prop :=
  ∀ x d, Relation.ReflTransGen (M.Step x) M.init d → d.wh < s x.length

end NTM

/-- `NSPACE s`: languages accepted by a nondeterministic TM in space `O(s)`. -/
def NSPACE (s : ℕ → ℕ) : Set (Set (List Bool)) :=
  { L | ∃ (Λ Γ : Type) (_ : Fintype Λ) (_ : Fintype Γ) (M : NTM Λ Γ) (c : ℕ),
      M.SpaceBounded (fun n => c * (s n + 1)) ∧ ∀ x, x ∈ L ↔ M.Accepts x }

namespace NTM

variable (M : NTM Λ Γ) {x : List Bool} {s : ℕ → ℕ}

theorem SpaceBounded.pos {M : NTM Λ Γ} (hM : M.SpaceBounded s) (x : List Bool) :
    0 < s x.length :=
  hM x M.init .refl

/-! ### Reachable configurations stay in a finite region -/

/-- The finite region of configurations of a machine using `< s` work cells. -/
def Good (n s : ℕ) (d : Cfg Λ Γ) : Prop :=
  d.ih ≤ n + 1 ∧ d.wh < s ∧ ∀ j, s ≤ j → d.tape j = M.blank

theorem reachable_good (hM : M.SpaceBounded s) {d : Cfg Λ Γ}
    (hd : Relation.ReflTransGen (M.Step x) M.init d) : M.Good x.length (s x.length) d := by
  induction hd with
  | refl => exact ⟨Nat.zero_le _, hM x _ .refl, fun _ _ => rfl⟩
  | @tail c d hcd hstep ih =>
    have hwh' := hM x d (hcd.tail hstep)
    obtain ⟨t, ht, rfl⟩ := hstep
    obtain ⟨hih, hwh, htape⟩ := ih
    refine ⟨?_, hwh', ?_⟩
    · rcases t with ⟨q, g, di, dw⟩
      cases di <;> simp only [Cfg.next, moveIn] <;> omega
    · intro j hj
      have hne : j ≠ c.wh := by omega
      simp [Cfg.next, hne, htape j hj]

/-! ### Bounded configurations: a finite type -/

/-- Bounded configurations: state, input head, work head, work tape contents. -/
abbrev BCfg (Λ Γ : Type) (n s : ℕ) := Λ × Fin (n + 2) × Fin s × (Fin s → Γ)

/-- Read a bounded configuration as a configuration (blank beyond cell `s`). -/
def toCfg {n s : ℕ} (b : BCfg Λ Γ n s) : Cfg Λ Γ :=
  ⟨b.1, b.2.1, b.2.2.1, fun j => if h : j < s then b.2.2.2 ⟨j, h⟩ else M.blank⟩

theorem exists_toCfg {n s : ℕ} {d : Cfg Λ Γ} (hd : M.Good n s d) :
    ∃ b : BCfg Λ Γ n s, M.toCfg b = d := by
  obtain ⟨hih, hwh, htape⟩ := hd
  refine ⟨(d.q, ⟨d.ih, by omega⟩, ⟨d.wh, hwh⟩, fun j => d.tape j), ?_⟩
  apply Cfg.ext
  · rfl
  · rfl
  · rfl
  · funext j
    show (if h : j < s then d.tape j else M.blank) = d.tape j
    split_ifs with h
    · rfl
    · exact (htape j (by omega)).symm

/-- The step relation restricted to bounded configurations. -/
def BStep {n s : ℕ} (x : List Bool) (b b' : BCfg Λ Γ n s) : Prop :=
  M.Step x (M.toCfg b) (M.toCfg b')

def initB {n s : ℕ} (hs : 0 < s) : BCfg Λ Γ n s :=
  (M.start, ⟨0, by omega⟩, ⟨0, hs⟩, fun _ => M.blank)

theorem toCfg_initB {n s : ℕ} (hs : 0 < s) : M.toCfg (M.initB (n := n) hs) = M.init := by
  apply Cfg.ext
  · rfl
  · rfl
  · rfl
  · funext j
    show (if h : j < s then M.blank else M.blank) = M.blank
    split_ifs <;> rfl

/-- **Acceptance as reachability among bounded configurations.** -/
theorem accepts_iff_bounded (hM : M.SpaceBounded s) (x : List Bool) :
    M.Accepts x ↔ ∃ b : BCfg Λ Γ x.length (s x.length),
      b.1 = M.accept ∧ Relation.ReflTransGen (M.BStep x) (M.initB (hM.pos x)) b := by
  constructor
  · rintro ⟨d, hd, hacc⟩
    have lift : ∀ d, Relation.ReflTransGen (M.Step x) M.init d →
        ∃ b : BCfg Λ Γ x.length (s x.length),
          M.toCfg b = d ∧ Relation.ReflTransGen (M.BStep x) (M.initB (hM.pos x)) b := by
      intro d hd
      induction hd with
      | refl => exact ⟨_, M.toCfg_initB _, .refl⟩
      | @tail c d hcd hstep ih =>
        obtain ⟨b, hb, hpath⟩ := ih
        obtain ⟨b', hb'⟩ := M.exists_toCfg (M.reachable_good hM (hcd.tail hstep))
        refine ⟨b', hb', hpath.tail ?_⟩
        unfold BStep
        rw [hb, hb']
        exact hstep
    obtain ⟨b, hb, hpath⟩ := lift d hd
    have : (M.toCfg b).q = M.accept := hb ▸ hacc
    exact ⟨b, this, hpath⟩
  · rintro ⟨b, hacc, hpath⟩
    have : Relation.ReflTransGen (M.Step x) (M.toCfg (M.initB (hM.pos x))) (M.toCfg b) :=
      hpath.lift M.toCfg (fun _ _ h => h)
    rw [M.toCfg_initB] at this
    exact ⟨_, this, hacc⟩

/-! ### Counting configurations -/

section Counting

variable [Fintype Λ] [Fintype Γ]

theorem card_BCfg (n s : ℕ) :
    Fintype.card (BCfg Λ Γ n s) =
      Fintype.card Λ * ((n + 2) * (s * Fintype.card Γ ^ s)) := by
  simp [BCfg, Fintype.card_prod]

variable (Λ Γ) in
/-- Bits per unit of space: depends only on the machine's state and tape alphabets. -/
def C : ℕ := Nat.clog 2 (Fintype.card Λ) + Nat.clog 2 (Fintype.card Γ) + 4

/-- **Configuration count.** With `log n ≤ s` there are at most `2 ^ (C * s)`
bounded configurations. -/
theorem card_BCfg_le {n s : ℕ} (hlog : Nat.log 2 n ≤ s) (hs : 1 ≤ s) :
    Fintype.card (BCfg Λ Γ n s) ≤ 2 ^ (C Λ Γ * s) := by
  unfold C
  set qa := Nat.clog 2 (Fintype.card Λ)
  set g := Nat.clog 2 (Fintype.card Γ)
  have hΛ : Fintype.card Λ ≤ 2 ^ qa := Nat.le_pow_clog (by decide) _
  have hΓ : Fintype.card Γ ≤ 2 ^ g := Nat.le_pow_clog (by decide) _
  have hn : n + 2 ≤ 2 ^ (s + 2) := by
    have h1 := Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
    have h2 : 2 ^ (Nat.log 2 n).succ ≤ 2 ^ (s + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have h3 : 2 ^ (s + 2) = 2 * 2 ^ (s + 1) := by ring
    have h4 := Nat.two_pow_pos (s + 1)
    omega
  have hsz : s ≤ 2 ^ s := Nat.lt_two_pow_self.le
  have hg : Fintype.card Γ ^ s ≤ 2 ^ (g * s) := by
    rw [Nat.pow_mul]
    exact Nat.pow_le_pow_left hΓ s
  rw [card_BCfg]
  calc Fintype.card Λ * ((n + 2) * (s * Fintype.card Γ ^ s))
      ≤ 2 ^ qa * (2 ^ (s + 2) * (2 ^ s * 2 ^ (g * s))) :=
        Nat.mul_le_mul hΛ (Nat.mul_le_mul hn (Nat.mul_le_mul hsz hg))
    _ = 2 ^ (qa + (s + 2) + (s + g * s)) := by ring
    _ ≤ 2 ^ ((qa + g + 4) * s) := by
        apply Nat.pow_le_pow_right (by decide)
        have e : (qa + g + 4) * s = qa * s + g * s + 4 * s := by ring
        have hq : qa ≤ qa * s := Nat.le_mul_of_pos_right _ hs
        omega

/-! ### Encoding configurations as vertices `Fin (2 ^ w)` -/

/-- Any injection of the bounded configurations into `Fin (2 ^ w)`. -/
noncomputable def encode {n s w : ℕ} (h : Fintype.card (BCfg Λ Γ n s) ≤ 2 ^ w) :
    BCfg Λ Γ n s ↪ Fin (2 ^ w) :=
  ⟨fun b => Fin.castLE h (Fintype.equivFin _ b),
    (Fin.castLE_injective h).comp (Fintype.equivFin _).injective⟩

end Counting

end NTM

/-! ### Transporting reachability along an embedding -/

section MapRel

variable {α β : Type*}

/-- The image of the relation `R` under the embedding `f`. -/
def MapRel (f : α ↪ β) (R : α → α → Prop) (u v : β) : Prop :=
  ∃ a b, f a = u ∧ f b = v ∧ R a b

theorem reflTransGen_mapRel_iff (f : α ↪ β) (R : α → α → Prop) (a : α) (v : β) :
    Relation.ReflTransGen (MapRel f R) (f a) v ↔ ∃ b, f b = v ∧ Relation.ReflTransGen R a b := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨a, rfl, .refl⟩
    | tail _ huv ih =>
      obtain ⟨b, hb, hab⟩ := ih
      obtain ⟨a', b', ha', rfl, hR⟩ := huv
      have : a' = b := f.injective (ha'.trans hb.symm)
      subst this
      exact ⟨b', rfl, hab.tail hR⟩
  · rintro ⟨b, rfl, h⟩
    exact h.lift f (fun x y hxy => ⟨x, y, rfl, rfl, hxy⟩)

end MapRel

namespace NTM

variable (M : NTM Λ Γ) [Fintype Λ] [Fintype Γ] {s : ℕ → ℕ}

/-- **Phase 3 headline.** For a space-bounded NTM and any `w` with enough room,
acceptance of `x` is reachability of an accepting vertex, from the encoded
initial configuration, in the configuration graph on `Fin (2 ^ w)`. -/
theorem accepts_iff_cfgGraph (hM : M.SpaceBounded s) (x : List Bool) {w : ℕ}
    (hcard : Fintype.card (BCfg Λ Γ x.length (s x.length)) ≤ 2 ^ w) :
    M.Accepts x ↔ ∃ v : Fin (2 ^ w),
      (∃ b, encode hcard b = v ∧ b.1 = M.accept) ∧
      Relation.ReflTransGen (MapRel (encode hcard) (M.BStep x))
        (encode hcard (M.initB (hM.pos x))) v := by
  rw [M.accepts_iff_bounded hM x]
  constructor
  · rintro ⟨b, hacc, hp⟩
    exact ⟨_, ⟨b, rfl, hacc⟩, (reflTransGen_mapRel_iff _ _ _ _).2 ⟨b, rfl, hp⟩⟩
  · rintro ⟨v, ⟨b, hb, hacc⟩, hp⟩
    obtain ⟨b', hb', hp'⟩ := (reflTransGen_mapRel_iff _ _ _ _).1 hp
    have : b' = b := (encode hcard).injective (hb'.trans hb.symm)
    exact ⟨b, hacc, this ▸ hp'⟩

/-- The width bound used downstream: `w = C * s |x|` suffices when `log |x| ≤ s |x|`. -/
theorem accepts_iff_cfgGraph_Cs (hM : M.SpaceBounded s) (x : List Bool)
    (hlog : Nat.log 2 x.length ≤ s x.length) :
    M.Accepts x ↔ ∃ v : Fin (2 ^ (C Λ Γ * s x.length)),
      (∃ b, encode (card_BCfg_le hlog (hM.pos x)) b = v ∧ b.1 = M.accept) ∧
      Relation.ReflTransGen (MapRel (encode (card_BCfg_le hlog (hM.pos x))) (M.BStep x))
        (encode (card_BCfg_le hlog (hM.pos x)) (M.initB (hM.pos x))) v :=
  M.accepts_iff_cfgGraph hM x _

end NTM

end Savitch.Machine
