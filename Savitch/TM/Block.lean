import Savitch.TM.Prog

/-!
# Verified composition of tape programs

Building blocks for writing the Savitch TM as a structured program:

* `Seg P x B lo hi s t`: running `P` on input `x` goes from `s` to `t`, every
  intermediate program counter stays in `[lo, hi)`, and every visited state
  (both endpoints included) keeps all work heads below `B`.
* `Spec c x B T T'`: block `c`, started at its first instruction on tapes `T`,
  exits at its end with tapes `T'`, staying within space `B`.
* `SubAt P c o`: block `c` occurs inside `P` at offset `o`. Because jumps are
  relative, `Seg.embed` transports any run of `c` into `P`.

Combinators with proved specifications:
* `Spec.seq`: `c₁ ++ c₂`.
* `Spec.ifElse_true`, `Spec.ifElse_false`: `ifElse cnd c₁ c₂`.
* `Spec.whileDo`: `whileDo cnd body`, from a `Loop` derivation.

`Seg.reachable` converts a halting run into a bound on *every* reachable state,
which is what `Code.mem_DSPACE` needs.
-/

namespace Savitch.TM

open Machine (Dir inputSym)

variable {k : ℕ} {Γ : Type}

/-! ### Conditions -/

/-- A test on the symbol under one head. -/
inductive Cond (k : ℕ) (Γ : Type) where
  | tape (t : Fin k) (p : Γ → Bool)
  | input (p : Option Bool → Bool)

def Cond.eval (x : List Bool) (T : Tapes k Γ) : Cond k Γ → Bool
  | .tape t p => p (T.read t)
  | .input p => p (inputSym x T.ih)

def Cond.not : Cond k Γ → Cond k Γ
  | .tape t p => .tape t (fun g => !p g)
  | .input p => .input (fun i => !p i)

theorem Cond.eval_not (x : List Bool) (T : Tapes k Γ) (c : Cond k Γ) :
    c.not.eval x T = !c.eval x T := by
  cases c <;> rfl

/-- Jump by `off` if the condition holds. -/
def Cond.jmp (off : ℤ) : Cond k Γ → Instr k Γ
  | .tape t p => .jmpIf t p off
  | .input p => .jmpIfIn p off

theorem Cond.exec_jmp (x : List Bool) (pc : ℤ) (T : Tapes k Γ) (off : ℤ) (c : Cond k Γ) :
    (c.jmp off).exec x pc T = .run (if c.eval x T then pc + off else pc + 1) T := by
  cases c <;> rfl

theorem exec_jump (x : List Bool) (pc : ℤ) (T : Tapes k Γ) (off : ℤ) :
    (Instr.jump off : Instr k Γ).exec x pc T = .run (pc + off) T := rfl

/-! ### Fetching inside concatenations -/

theorem fetch_left (c₁ c₂ : Code k Γ) {pc : ℤ} (h0 : 0 ≤ pc) (h1 : pc < c₁.length) :
    Code.fetch (c₁ ++ c₂) pc = Code.fetch c₁ pc := by
  simp only [Code.fetch, h0, ↓reduceIte]
  exact List.getElem?_append_left (by omega)

theorem fetch_right (c₁ c₂ : Code k Γ) {pc : ℤ} (h0 : 0 ≤ pc) :
    Code.fetch (c₁ ++ c₂) (c₁.length + pc) = Code.fetch c₂ pc := by
  simp only [Code.fetch, h0, show (0 : ℤ) ≤ c₁.length + pc by omega, ↓reduceIte]
  rw [show ((c₁.length : ℤ) + pc).toNat = c₁.length + pc.toNat by omega,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

/-- Block `c` occurs in program `P` at offset `o`. -/
def SubAt (P c : Code k Γ) (o : ℤ) : Prop :=
  ∀ pc : ℤ, 0 ≤ pc → pc < c.length → Code.fetch P (o + pc) = Code.fetch c pc

theorem SubAt.self (P : Code k Γ) : SubAt P P 0 := fun pc _ _ => by rw [zero_add]

theorem SubAt.left {P c₁ c₂ : Code k Γ} {o : ℤ} (h : SubAt P (c₁ ++ c₂) o) : SubAt P c₁ o :=
  fun pc h0 h1 => by
    rw [h pc h0 (by simp; omega), fetch_left _ _ h0 h1]

theorem SubAt.right {P c₁ c₂ : Code k Γ} {o : ℤ} (h : SubAt P (c₁ ++ c₂) o) :
    SubAt P c₂ (o + c₁.length) :=
  fun pc h0 h1 => by
    rw [add_assoc, h _ (by omega) (by simp; omega), fetch_right _ _ h0]

theorem SubAt.single {P : Code k Γ} {i : Instr k Γ} {o : ℤ} (h : SubAt P [i] o) :
    Code.fetch P o = some i := by
  have := h 0 le_rfl (by simp)
  rw [add_zero] at this
  rw [this]
  rfl

/-! ### Shifting program counters -/

def PSt.shift (o : ℤ) : PSt k Γ → PSt k Γ
  | .run pc T => .run (o + pc) T
  | .halted b T => .halted b T

theorem PSt.shift_tapes (o : ℤ) (s : PSt k Γ) : (s.shift o).tapes = s.tapes := by
  cases s <;> rfl

theorem exec_shift (x : List Bool) (o pc : ℤ) (T : Tapes k Γ) (i : Instr k Γ) :
    i.exec x (o + pc) T = (i.exec x pc T).shift o := by
  cases i <;> simp only [Instr.exec, PSt.shift] <;> (try split_ifs) <;>
    (congr 1; omega)

theorem step_sub {P c : Code k Γ} {o : ℤ} (h : SubAt P c o) (x : List Bool) {pc : ℤ}
    (T : Tapes k Γ) (h0 : 0 ≤ pc) (h1 : pc < c.length) :
    Code.step P x (.run (o + pc) T) = (Code.step c x (.run pc T)).shift o := by
  obtain ⟨i, hi⟩ : ∃ i, Code.fetch c pc = some i := ⟨_, fetch_eq_some ⟨h0, by omega⟩⟩
  simp only [Code.step, h pc h0 h1, hi, exec_shift]

/-! ### Space-bounded segments of a run -/

inductive Seg (P : Code k Γ) (x : List Bool) (B : ℕ) (lo hi : ℤ) : PSt k Γ → PSt k Γ → Prop
  | refl {s} : s.tapes.Within B → Seg P x B lo hi s s
  | step {pc T s} : lo ≤ pc → pc < hi → T.Within B →
      Seg P x B lo hi (Code.step P x (.run pc T)) s → Seg P x B lo hi (.run pc T) s

namespace Seg

variable {P : Code k Γ} {x : List Bool} {B : ℕ} {lo hi : ℤ} {s t u : PSt k Γ}

theorem trans (h₁ : Seg P x B lo hi s t) (h₂ : Seg P x B lo hi t u) : Seg P x B lo hi s u := by
  revert h₂
  induction h₁ with
  | refl _ => exact id
  | step hl hh hT _ ih => exact fun h₂ => .step hl hh hT (ih h₂)

theorem mono {lo' hi' : ℤ} (h : Seg P x B lo hi s t) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    Seg P x B lo' hi' s t := by
  induction h with
  | refl hT => exact .refl hT
  | step hl hh hT _ ih => exact .step (by omega) (by omega) hT ih

theorem target_within (h : Seg P x B lo hi s t) : t.tapes.Within B := by
  induction h with
  | refl hT => exact hT
  | step _ _ _ _ ih => exact ih

theorem toReflTransGen (h : Seg P x B lo hi s t) :
    Relation.ReflTransGen (Code.StepRel P x) s t := by
  induction h with
  | refl _ => exact .refl
  | step _ _ _ _ ih => exact ih.head rfl

/-- Rewrite the program counters of a segment's endpoints. -/
theorem of_eq {p p' q q' : ℤ} {T T' : Tapes k Γ}
    (h : Seg P x B lo hi (.run p T) (.run q T')) (hp : p = p') (hq : q = q') :
    Seg P x B lo hi (.run p' T) (.run q' T') := by
  subst hp hq; exact h

theorem refl_of_eq {p q : ℤ} {T : Tapes k Γ} (h : p = q) (hT : T.Within B) :
    Seg P x B lo hi (.run p T) (.run q T) := by
  subst h; exact .refl hT

/-- Transport a run of block `c` into a program `P` containing it at offset `o`. -/
theorem embed {c : Code k Γ} {o : ℤ} (hsub : SubAt P c o) {s t : PSt k Γ}
    (h : Seg c x B lo hi s t) (hlo : 0 ≤ lo) (hhi : hi ≤ c.length) :
    Seg P x B (o + lo) (o + hi) (s.shift o) (t.shift o) := by
  induction h with
  | refl hT => exact .refl (by rw [PSt.shift_tapes]; exact hT)
  | @step pc T s hl hh hT _ ih =>
    refine .step (by omega) (by omega) hT ?_
    rw [step_sub hsub x T (by omega) (by omega)]
    exact ih

theorem fixed_reach (hfix : Code.step P x t = t) {u : PSt k Γ}
    (hu : Relation.ReflTransGen (Code.StepRel P x) t u) : u = t := by
  induction hu with
  | refl => rfl
  | tail _ hyz ih => rw [← hyz, ih, hfix]

/-- Determinism: a bounded run ending in a fixed point bounds every reachable state. -/
theorem reachable (h : Seg P x B lo hi s t) (hfix : Code.step P x t = t) :
    ∀ u, Relation.ReflTransGen (Code.StepRel P x) s u → u.tapes.Within B := by
  induction h with
  | refl hT =>
    intro u hu
    rw [fixed_reach hfix hu]
    exact hT
  | step _ _ hT _ ih =>
    intro u hu
    rcases Relation.ReflTransGen.cases_head hu with rfl | ⟨v, hv, hvu⟩
    · exact hT
    · exact ih hfix u (hv ▸ hvu)

end Seg

/-! ### Block specifications and combinators -/

/-- Block `c` takes tapes `T` to `T'` in space `B`, entering at its first
instruction and leaving just past its last. -/
def Spec (c : Code k Γ) (x : List Bool) (B : ℕ) (T T' : Tapes k Γ) : Prop :=
  Seg c x B 0 c.length (.run 0 T) (.run c.length T')

/-- Run a block that sits inside `P` at offset `o`. -/
theorem Spec.embed {P c : Code k Γ} {o : ℤ} {x : List Bool} {B : ℕ} {T T' : Tapes k Γ}
    (hsub : SubAt P c o) (h : Spec c x B T T') :
    Seg P x B o (o + c.length) (.run o T) (.run (o + c.length) T') := by
  have := Seg.embed hsub h le_rfl le_rfl
  simp only [PSt.shift, add_zero] at this
  exact this

theorem Spec.seq {c₁ c₂ : Code k Γ} {x : List Bool} {B : ℕ} {T T' T'' : Tapes k Γ}
    (h₁ : Spec c₁ x B T T') (h₂ : Spec c₂ x B T' T'') : Spec (c₁ ++ c₂) x B T T'' := by
  have hs := SubAt.self (c₁ ++ c₂)
  have a := Spec.embed hs.left h₁
  have b := Spec.embed hs.right h₂
  unfold Spec
  rw [List.length_append, Nat.cast_add]
  rw [zero_add] at a b
  exact (a.mono le_rfl (by omega)).trans (b.mono (by omega) (by omega))

/-- `if cnd then c₁ else c₂`. -/
def ifElse (cnd : Cond k Γ) (c₁ c₂ : Code k Γ) : Code k Γ :=
  [cnd.jmp (c₂.length + 2)] ++ c₂ ++ [Instr.jump (c₁.length + 1)] ++ c₁

theorem Spec.ifElse_true {cnd : Cond k Γ} {c₁ c₂ : Code k Γ} {x : List Bool} {B : ℕ}
    {T T' : Tapes k Γ} (hc : cnd.eval x T = true) (hT : T.Within B) (h : Spec c₁ x B T T') :
    Spec (ifElse cnd c₁ c₂) x B T T' := by
  have hs := SubAt.self (ifElse cnd c₁ c₂)
  unfold ifElse at hs
  have hj := hs.left.left.left.single
  have b := Spec.embed hs.right h
  unfold Spec ifElse
  simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one] at b ⊢
  refine .step le_rfl (by omega) hT ?_
  simp only [Code.step, hj, Cond.exec_jmp, hc, ↓reduceIte]
  exact (b.of_eq (by omega) (by omega)).mono (by omega) (by omega)

theorem Spec.ifElse_false {cnd : Cond k Γ} {c₁ c₂ : Code k Γ} {x : List Bool} {B : ℕ}
    {T T' : Tapes k Γ} (hc : cnd.eval x T = false) (hT : T.Within B) (h : Spec c₂ x B T T') :
    Spec (ifElse cnd c₁ c₂) x B T T' := by
  have hs := SubAt.self (ifElse cnd c₁ c₂)
  unfold ifElse at hs
  have hj := hs.left.left.left.single
  have hjump := hs.left.right.single
  have b := Spec.embed hs.left.left.right h
  have hT' := b.target_within
  unfold Spec ifElse
  simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one] at b hjump ⊢
  refine .step le_rfl (by omega) hT ?_
  simp only [Code.step, hj, Cond.exec_jmp, hc, Bool.false_eq_true, ↓reduceIte, zero_add]
  refine (b.of_eq (p' := 1) (q' := 1 + (c₂.length : ℤ)) (by omega) (by omega)).mono
    (by omega) (by omega) |>.trans ?_
  refine .step (pc := 1 + (c₂.length : ℤ)) (by omega) (by omega) hT' ?_
  rw [zero_add] at hjump
  simp only [Code.step, hjump, exec_jump]
  exact Seg.refl_of_eq (by omega) hT'

/-- `while cnd do body`. -/
def whileDo (cnd : Cond k Γ) (body : Code k Γ) : Code k Γ :=
  [cnd.not.jmp (body.length + 2)] ++ body ++ [Instr.jump (-(body.length + 1 : ℤ))]

/-- A terminating execution of a loop: a finite chain of body runs, each started
while the condition holds, ending in a state where it fails. -/
inductive Loop (cnd : Cond k Γ) (body : Code k Γ) (x : List Bool) (B : ℕ) :
    Tapes k Γ → Tapes k Γ → Prop
  | stop {T} : cnd.eval x T = false → T.Within B → Loop cnd body x B T T
  | iter {T T' T''} : cnd.eval x T = true → T.Within B → Spec body x B T T' →
      Loop cnd body x B T' T'' → Loop cnd body x B T T''

theorem Spec.whileDo {cnd : Cond k Γ} {body : Code k Γ} {x : List Bool} {B : ℕ}
    {T T' : Tapes k Γ} (h : Loop cnd body x B T T') : Spec (TM.whileDo cnd body) x B T T' := by
  have hs := SubAt.self (TM.whileDo cnd body)
  unfold TM.whileDo at hs
  have hj := hs.left.left.single
  have hjump := hs.right.single
  simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one,
    zero_add] at hjump
  induction h with
  | stop hc hT =>
    unfold Spec TM.whileDo
    simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
    refine .step le_rfl (by omega) hT ?_
    simp only [Code.step, hj, Cond.exec_jmp, Cond.eval_not, hc, Bool.not_false, ↓reduceIte,
      zero_add]
    exact Seg.refl_of_eq (by omega) hT
  | iter hc hT hbody _ ih =>
    have b := Spec.embed hs.left.right hbody
    have hT' := b.target_within
    unfold Spec TM.whileDo at ih ⊢
    simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]
      at b ih ⊢
    refine .step le_rfl (by omega) hT ?_
    simp only [Code.step, hj, Cond.exec_jmp, Cond.eval_not, hc, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte, zero_add]
    refine (b.of_eq (p' := 1) (q' := 1 + (body.length : ℤ)) (by omega) (by omega)).mono
      (by omega) (by omega) |>.trans ?_
    refine .step (pc := 1 + (body.length : ℤ)) (by omega) (by omega) hT' ?_
    simp only [Code.step, hjump, exec_jump]
    exact ih.of_eq (by omega) rfl

end Savitch.TM
