import Savitch.TM.DTM

/-!
# A tape assembly language that compiles to DTMs

Writing TM transition tables by hand is impractical. Instead we write programs
in a tiny assembly language whose every instruction is **one TM step** on a
single tape:

* `write t g`: write `g` under the head of work tape `t`;
* `move t d` / `moveIn d`: move the head of work tape `t` / of the input tape;
* `jmpIf t p off` / `jmpIfIn p off`: if `p` holds of the symbol under the head,
  jump by the relative offset `off`, else fall through;
* `halt b`: stop with answer `b`.

Jumps are **relative**, so code blocks can be concatenated without relocation
(see `Savitch/TM/Block.lean`).

Main result: `Code.mem_DSPACE`. A program that halts with the right answer on
every input, and keeps its heads below `c * (f n + 1)`, puts its language in
`DSPACE f`. The proof compiles the program to a DTM (`Code.toDTM`) whose states
are program counters, and shows that the compiled machine simulates the
program **step for step** (`Code.step_enc`).
-/

namespace Savitch.TM

open Machine (Dir inputSym moveIn moveWork)

variable {k : ℕ} {Γ : Type}

namespace Tapes

def write (T : Tapes k Γ) (t : Fin k) (g : Γ) : Tapes k Γ :=
  { T with tp := Function.update T.tp t (Function.update (T.tp t) (T.hd t) g) }

def move (T : Tapes k Γ) (t : Fin k) (d : Dir) : Tapes k Γ :=
  { T with hd := Function.update T.hd t (moveWork (T.hd t) d) }

def moveInput (n : ℕ) (T : Tapes k Γ) (d : Dir) : Tapes k Γ :=
  { T with ih := moveIn n T.ih d }

end Tapes

inductive Instr (k : ℕ) (Γ : Type) where
  | write (t : Fin k) (g : Γ)
  | move (t : Fin k) (d : Dir)
  | moveIn (d : Dir)
  | jmpIf (t : Fin k) (p : Γ → Bool) (off : ℤ)
  | jmpIfIn (p : Option Bool → Bool) (off : ℤ)
  | halt (b : Bool)

/-- Unconditional relative jump. -/
def Instr.jump (off : ℤ) : Instr k Γ := .jmpIfIn (fun _ => true) off

abbrev Code (k : ℕ) (Γ : Type) := List (Instr k Γ)

/-- Program state: running at program counter `pc`, or halted with an answer. -/
inductive PSt (k : ℕ) (Γ : Type) where
  | run (pc : ℤ) (T : Tapes k Γ)
  | halted (b : Bool) (T : Tapes k Γ)

def PSt.tapes : PSt k Γ → Tapes k Γ
  | .run _ T => T
  | .halted _ T => T

def Instr.exec (x : List Bool) (pc : ℤ) (T : Tapes k Γ) : Instr k Γ → PSt k Γ
  | .write t g => .run (pc + 1) (T.write t g)
  | .move t d => .run (pc + 1) (T.move t d)
  | .moveIn d => .run (pc + 1) (T.moveInput x.length d)
  | .jmpIf t p off => .run (if p (T.read t) then pc + off else pc + 1) T
  | .jmpIfIn p off => .run (if p (inputSym x T.ih) then pc + off else pc + 1) T
  | .halt b => .halted b T

/-- The instruction at `pc`, if `pc` is in range. -/
def Code.fetch (P : Code k Γ) (pc : ℤ) : Option (Instr k Γ) :=
  if 0 ≤ pc then P[pc.toNat]? else none

/-- One program step. Out-of-range program counters and halted states are fixed points. -/
def Code.step (P : Code k Γ) (x : List Bool) : PSt k Γ → PSt k Γ
  | .run pc T =>
    match Code.fetch P pc with
    | some i => i.exec x pc T
    | none => .run pc T
  | .halted b T => .halted b T

def Code.StepRel (P : Code k Γ) (x : List Bool) (s t : PSt k Γ) : Prop := Code.step P x s = t

/-! ### Compilation to a DTM -/

/-- DTM states: a program counter in range, "stuck" (`none`), or halted. -/
abbrev Code.Q (P : Code k Γ) := Option (Fin P.length) ⊕ Bool

def Code.pcState (P : Code k Γ) (pc : ℤ) : Option (Fin P.length) :=
  if h : 0 ≤ pc ∧ pc.toNat < P.length then some ⟨pc.toNat, h.2⟩ else none

def stayAll : Fin k → Dir := fun _ => .stay

def Code.δ (P : Code k Γ) (q : Code.Q P) (inp : Option Bool) (r : Fin k → Γ) :
    Code.Q P × (Fin k → Γ) × Dir × (Fin k → Dir) :=
  match q with
  | .inl (some i) =>
    match P.get i with
    | .write t g => (.inl (Code.pcState P ((i : ℕ) + 1)), Function.update r t g, .stay, stayAll)
    | .move t d => (.inl (Code.pcState P ((i : ℕ) + 1)), r, .stay, Function.update stayAll t d)
    | .moveIn d => (.inl (Code.pcState P ((i : ℕ) + 1)), r, d, stayAll)
    | .jmpIf t p off =>
      (.inl (Code.pcState P (if p (r t) then ((i : ℕ) : ℤ) + off else (i : ℕ) + 1)),
        r, .stay, stayAll)
    | .jmpIfIn p off =>
      (.inl (Code.pcState P (if p inp then ((i : ℕ) : ℤ) + off else (i : ℕ) + 1)),
        r, .stay, stayAll)
    | .halt b => (.inr b, r, .stay, stayAll)
  | .inl none => (.inl none, r, .stay, stayAll)
  | .inr b => (.inr b, r, .stay, stayAll)

/-- The DTM whose states are the program counters of `P`. -/
def Code.toDTM (P : Code k Γ) (g : Γ) : DTM k (Code.Q P) Γ where
  blank := g
  start := .inl (Code.pcState P 0)
  halt := fun q => match q with
    | .inr b => some b
    | .inl _ => none
  δ := Code.δ P

def Code.enc (P : Code k Γ) : PSt k Γ → DCfg k (Code.Q P) Γ
  | .run pc T => ⟨.inl (Code.pcState P pc), T⟩
  | .halted b T => ⟨.inr b, T⟩

theorem Code.enc_T (P : Code k Γ) (s : PSt k Γ) : (Code.enc P s).T = s.tapes := by
  cases s <;> rfl

/-- Writing back what was read changes nothing. -/
theorem tapes_stay (T : Tapes k Γ) (n : ℕ) :
    (⟨moveIn n T.ih .stay, fun i => moveWork (T.hd i) .stay,
      fun i => Function.update (T.tp i) (T.hd i) (T.read i)⟩ : Tapes k Γ) = T := by
  ext i <;> simp [moveIn, moveWork, Tapes.read]

theorem fetch_eq_some {P : Code k Γ} {pc : ℤ} (h : 0 ≤ pc ∧ pc.toNat < P.length) :
    Code.fetch P pc = some (P.get ⟨pc.toNat, h.2⟩) := by
  simp [Code.fetch, h.1, h.2]

theorem fetch_eq_none {P : Code k Γ} {pc : ℤ} (h : ¬ (0 ≤ pc ∧ pc.toNat < P.length)) :
    Code.fetch P pc = none := by
  unfold Code.fetch
  split_ifs with h0
  · exact List.getElem?_eq_none (by omega)
  · rfl

theorem dcfg_eq {Λ : Type} {q q' : Λ} {T T' : Tapes k Γ} (hq : q = q') (hT : T = T') :
    (⟨q, T⟩ : DCfg k Λ Γ) = ⟨q', T'⟩ := by
  subst hq hT; rfl

/-- **Step-for-step simulation**: the compiled DTM tracks the program exactly. -/
theorem Code.step_enc (P : Code k Γ) (g : Γ) (x : List Bool) (s : PSt k Γ) :
    (Code.toDTM P g).step x (Code.enc P s) = Code.enc P (Code.step P x s) := by
  cases s with
  | halted b T => rfl
  | run pc T =>
    by_cases h : 0 ≤ pc ∧ pc.toNat < P.length
    · have hpc : Code.pcState P pc = some ⟨pc.toNat, h.2⟩ := by simp [Code.pcState, h]
      have hz : ((pc.toNat : ℕ) : ℤ) = pc := Int.toNat_of_nonneg h.1
      have hf := fetch_eq_some h
      cases hins : P.get ⟨pc.toNat, h.2⟩ with
      | write t g' =>
        simp only [Code.step, hf, hins, Code.enc, DTM.step, Code.toDTM, hpc, Code.δ,
          Instr.exec, hz]
        apply dcfg_eq rfl
        ext i j
        · rfl
        · simp [moveWork, Tapes.write, stayAll]
        · by_cases hi : i = t
          · subst hi; simp [Tapes.write]
          · simp only [Tapes.write, Function.update_apply, hi, Tapes.read, ite_false]
            split_ifs with hj
            · rw [hj]
            · rfl
      | move t d =>
        simp only [Code.step, hf, hins, Code.enc, DTM.step, Code.toDTM, hpc, Code.δ,
          Instr.exec, hz]
        apply dcfg_eq rfl
        ext i j
        · rfl
        · by_cases hi : i = t
          · subst hi; simp [Tapes.move]
          · simp [Tapes.move, hi, stayAll, moveWork]
        · simp [Tapes.move, Tapes.read]
      | moveIn d =>
        simp only [Code.step, hf, hins, Code.enc, DTM.step, Code.toDTM, hpc, Code.δ,
          Instr.exec, hz]
        apply dcfg_eq rfl
        ext i j
        · rfl
        · simp [Tapes.moveInput, stayAll, moveWork]
        · simp [Tapes.moveInput, Tapes.read]
      | jmpIf t p off =>
        simp only [Code.step, hf, hins, Code.enc, DTM.step, Code.toDTM, hpc, Code.δ,
          Instr.exec, hz]
        apply dcfg_eq
        · simp only [Tapes.read]
        · exact tapes_stay T x.length
      | jmpIfIn p off =>
        simp only [Code.step, hf, hins, Code.enc, DTM.step, Code.toDTM, hpc, Code.δ,
          Instr.exec, hz]
        apply dcfg_eq
        · split_ifs <;> rfl
        · exact tapes_stay T x.length
      | halt b =>
        simp only [Code.step, hf, hins, Code.enc, DTM.step, Code.toDTM, hpc, Code.δ,
          Instr.exec]
        exact dcfg_eq rfl (tapes_stay T x.length)
    · have hpc : Code.pcState P pc = none := by simp [Code.pcState, h]
      simp only [Code.step, fetch_eq_none h, Code.enc, DTM.step, Code.toDTM, hpc, Code.δ]
      exact dcfg_eq rfl (tapes_stay T x.length)

theorem Code.reach_enc (P : Code k Γ) (g : Γ) (x : List Bool) {s t : PSt k Γ}
    (h : Relation.ReflTransGen (Code.StepRel P x) s t) :
    Relation.ReflTransGen ((Code.toDTM P g).StepRel x) (Code.enc P s) (Code.enc P t) :=
  h.lift _ (fun a b hab => by
    show (Code.toDTM P g).step x (Code.enc P a) = Code.enc P b
    rw [Code.step_enc]
    exact congrArg _ hab)

theorem Code.reach_dtm (P : Code k Γ) (g : Γ) (x : List Bool) {s : PSt k Γ}
    {d : DCfg k (Code.Q P) Γ}
    (h : Relation.ReflTransGen ((Code.toDTM P g).StepRel x) (Code.enc P s) d) :
    ∃ t, Relation.ReflTransGen (Code.StepRel P x) s t ∧ Code.enc P t = d := by
  induction h with
  | refl => exact ⟨s, .refl, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨t, ht, rfl⟩ := ih
    exact ⟨Code.step P x t, ht.tail rfl, by rw [← Code.step_enc P g]; exact hstep⟩

/-- **Programs are Turing machines.** A program that halts with the right answer on
every input and keeps every work head below `c * (f n + 1)` decides a language in
`DSPACE f`. -/
theorem Code.mem_DSPACE [Fintype Γ] (P : Code k Γ) (g : Γ) {f : ℕ → ℕ} {L : Set (List Bool)}
    (c : ℕ)
    (hspace : ∀ x s, Relation.ReflTransGen (Code.StepRel P x) (.run 0 (Tapes.blank g)) s →
      s.tapes.Within (c * (f x.length + 1)))
    (hdec : ∀ x, ∃ b T, Relation.ReflTransGen (Code.StepRel P x) (.run 0 (Tapes.blank g))
      (.halted b T) ∧ (b = true ↔ x ∈ L)) :
    L ∈ DSPACE f := by
  refine ⟨k, Code.Q P, Γ, inferInstance, inferInstance, Code.toDTM P g, c, ?_, ?_⟩
  · intro x d hd
    obtain ⟨t, ht, rfl⟩ := Code.reach_dtm P g x (s := .run 0 (Tapes.blank g)) hd
    rw [Code.enc_T]
    exact hspace x t ht
  · intro x
    obtain ⟨b, T, h, hb⟩ := hdec x
    exact ⟨b, ⟨_, Code.reach_enc P g x h, rfl⟩, hb⟩

end Savitch.TM
