import Savitch.TM.Block

/-!
# Frame rule: code that does not touch a tape leaves it alone

If every `write` / `move` instruction of a block `c` names a tape in `S`, then
running `c` leaves every tape outside `S` exactly as it was (contents and head).
If `c` has no `moveIn`, the input head is unchanged too.

This is proved once, by induction over runs (`Seg.agree`, `Spec.agree`), so that
routine specifications only need to describe the tapes they actually use.
-/

namespace Savitch.TM

variable {k : ℕ} {Γ : Type}

/-- The instruction only writes / moves tapes in `S`. -/
def Instr.Touches (S : Fin k → Prop) : Instr k Γ → Prop
  | .write t _ => S t
  | .move t _ => S t
  | _ => True

/-- The instruction does not move the input head. -/
def Instr.NoIn : Instr k Γ → Prop
  | .moveIn _ => False
  | _ => True

def Code.Touches (c : Code k Γ) (S : Fin k → Prop) : Prop := ∀ i ∈ c, i.Touches S

def Code.NoIn (c : Code k Γ) : Prop := ∀ i ∈ c, i.NoIn

/-- `T'` agrees with `T` on every tape outside `S`. -/
def Tapes.Agree (S : Fin k → Prop) (T T' : Tapes k Γ) : Prop :=
  ∀ t, ¬ S t → T'.tp t = T.tp t ∧ T'.hd t = T.hd t

theorem Tapes.Agree.refl (S : Fin k → Prop) (T : Tapes k Γ) : T.Agree S T :=
  fun _ _ => ⟨rfl, rfl⟩

theorem Tapes.Agree.trans {S : Fin k → Prop} {T T' T'' : Tapes k Γ} (h₁ : T.Agree S T')
    (h₂ : T'.Agree S T'') : T.Agree S T'' :=
  fun t ht => ⟨(h₂ t ht).1.trans (h₁ t ht).1, (h₂ t ht).2.trans (h₁ t ht).2⟩

theorem fetch_mem {c : Code k Γ} {pc : ℤ} {i : Instr k Γ} (h : Code.fetch c pc = some i) :
    i ∈ c := by
  unfold Code.fetch at h
  split_ifs at h
  exact List.mem_of_getElem? h

theorem exec_agree {S : Fin k → Prop} {i : Instr k Γ} (hi : i.Touches S) (x : List Bool)
    (pc : ℤ) (T : Tapes k Γ) : T.Agree S (i.exec x pc T).tapes := by
  intro u hu
  cases i with
  | write t g =>
    have : u ≠ t := fun e => hu (e ▸ hi)
    exact ⟨by simp [Instr.exec, PSt.tapes, Tapes.write, this], rfl⟩
  | move t d =>
    have : u ≠ t := fun e => hu (e ▸ hi)
    exact ⟨rfl, by simp [Instr.exec, PSt.tapes, Tapes.move, this]⟩
  | moveIn d => exact ⟨rfl, rfl⟩
  | jmpIf t p off => exact ⟨rfl, rfl⟩
  | jmpIfIn p off => exact ⟨rfl, rfl⟩
  | halt b => exact ⟨rfl, rfl⟩

theorem exec_ih {i : Instr k Γ} (hi : i.NoIn) (x : List Bool) (pc : ℤ) (T : Tapes k Γ) :
    (i.exec x pc T).tapes.ih = T.ih := by
  cases i with
  | moveIn d => exact absurd hi id
  | _ => rfl

theorem step_agree {S : Fin k → Prop} {c : Code k Γ} (hc : c.Touches S) (x : List Bool)
    (s : PSt k Γ) : s.tapes.Agree S (Code.step c x s).tapes := by
  cases s with
  | run pc T =>
    simp only [Code.step]
    cases h : Code.fetch c pc with
    | none => exact Tapes.Agree.refl S T
    | some i => exact exec_agree (hc i (fetch_mem h)) x pc T
  | halted b T => exact Tapes.Agree.refl S T

theorem step_ih {c : Code k Γ} (hc : c.NoIn) (x : List Bool) (s : PSt k Γ) :
    (Code.step c x s).tapes.ih = s.tapes.ih := by
  cases s with
  | run pc T =>
    simp only [Code.step]
    cases h : Code.fetch c pc with
    | none => rfl
    | some i => exact exec_ih (hc i (fetch_mem h)) x pc T
  | halted b T => rfl

theorem Seg.agree {S : Fin k → Prop} {c : Code k Γ} (hc : c.Touches S) {x : List Bool} {B : ℕ}
    {lo hi : ℤ} {s s' : PSt k Γ} (h : Seg c x B lo hi s s') : s.tapes.Agree S s'.tapes := by
  induction h with
  | refl _ => exact Tapes.Agree.refl S _
  | step _ _ _ _ ih => exact (step_agree hc x _).trans ih

theorem Seg.ih_eq {c : Code k Γ} (hc : c.NoIn) {x : List Bool} {B : ℕ}
    {lo hi : ℤ} {s s' : PSt k Γ} (h : Seg c x B lo hi s s') : s'.tapes.ih = s.tapes.ih := by
  induction h with
  | refl _ => rfl
  | step _ _ _ _ ih => exact ih.trans (step_ih hc x _)

/-- **Frame rule.** A block touching only tapes in `S` preserves all other tapes. -/
theorem Spec.agree {S : Fin k → Prop} {c : Code k Γ} (hc : c.Touches S) {x : List Bool} {B : ℕ}
    {T T' : Tapes k Γ} (h : Spec c x B T T') : T.Agree S T' :=
  Seg.agree hc h

/-- A block without `moveIn` keeps the input head where it was. -/
theorem Spec.ih_eq {c : Code k Γ} (hc : c.NoIn) {x : List Bool} {B : ℕ}
    {T T' : Tapes k Γ} (h : Spec c x B T T') : T'.ih = T.ih :=
  Seg.ih_eq hc h

/-! ### `Touches` / `NoIn` for the combinators -/

section Combinators

variable {S : Fin k → Prop}

theorem Code.Touches.nil : Code.Touches ([] : Code k Γ) S := fun _ h => absurd h List.not_mem_nil

theorem Code.Touches.append {c₁ c₂ : Code k Γ} (h₁ : c₁.Touches S) (h₂ : c₂.Touches S) :
    (c₁ ++ c₂).Touches S := fun i hi => by
  rcases List.mem_append.1 hi with h | h
  · exact h₁ i h
  · exact h₂ i h

theorem Code.Touches.single {i : Instr k Γ} (h : i.Touches S) : Code.Touches [i] S :=
  fun j hj => by rw [List.mem_singleton] at hj; exact hj ▸ h

theorem Code.Touches.jmp (cnd : Cond k Γ) (off : ℤ) : Code.Touches [cnd.jmp off] S :=
  Code.Touches.single (by cases cnd <;> trivial)

theorem Code.Touches.jump (off : ℤ) : Code.Touches [(Instr.jump off : Instr k Γ)] S :=
  Code.Touches.single trivial

theorem Code.Touches.ifElse {cnd : Cond k Γ} {c₁ c₂ : Code k Γ} (h₁ : c₁.Touches S)
    (h₂ : c₂.Touches S) : (ifElse cnd c₁ c₂).Touches S :=
  (((Code.Touches.jmp cnd _).append h₂).append (Code.Touches.jump _)).append h₁

theorem Code.Touches.whileDo {cnd : Cond k Γ} {c : Code k Γ} (h : c.Touches S) :
    (whileDo cnd c).Touches S :=
  ((Code.Touches.jmp cnd.not _).append h).append (Code.Touches.jump _)

theorem Code.Touches.mono {c : Code k Γ} {S S' : Fin k → Prop} (h : c.Touches S)
    (hS : ∀ t, S t → S' t) : c.Touches S' := fun i hi => by
  have := h i hi
  cases i <;> first | exact hS _ this | trivial

theorem Code.NoIn.nil : Code.NoIn ([] : Code k Γ) := fun _ h => absurd h List.not_mem_nil

theorem Code.NoIn.append {c₁ c₂ : Code k Γ} (h₁ : c₁.NoIn) (h₂ : c₂.NoIn) :
    (c₁ ++ c₂).NoIn := fun i hi => by
  rcases List.mem_append.1 hi with h | h
  · exact h₁ i h
  · exact h₂ i h

theorem Code.NoIn.single {i : Instr k Γ} (h : i.NoIn) : Code.NoIn [i] :=
  fun j hj => by rw [List.mem_singleton] at hj; exact hj ▸ h

theorem Code.NoIn.ifElse {cnd : Cond k Γ} {c₁ c₂ : Code k Γ} (h₁ : c₁.NoIn) (h₂ : c₂.NoIn) :
    (ifElse cnd c₁ c₂).NoIn :=
  (((Code.NoIn.single (by cases cnd <;> trivial)).append h₂).append
    (Code.NoIn.single (i := (Instr.jump _ : Instr k Γ)) trivial)).append h₁

theorem Code.NoIn.whileDo {cnd : Cond k Γ} {c : Code k Γ} (h : c.NoIn) : (whileDo cnd c).NoIn :=
  ((Code.NoIn.single (by cases cnd <;> trivial)).append h).append
    (Code.NoIn.single (i := (Instr.jump _ : Instr k Γ)) trivial)

end Combinators

end Savitch.TM
