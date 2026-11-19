import Savitch.TM.Macros

/-!
# Binary blocks on tapes

Phase 4b-2 (continued) of the Savitch formalization (see `PLAN.md`).

Vertices of the Phase 2 machine are numbers `< 2 ^ w`. On tape, a vertex is a
block of `w` cells holding its bits **little-endian**, written with two
designated symbols `z` (bit 0) and `o` (bit 1).

Pure part:
* `bval l`: the value of a little-endian bit list; `bval_lt`, `bval_inj`.
* `binc l`: increment; `bval_binc` shows it adds one (when there is room).

Tape part:
* `seg f s n`: the list of `n` cells of tape contents `f` starting at `s`.
* `incr t z o`: in-place increment of the block under head `t`
  (`Spec.incr`: the block afterwards holds `binc l`, nothing else changes).
-/

namespace Savitch.TM

/-! ### Little-endian binary numbers -/

def bval : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat + 2 * bval l

def binc : List Bool → List Bool
  | [] => []
  | true :: l => false :: binc l
  | false :: l => true :: l

theorem binc_length : ∀ l : List Bool, (binc l).length = l.length
  | [] => rfl
  | true :: l => by simp [binc, binc_length l]
  | false :: l => rfl

theorem bval_lt : ∀ l : List Bool, bval l < 2 ^ l.length
  | [] => by simp [bval]
  | b :: l => by
    have := bval_lt l
    cases b <;> simp [bval, Nat.pow_succ] <;> omega

theorem bval_binc : ∀ l : List Bool, bval l + 1 < 2 ^ l.length → bval (binc l) = bval l + 1
  | [], h => by simp [bval] at h
  | true :: l, h => by
    have ih := bval_binc l (by simp [bval, Nat.pow_succ] at h; omega)
    simp [binc, bval, ih]; omega
  | false :: l, _ => by simp [binc, bval]; omega

theorem bval_inj : ∀ {l₁ l₂ : List Bool}, l₁.length = l₂.length → bval l₁ = bval l₂ → l₁ = l₂
  | [], [], _, _ => rfl
  | b₁ :: l₁, b₂ :: l₂, hl, h => by
    have hb : b₁ = b₂ := by
      cases b₁ <;> cases b₂ <;> simp [bval] at h ⊢ <;> omega
    subst hb
    have : bval l₁ = bval l₂ := by simp [bval] at h; omega
    rw [bval_inj (by simpa using hl) this]

theorem bval_replicate_false : ∀ n, bval (List.replicate n false) = 0
  | 0 => rfl
  | n + 1 => by simp [List.replicate_succ, bval, bval_replicate_false n]

/-! ### Segments of tape -/

variable {k : ℕ} {Γ : Type}

/-- The `n` cells of `f` starting at position `s`. -/
def seg (f : ℕ → Γ) : ℕ → ℕ → List Γ
  | _, 0 => []
  | s, n + 1 => f s :: seg f (s + 1) n

theorem seg_congr {f g : ℕ → Γ} : ∀ {s n : ℕ}, (∀ j, s ≤ j → j < s + n → f j = g j) →
    seg f s n = seg g s n
  | _, 0, _ => rfl
  | s, n + 1, h => by
    simp only [seg]
    rw [h s le_rfl (by omega), seg_congr (fun j h1 h2 => h j (by omega) (by omega))]

theorem seg_length (f : ℕ → Γ) : ∀ s n, (seg f s n).length = n
  | _, 0 => rfl
  | s, n + 1 => by simp [seg, seg_length f (s + 1) n]

theorem ite_neg' {α : Type} {p : Prop} [Decidable p] (h : ¬p) (a b : α) :
    (if p then a else b) = b := by simp [h]

theorem ite_pos' {α : Type} {p : Prop} [Decidable p] (h : p) (a b : α) :
    (if p then a else b) = a := by simp [h]

/-! ### Frame conditions -/

/-- `T'` differs from `T` at most on tape `t` (contents and head). -/
def Tapes.Frame (t : Fin k) (T T' : Tapes k Γ) : Prop :=
  T'.ih = T.ih ∧ ∀ i, i ≠ t → T'.tp i = T.tp i ∧ T'.hd i = T.hd i

theorem Tapes.Frame.refl (t : Fin k) (T : Tapes k Γ) : T.Frame t T := ⟨rfl, fun _ _ => ⟨rfl, rfl⟩⟩

theorem Tapes.Frame.trans {t : Fin k} {T T' T'' : Tapes k Γ} (h₁ : T.Frame t T')
    (h₂ : T'.Frame t T'') : T.Frame t T'' :=
  ⟨h₂.1.trans h₁.1, fun i hi => ⟨(h₂.2 i hi).1.trans (h₁.2 i hi).1,
    (h₂.2 i hi).2.trans (h₁.2 i hi).2⟩⟩

theorem Tapes.Frame.write (t : Fin k) (T : Tapes k Γ) (g : Γ) : T.Frame t (T.write t g) :=
  ⟨rfl, fun i hi => ⟨by simp [Tapes.write, hi], rfl⟩⟩

theorem Tapes.Frame.setHead (t : Fin k) (T : Tapes k Γ) (n : ℕ) : T.Frame t (T.setHead t n) :=
  ⟨rfl, fun _ hi => ⟨rfl, Tapes.setHead_hd_ne T t hi n⟩⟩

theorem Tapes.write_tp_self (T : Tapes k Γ) (t : Fin k) (g : Γ) (j : ℕ) :
    (T.write t g).tp t j = if j = T.hd t then g else T.tp t j := by
  simp [Tapes.write, Function.update_apply]

/-! ### In-place increment -/

section Incr

variable [DecidableEq Γ] {x : List Bool} {B : ℕ}

/-- The tape symbol of a bit. -/
def bsym (z o : Γ) (b : Bool) : Γ := if b then o else z

/-- Increment the little-endian binary block under head `t`. The head ends
somewhere inside the block (the caller rewinds it). -/
def incr (t : Fin k) (z o : Γ) : Code k Γ :=
  whileDo (.tape t (fun g => decide (g = o))) ([Instr.write t z] ++ [Instr.move t .right]) ++
    ifElse (.tape t (fun g => decide (g = z))) [Instr.write t o] []

/-- What `incr` guarantees, for a block holding `l`. -/
def IncrPost (t : Fin k) (z o : Γ) (l : List Bool) (T T' : Tapes k Γ) : Prop :=
  seg (T'.tp t) (T.hd t) l.length = (binc l).map (bsym z o) ∧
  (∀ j, (j < T.hd t ∨ T.hd t + l.length ≤ j) → T'.tp t j = T.tp t j) ∧
  T.Frame t T' ∧ T'.hd t ≤ T.hd t + l.length

theorem incr_aux (t : Fin k) (z o : Γ) (hzo : z ≠ o) :
    ∀ (l : List Bool) (T : Tapes k Γ),
      seg (T.tp t) (T.hd t) l.length = l.map (bsym z o) →
      T.tp t (T.hd t + l.length) ≠ z → T.tp t (T.hd t + l.length) ≠ o →
      T.Within B → T.hd t + l.length < B →
      ∃ Tm T', Loop (.tape t (fun g => decide (g = o)))
          ([Instr.write t z] ++ [Instr.move t .right]) x B T Tm ∧
        Spec (ifElse (.tape t (fun g => decide (g = z))) [Instr.write t o] []) x B Tm T' ∧
        IncrPost t z o l T T'
  | [], T, _, hz, ho, hT, _ => by
    refine ⟨T, T, .stop (decide_eq_false (by simpa [Tapes.read] using ho)) hT,
      Spec.ifElse_false (decide_eq_false (by simpa [Tapes.read] using hz)) hT (Spec.nil hT), ?_⟩
    exact ⟨rfl, fun _ _ => rfl, Tapes.Frame.refl t T, by simp⟩
  | false :: l, T, hseg, _, _, hT, hB => by
    simp only [seg, List.map, List.length_cons] at hseg
    obtain ⟨h0, hrest⟩ := List.cons.inj hseg
    have hcz : T.read t = z := by simpa [bsym, Tapes.read] using h0
    refine ⟨T, T.write t o, .stop (by simp [Cond.eval, hcz, hzo]) hT,
      Spec.ifElse_true (by simp [Cond.eval, hcz]) hT (Spec.write hT), ?_⟩
    refine ⟨?_, ?_, Tapes.Frame.write t T o, by simp⟩
    · simp only [List.length_cons, seg, binc, List.map, Tapes.write_tp_self]
      rw [seg_congr (g := T.tp t) (fun j h1 _ => by
        rw [Tapes.write_tp_self, ite_neg' (by omega)])]
      rw [hrest]; rfl
    · intro j hj
      rw [Tapes.write_tp_self, ite_neg' (by simp at hj; omega)]
  | true :: l, T, hseg, hz, ho, hT, hB => by
    simp only [seg, List.map, List.length_cons] at hseg hz ho hB
    obtain ⟨h0, hrest⟩ := List.cons.inj hseg
    have hco : T.read t = o := by simpa [bsym, Tapes.read] using h0
    set T₁ := (T.write t z).setHead t (T.hd t + 1) with hT₁
    have hT₁hd : T₁.hd t = T.hd t + 1 := by simp [T₁]
    have hT₁tp : ∀ j, j ≠ T.hd t → T₁.tp t j = T.tp t j := fun j hj => by
      simp only [T₁, Tapes.setHead_tp]; rw [Tapes.write_tp_self, ite_neg' hj]
    have hT₁ : T₁.Within B := Tapes.within_setHead (Tapes.within_write hT) (by omega)
    obtain ⟨Tm, T', hloop, htail, hP1, hP2, hP3, hP4⟩ := incr_aux t z o hzo l T₁
      (by rw [hT₁hd, seg_congr (g := T.tp t) (fun j h1 _ => hT₁tp j (by omega))]; exact hrest)
      (by rw [hT₁hd, hT₁tp _ (by omega), show T.hd t + 1 + l.length = T.hd t + (l.length + 1)
            by omega]; exact hz)
      (by rw [hT₁hd, hT₁tp _ (by omega), show T.hd t + 1 + l.length = T.hd t + (l.length + 1)
            by omega]; exact ho)
      hT₁ (by rw [hT₁hd]; omega)
    have hbody : Spec ([Instr.write t z] ++ [Instr.move t .right]) x B T T₁ :=
      (Spec.write hT).seq (Spec.moveRight (Tapes.within_write hT) (by simp; omega))
    refine ⟨Tm, T', .iter (by simp [Cond.eval, hco]) hT hbody hloop, htail, ?_, ?_, ?_, ?_⟩
    · rw [hT₁hd] at hP1
      simp only [List.length_cons, seg, binc, List.map]
      rw [hP1, hP2 _ (Or.inl (by rw [hT₁hd]; omega))]
      simp [T₁, Tapes.write_tp_self, bsym]
    · intro j hj
      simp only [List.length_cons] at hj
      rw [hP2 j (by rw [hT₁hd]; omega), hT₁tp j (by omega)]
    · exact (Tapes.Frame.trans (Tapes.Frame.trans (Tapes.Frame.write t T z)
        (Tapes.Frame.setHead t _ _)) hP3)
    · rw [hT₁hd] at hP4; simp; omega

/-- **Binary increment on tape.** If the cells under head `t` hold the bits `l`,
followed by a cell that is neither bit symbol, then `incr` replaces them by
`binc l` and changes nothing else (except the head of tape `t`). -/
theorem Spec.incr (t : Fin k) (z o : Γ) (hzo : z ≠ o) (l : List Bool) (T : Tapes k Γ)
    (hseg : seg (T.tp t) (T.hd t) l.length = l.map (bsym z o))
    (hz : T.tp t (T.hd t + l.length) ≠ z) (ho : T.tp t (T.hd t + l.length) ≠ o)
    (hT : T.Within B) (hB : T.hd t + l.length < B) :
    ∃ T', Spec (TM.incr t z o) x B T T' ∧ IncrPost t z o l T T' := by
  obtain ⟨Tm, T', hloop, htail, hpost⟩ := incr_aux (x := x) t z o hzo l T hseg hz ho hT hB
  exact ⟨T', (Spec.whileDo hloop).seq htail, hpost⟩

end Incr

/-! ### Comparing two binary blocks -/

section Compare

variable [DecidableEq Γ] {x : List Bool} {B : ℕ}

omit [DecidableEq Γ] in
theorem bsym_inj {z o : Γ} (hzo : z ≠ o) {b₁ b₂ : Bool} (h : bsym z o b₁ = bsym z o b₂) :
    b₁ = b₂ := by
  cases b₁ <;> cases b₂ <;> simp_all [bsym, Ne.symm hzo]

/-- One comparison step: on a mismatch at the current cells, write `no` on tape `f`;
then advance heads `a` and `b`. -/
def cmpBody (a b f : Fin k) (z o no : Γ) : Code k Γ :=
  TM.cases a (fun g => ifElse (.tape b (fun h => decide (h = g))) [] [Instr.write f no]) [z, o] ++
    [Instr.move a .right] ++ [Instr.move b .right]

/-- Compare the bit blocks under heads `a` and `b` (the block on `a` ends at the
first non-bit cell), writing `yes` / `no` under head `f`. -/
def cmpBits (a b f : Fin k) (z o yes no : Γ) : Code k Γ :=
  [Instr.write f yes] ++
    whileDo (.tape a (fun g => decide (g = z) || decide (g = o))) (cmpBody a b f z o no)

/-- What the comparison loop guarantees. -/
def CmpPost (a b f : Fin k) (no : Γ) (eq : Bool) (n : ℕ) (T T' : Tapes k Γ) : Prop :=
  T'.tp f (T.hd f) = (if eq then T.read f else no) ∧
  (∀ j, j ≠ T.hd f → T'.tp f j = T.tp f j) ∧
  (∀ i, i ≠ f → T'.tp i = T.tp i) ∧
  T'.hd a = T.hd a + n ∧ T'.hd b = T.hd b + n ∧
  (∀ i, i ≠ a → i ≠ b → T'.hd i = T.hd i) ∧ T'.ih = T.ih

theorem cmp_aux {a b f : Fin k} (hab : a ≠ b) (haf : a ≠ f) (hbf : b ≠ f) {z o no : Γ}
    (hzo : z ≠ o) :
    ∀ (l₁ l₂ : List Bool) (T : Tapes k Γ), l₁.length = l₂.length →
      seg (T.tp a) (T.hd a) l₁.length = l₁.map (bsym z o) →
      seg (T.tp b) (T.hd b) l₂.length = l₂.map (bsym z o) →
      T.tp a (T.hd a + l₁.length) ≠ z → T.tp a (T.hd a + l₁.length) ≠ o →
      T.Within B → T.hd a + l₁.length < B → T.hd b + l₁.length < B →
      ∃ T', Loop (.tape a (fun g => decide (g = z) || decide (g = o))) (cmpBody a b f z o no)
          x B T T' ∧ CmpPost a b f no (decide (l₁ = l₂)) l₁.length T T'
  | [], [], T, _, _, _, hz, ho, hT, _, _ => by
    have hz' : T.tp a (T.hd a) ≠ z := by simpa using hz
    have ho' : T.tp a (T.hd a) ≠ o := by simpa using ho
    refine ⟨T, .stop (by simp [Cond.eval, Tapes.read, hz', ho']) hT, ?_⟩
    exact ⟨by simp [Tapes.read], fun _ _ => rfl, fun _ _ => rfl, by simp, by simp,
      fun _ _ _ => rfl, rfl⟩
  | b₁ :: l₁, b₂ :: l₂, T, hl, hsa, hsb, hz, ho, hT, hBa, hBb => by
    simp only [List.length_cons, seg, List.map] at hl hsa hsb hz ho hBa hBb
    obtain ⟨ha0, hrestA⟩ := List.cons.inj hsa
    obtain ⟨hb0, hrestB⟩ := List.cons.inj hsb
    have hl' : l₁.length = l₂.length := by omega
    have hra : T.read a = bsym z o b₁ := ha0
    have hrb : T.read b = bsym z o b₂ := hb0
    -- after the case split, the flag tape holds `T₀`
    set T₀ := if b₁ = b₂ then T else T.write f no with hT₀def
    have hT₀hd : T₀.hd = T.hd := by by_cases h : b₁ = b₂ <;> simp [T₀, h]
    have hT₀ih : T₀.ih = T.ih := by by_cases h : b₁ = b₂ <;> simp [T₀, h]
    have hT₀tp : ∀ i, i ≠ f → T₀.tp i = T.tp i := fun i hi => by
      by_cases h : b₁ = b₂ <;> simp [T₀, h, Tapes.write, hi]
    have hT₀f : ∀ j, j ≠ T.hd f → T₀.tp f j = T.tp f j := fun j hj => by
      by_cases h : b₁ = b₂
      · simp [T₀, h]
      · simp only [T₀, h, ite_false]; rw [Tapes.write_tp_self, ite_neg' hj]
    have hT₀flag : T₀.tp f (T.hd f) = if b₁ = b₂ then T.read f else no := by
      by_cases h : b₁ = b₂
      · simp [T₀, h, Tapes.read]
      · simp [T₀, h, Tapes.write_tp_self]
    have hT₀W : T₀.Within B := by
      intro i; rw [hT₀hd]; exact hT i
    have hcase : Spec (TM.cases a (fun g => ifElse (.tape b (fun h => decide (h = g))) []
        [Instr.write f no]) [z, o]) x B T T₀ := by
      refine Spec.cases a _ [z, o] (by rw [hra]; cases b₁ <;> simp [bsym]) hT ?_
      by_cases h : b₁ = b₂
      · have : T₀ = T := by simp [T₀, h]
        rw [this]
        exact Spec.ifElse_true (by simp [Cond.eval, hra, hrb, h]) hT (Spec.nil hT)
      · have : T₀ = T.write f no := by simp [T₀, h]
        rw [this]
        refine Spec.ifElse_false ?_ hT (Spec.write hT)
        simp only [Cond.eval, hra, hrb, decide_eq_false_iff_not]
        exact fun e => h (bsym_inj hzo e).symm
    set T₁ := (T₀.setHead a (T₀.hd a + 1)).setHead b (T₀.hd b + 1) with hT₁def
    have hT₁hd_a : T₁.hd a = T.hd a + 1 := by simp [T₁, Tapes.setHead, hab, hT₀hd]
    have hT₁hd_b : T₁.hd b = T.hd b + 1 := by simp [T₁, Tapes.setHead, hT₀hd]
    have hT₁hd : ∀ i, i ≠ a → i ≠ b → T₁.hd i = T.hd i := fun i h1 h2 => by
      simp [T₁, Tapes.setHead, h1, h2, hT₀hd]
    have hT₁tp : T₁.tp = T₀.tp := rfl
    have hT₁W : T₁.Within B :=
      Tapes.within_setHead (Tapes.within_setHead hT₀W (by rw [hT₀hd]; omega))
        (by rw [hT₀hd]; omega)
    have hbody : Spec (cmpBody a b f z o no) x B T T₁ := by
      have h2 := Spec.moveRight (x := x) (t := a) hT₀W (by rw [hT₀hd]; omega)
      have h3 := Spec.moveRight (x := x) (t := b)
        (Tapes.within_setHead (t := a) (n := T₀.hd a + 1) hT₀W (by rw [hT₀hd]; omega))
        (by rw [Tapes.setHead_hd_ne _ _ (Ne.symm hab), hT₀hd]; omega)
      rw [Tapes.setHead_hd_ne _ _ (Ne.symm hab)] at h3
      exact (hcase.seq h2).seq h3
    obtain ⟨T', hloop, hP1, hP2, hP3, hP4, hP5, hP6, hP7⟩ :=
      cmp_aux hab haf hbf hzo l₁ l₂ T₁ hl'
        (by rw [hT₁hd_a, hT₁tp, hT₀tp a haf]; exact hrestA)
        (by rw [hT₁hd_b, hT₁tp, hT₀tp b hbf, ← hl']; rw [← hl'] at hrestB; exact hrestB)
        (by rw [hT₁hd_a, hT₁tp, hT₀tp a haf]; rwa [Nat.add_assoc, Nat.add_comm 1])
        (by rw [hT₁hd_a, hT₁tp, hT₀tp a haf]; rwa [Nat.add_assoc, Nat.add_comm 1])
        hT₁W (by rw [hT₁hd_a]; omega) (by rw [hT₁hd_b]; omega)
    have hcond : Cond.eval x T (.tape a (fun g => decide (g = z) || decide (g = o))) = true := by
      simp only [Cond.eval, hra]; cases b₁ <;> simp [bsym]
    refine ⟨T', .iter hcond hT hbody hloop, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hf : T₁.hd f = T.hd f := hT₁hd f (Ne.symm haf) (Ne.symm hbf)
      rw [hf] at hP1
      rw [hP1]
      simp only [Tapes.read, hf, hT₁tp, hT₀flag, List.cons.injEq]
      by_cases h : b₁ = b₂ <;> by_cases h' : l₁ = l₂ <;> simp [h, h']
    · intro j hj
      have hf : T₁.hd f = T.hd f := hT₁hd f (Ne.symm haf) (Ne.symm hbf)
      rw [hP2 j (by rw [hf]; exact hj), hT₁tp, hT₀f j hj]
    · intro i hi
      rw [hP3 i hi, hT₁tp, hT₀tp i hi]
    · rw [hP4, hT₁hd_a]; simp only [List.length_cons]; omega
    · rw [hP5, hT₁hd_b]; simp only [List.length_cons]; omega
    · intro i h1 h2; rw [hP6 i h1 h2, hT₁hd i h1 h2]
    · rw [hP7]; simp [T₁, hT₀ih]

/-- **Block compare.** For bit blocks `l₁` (under head `a`, ending at a non-bit cell)
and `l₂` (under head `b`) of equal length, `cmpBits` writes `yes` under head `f`
exactly when `l₁ = l₂`, and `no` otherwise. -/
theorem Spec.cmpBits {a b f : Fin k} (hab : a ≠ b) (haf : a ≠ f) (hbf : b ≠ f) {z o yes no : Γ}
    (hzo : z ≠ o) (l₁ l₂ : List Bool) (T : Tapes k Γ) (hl : l₁.length = l₂.length)
    (hsa : seg (T.tp a) (T.hd a) l₁.length = l₁.map (bsym z o))
    (hsb : seg (T.tp b) (T.hd b) l₂.length = l₂.map (bsym z o))
    (hz : T.tp a (T.hd a + l₁.length) ≠ z) (ho : T.tp a (T.hd a + l₁.length) ≠ o)
    (hT : T.Within B) (hBa : T.hd a + l₁.length < B) (hBb : T.hd b + l₁.length < B) :
    ∃ T', Spec (TM.cmpBits a b f z o yes no) x B T T' ∧
      CmpPost a b f no (decide (l₁ = l₂)) l₁.length (T.write f yes) T' := by
  have hW := Tapes.within_write (t := f) (g := yes) hT
  obtain ⟨T', hloop, hpost⟩ := cmp_aux (x := x) hab haf hbf hzo l₁ l₂ (T.write f yes) hl
    (by simp only [Tapes.write_hd]; rw [seg_congr (g := T.tp a) (fun j _ _ => by
      simp [Tapes.write, haf])]; exact hsa)
    (by simp only [Tapes.write_hd]; rw [seg_congr (g := T.tp b) (fun j _ _ => by
      simp [Tapes.write, hbf])]; exact hsb)
    (by simpa [Tapes.write, haf] using hz) (by simpa [Tapes.write, haf] using ho)
    hW hBa hBb
  exact ⟨T', (Spec.write hT).seq (Spec.whileDo hloop), hpost⟩

end Compare

end Savitch.TM
