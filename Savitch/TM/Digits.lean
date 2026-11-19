import Savitch.TM.Binary
import Mathlib.Algebra.BigOperators.Fin

/-!
# Base-`m` digit blocks on tapes

Phase 4b-3 / 4b-5 groundwork (see `PLAN.md`).

A vertex of the generic Phase 2 machine is a number `< m ^ L` (`m` = number of
records). On tape it is a block of `L` cells holding its base-`m` digits
**little-endian**, the digit `d` written as the symbol `sym d`.

Pure part:
* `dval l`: the value of a digit list; `dval_lt`, `dval_inj`.
* `dinc l`: increment; `dval_dinc` shows it adds one when there is room.
* `finFunctionFinEquiv_val`: Mathlib's `finFunctionFinEquiv` is `dval ∘ List.ofFn`,
  so the enumeration order of vertices is exactly the order `dinc` walks in.

Tape part:
* `casesD t sym code ds`: case split on which digit is under head `t`.
* `incrD t sym`: in-place increment (`Spec.incrD`).
* `cmpD a b f sym yes no`: compare two digit blocks into a flag cell (`Spec.cmpD`).
-/

namespace Savitch.TM

/-! ### Little-endian base-`m` numbers -/

section Pure

variable {m : ℕ}

def dval : List (Fin m) → ℕ
  | [] => 0
  | d :: l => d.val + m * dval l

def dinc [NeZero m] : List (Fin m) → List (Fin m)
  | [] => []
  | d :: l => if h : d.val + 1 < m then ⟨d.val + 1, h⟩ :: l else 0 :: dinc l

theorem dinc_length [NeZero m] : ∀ l : List (Fin m), (dinc l).length = l.length
  | [] => rfl
  | d :: l => by
    unfold dinc
    split_ifs <;> simp [dinc_length l]

theorem dval_lt : ∀ l : List (Fin m), dval l < m ^ l.length
  | [] => by simp [dval]
  | d :: l => by
    have ih := dval_lt l
    have h1 : m * dval l + m ≤ m * m ^ l.length := by
      have := Nat.mul_le_mul_left m (show dval l + 1 ≤ m ^ l.length from ih)
      rwa [Nat.mul_add, Nat.mul_one] at this
    have := d.isLt
    simp only [dval, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_comm (m ^ l.length) m]
    omega

theorem dval_dinc [NeZero m] :
    ∀ l : List (Fin m), dval l + 1 < m ^ l.length → dval (dinc l) = dval l + 1
  | [], h => by simp [dval] at h
  | d :: l, h => by
    unfold dinc
    split_ifs with hd
    · simp only [dval]; omega
    · have hdm : d.val = m - 1 := by have := d.isLt; omega
      have hpos : 0 < m := Nat.pos_of_neZero m
      have h' : dval l + 1 < m ^ l.length := by
        simp only [dval, List.length_cons, Nat.pow_succ] at h
        have : m * (dval l + 1) < m * m ^ l.length := by
          rw [Nat.mul_comm (m ^ l.length) m] at h
          rw [Nat.mul_add, Nat.mul_one]; omega
        exact Nat.lt_of_mul_lt_mul_left this
      simp only [dval, dval_dinc l h', Fin.val_zero, Nat.mul_add, Nat.mul_one]
      omega

theorem dval_inj : ∀ {l₁ l₂ : List (Fin m)}, l₁.length = l₂.length → dval l₁ = dval l₂ → l₁ = l₂
  | [], [], _, _ => rfl
  | d₁ :: l₁, d₂ :: l₂, hl, h => by
    simp only [dval] at h
    have hpos : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) d₁.isLt
    have hd : d₁.val = d₂.val := by
      have := congrArg (· % m) h
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt d₁.isLt,
        Nat.mod_eq_of_lt d₂.isLt] at this
      exact this
    have hv : dval l₁ = dval l₂ := by
      have : m * dval l₁ = m * dval l₂ := by omega
      exact Nat.eq_of_mul_eq_mul_left hpos this
    rw [Fin.ext hd, dval_inj (by simpa using hl) hv]

theorem sum_eq_dval : ∀ {L : ℕ} (f : Fin L → Fin m),
    ∑ i : Fin L, (f i : ℕ) * m ^ (i : ℕ) = dval (List.ofFn f)
  | 0, f => by simp [dval]
  | L + 1, f => by
    rw [Fin.sum_univ_succ, List.ofFn_succ, dval, ← sum_eq_dval (fun i => f i.succ),
      Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, Nat.mul_one, Fin.val_succ, pow_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Mathlib's `finFunctionFinEquiv` reads a digit function little-endian. -/
theorem finFunctionFinEquiv_val {L : ℕ} (f : Fin L → Fin m) :
    (finFunctionFinEquiv f : ℕ) = dval (List.ofFn f) := by
  rw [finFunctionFinEquiv_apply, sum_eq_dval]

end Pure

/-! ### Tape routines on digit blocks -/

variable {k : ℕ} {Γ : Type} [DecidableEq Γ] {m : ℕ} {x : List Bool} {B : ℕ}

/-- Run `code d` where `sym d` is the symbol under head `t` (for `d ∈ ds`). -/
def casesD (t : Fin k) (sym : Fin m → Γ) (code : Fin m → Code k Γ) : List (Fin m) → Code k Γ
  | [] => []
  | d :: ds => ifElse (.tape t (fun g => decide (g = sym d))) (code d) (casesD t sym code ds)

theorem Spec.casesD {t : Fin k} {sym : Fin m → Γ} (hsym : Function.Injective sym)
    (code : Fin m → Code k Γ) {d : Fin m} {T T' : Tapes k Γ} (hT : T.Within B)
    (hd : T.read t = sym d) (h : Spec (code d) x B T T') :
    ∀ ds : List (Fin m), d ∈ ds → Spec (TM.casesD t sym code ds) x B T T'
  | [], hmem => absurd hmem List.not_mem_nil
  | d' :: ds, hmem => by
    by_cases he : d' = d
    · subst he
      exact Spec.ifElse_true (by simp [Cond.eval, hd]) hT h
    · refine Spec.ifElse_false ?_ hT (Spec.casesD hsym code hT hd h ds
        (List.mem_of_ne_of_mem (Ne.symm he) hmem))
      simp only [Cond.eval, hd, decide_eq_false_iff_not]
      exact fun e => he (hsym e).symm

theorem Spec.casesD_none {t : Fin k} {sym : Fin m → Γ} (code : Fin m → Code k Γ)
    {T : Tapes k Γ} (hT : T.Within B) :
    ∀ ds : List (Fin m), (∀ d, T.read t ≠ sym d) → Spec (TM.casesD t sym code ds) x B T T
  | [], _ => Spec.nil hT
  | d :: ds, hn => Spec.ifElse_false (by simp [Cond.eval, hn d]) hT
      (Spec.casesD_none code hT ds hn)

section IncrD

variable [NeZero m]

def topD : Fin m := ⟨m - 1, by have := Nat.pos_of_neZero m; omega⟩

/-- In-place increment of the digit block under head `t`. -/
def incrD (t : Fin k) (sym : Fin m → Γ) : Code k Γ :=
  whileDo (.tape t (fun g => decide (g = sym topD)))
    ([Instr.write t (sym 0)] ++ [Instr.move t .right]) ++
  TM.casesD t sym (fun d => if h : d.val + 1 < m then [Instr.write t (sym ⟨d.val + 1, h⟩)] else [])
    (List.finRange m)

def IncrDPost (t : Fin k) (sym : Fin m → Γ) (l : List (Fin m)) (T T' : Tapes k Γ) : Prop :=
  seg (T'.tp t) (T.hd t) l.length = (dinc l).map sym ∧
  (∀ j, (j < T.hd t ∨ T.hd t + l.length ≤ j) → T'.tp t j = T.tp t j) ∧
  T.Frame t T' ∧ T'.hd t ≤ T.hd t + l.length

theorem incrD_aux (t : Fin k) {sym : Fin m → Γ} (hsym : Function.Injective sym) :
    ∀ (l : List (Fin m)) (T : Tapes k Γ),
      seg (T.tp t) (T.hd t) l.length = l.map sym →
      (∀ d, T.tp t (T.hd t + l.length) ≠ sym d) →
      T.Within B → T.hd t + l.length < B →
      ∃ Tm T', Loop (.tape t (fun g => decide (g = sym topD)))
          ([Instr.write t (sym 0)] ++ [Instr.move t .right]) x B T Tm ∧
        Spec (TM.casesD t sym (fun d => if h : d.val + 1 < m then
          [Instr.write t (sym ⟨d.val + 1, h⟩)] else []) (List.finRange m)) x B Tm T' ∧
        IncrDPost t sym l T T'
  | [], T, _, hend, hT, _ => by
    have hn : ∀ d, T.read t ≠ sym d := by simpa [Tapes.read] using hend
    refine ⟨T, T, .stop (by simp [Cond.eval, hn]) hT, Spec.casesD_none _ hT _ hn, ?_⟩
    exact ⟨rfl, fun _ _ => rfl, Tapes.Frame.refl t T, by simp⟩
  | d :: l, T, hseg, hend, hT, hB => by
    simp only [seg, List.map, List.length_cons] at hseg hend hB
    obtain ⟨h0, hrest⟩ := List.cons.inj hseg
    have hrd : T.read t = sym d := h0
    by_cases hd : d.val + 1 < m
    · -- no carry: the loop stops, the case split bumps `d`
      have hne : d ≠ topD := fun e => by simp [e, topD] at hd; omega
      refine ⟨T, T.write t (sym ⟨d.val + 1, hd⟩),
        .stop (by simp [Cond.eval, hrd]; exact fun e => hne (hsym e)) hT,
        Spec.casesD hsym _ hT hrd (by simp only [hd, ↓reduceDIte]; exact Spec.write hT) _
          (List.mem_finRange d), ?_⟩
      refine ⟨?_, ?_, Tapes.Frame.write t T _, by simp⟩
      · simp only [List.length_cons, seg, dinc, hd, ↓reduceDIte, List.map, Tapes.write_tp_self,
          ite_true]
        rw [seg_congr (g := T.tp t) (fun j h1 _ => by
          rw [Tapes.write_tp_self, ite_neg' (by omega)])]
        rw [hrest]
      · intro j hj
        rw [Tapes.write_tp_self, ite_neg' (by simp at hj; omega)]
    · -- carry: `d` is the top digit; write `0` and continue to the right
      have htop : d = topD := Fin.ext (by simp [topD]; omega)
      set T₁ := (T.write t (sym 0)).setHead t (T.hd t + 1) with hT₁
      have hT₁hd : T₁.hd t = T.hd t + 1 := by simp [T₁]
      have hT₁tp : ∀ j, j ≠ T.hd t → T₁.tp t j = T.tp t j := fun j hj => by
        simp only [T₁, Tapes.setHead_tp]; rw [Tapes.write_tp_self, ite_neg' hj]
      have hT₁ : T₁.Within B := Tapes.within_setHead (Tapes.within_write hT) (by omega)
      obtain ⟨Tm, T', hloop, htail, hP1, hP2, hP3, hP4⟩ := incrD_aux t hsym l T₁
        (by rw [hT₁hd, seg_congr (g := T.tp t) (fun j h1 _ => hT₁tp j (by omega))]; exact hrest)
        (fun d' => by
          rw [hT₁hd, hT₁tp _ (by omega), show T.hd t + 1 + l.length = T.hd t + (l.length + 1)
            by omega]; exact hend d')
        hT₁ (by rw [hT₁hd]; omega)
      have hbody : Spec ([Instr.write t (sym 0)] ++ [Instr.move t .right]) x B T T₁ :=
        (Spec.write hT).seq (Spec.moveRight (Tapes.within_write hT) (by simp; omega))
      refine ⟨Tm, T', .iter (by simp [Cond.eval, hrd, htop]) hT hbody hloop, htail,
        ?_, ?_, ?_, ?_⟩
      · rw [hT₁hd] at hP1
        simp only [List.length_cons, seg, dinc, hd, ↓reduceDIte, List.map]
        rw [hP1, hP2 _ (Or.inl (by rw [hT₁hd]; omega))]
        simp [T₁, Tapes.write_tp_self]
      · intro j hj
        simp only [List.length_cons] at hj
        rw [hP2 j (by rw [hT₁hd]; omega), hT₁tp j (by omega)]
      · exact (Tapes.Frame.trans (Tapes.Frame.trans (Tapes.Frame.write t T _)
          (Tapes.Frame.setHead t _ _)) hP3)
      · rw [hT₁hd] at hP4; simp; omega

/-- **Digit-block increment on tape.** If the cells under head `t` hold the digits
`l` (followed by a non-digit cell), `incrD` replaces them by `dinc l`. -/
theorem Spec.incrD (t : Fin k) {sym : Fin m → Γ} (hsym : Function.Injective sym)
    (l : List (Fin m)) (T : Tapes k Γ)
    (hseg : seg (T.tp t) (T.hd t) l.length = l.map sym)
    (hend : ∀ d, T.tp t (T.hd t + l.length) ≠ sym d)
    (hT : T.Within B) (hB : T.hd t + l.length < B) :
    ∃ T', Spec (TM.incrD t sym) x B T T' ∧ IncrDPost t sym l T T' := by
  obtain ⟨Tm, T', hloop, htail, hpost⟩ := incrD_aux (x := x) t hsym l T hseg hend hT hB
  exact ⟨T', (Spec.whileDo hloop).seq htail, hpost⟩

end IncrD

/-! ### Comparing two digit blocks -/

section CmpD

/-- Is `g` a digit symbol? -/
def isDigit (sym : Fin m → Γ) (g : Γ) : Bool := decide (∃ d, g = sym d)

/-- One comparison step for digit blocks. -/
def cmpDBody (a b f : Fin k) (sym : Fin m → Γ) (no : Γ) : Code k Γ :=
  TM.casesD a sym (fun d => ifElse (.tape b (fun h => decide (h = sym d))) []
    [Instr.write f no]) (List.finRange m) ++
  [Instr.move a .right] ++ [Instr.move b .right]

/-- Compare the digit blocks under heads `a` and `b`, writing `yes`/`no` under head `f`. -/
def cmpD (a b f : Fin k) (sym : Fin m → Γ) (yes no : Γ) : Code k Γ :=
  [Instr.write f yes] ++ whileDo (.tape a (isDigit sym)) (cmpDBody a b f sym no)

theorem cmpD_aux {a b f : Fin k} (hab : a ≠ b) (haf : a ≠ f) (hbf : b ≠ f) {sym : Fin m → Γ}
    (hsym : Function.Injective sym) {no : Γ} :
    ∀ (l₁ l₂ : List (Fin m)) (T : Tapes k Γ), l₁.length = l₂.length →
      seg (T.tp a) (T.hd a) l₁.length = l₁.map sym →
      seg (T.tp b) (T.hd b) l₂.length = l₂.map sym →
      (∀ d, T.tp a (T.hd a + l₁.length) ≠ sym d) →
      T.Within B → T.hd a + l₁.length < B → T.hd b + l₁.length < B →
      ∃ T', Loop (.tape a (isDigit sym)) (cmpDBody a b f sym no) x B T T' ∧
        CmpPost a b f no (decide (l₁ = l₂)) l₁.length T T'
  | [], [], T, _, _, _, hend, hT, _, _ => by
    have hn : ∀ d, T.read a ≠ sym d := by simpa [Tapes.read] using hend
    refine ⟨T, .stop (by simp [Cond.eval, isDigit, hn]) hT, ?_⟩
    exact ⟨by simp [Tapes.read], fun _ _ => rfl, fun _ _ => rfl, by simp, by simp,
      fun _ _ _ => rfl, rfl⟩
  | d₁ :: l₁, d₂ :: l₂, T, hl, hsa, hsb, hend, hT, hBa, hBb => by
    simp only [List.length_cons, seg, List.map] at hl hsa hsb hend hBa hBb
    obtain ⟨ha0, hrestA⟩ := List.cons.inj hsa
    obtain ⟨hb0, hrestB⟩ := List.cons.inj hsb
    have hl' : l₁.length = l₂.length := by omega
    have hra : T.read a = sym d₁ := ha0
    have hrb : T.read b = sym d₂ := hb0
    set T₀ := if d₁ = d₂ then T else T.write f no with hT₀def
    have hT₀hd : T₀.hd = T.hd := by by_cases h : d₁ = d₂ <;> simp [T₀, h]
    have hT₀ih : T₀.ih = T.ih := by by_cases h : d₁ = d₂ <;> simp [T₀, h]
    have hT₀tp : ∀ i, i ≠ f → T₀.tp i = T.tp i := fun i hi => by
      by_cases h : d₁ = d₂ <;> simp [T₀, h, Tapes.write, hi]
    have hT₀f : ∀ j, j ≠ T.hd f → T₀.tp f j = T.tp f j := fun j hj => by
      by_cases h : d₁ = d₂
      · simp [T₀, h]
      · simp only [T₀, h, ite_false]; rw [Tapes.write_tp_self, ite_neg' hj]
    have hT₀flag : T₀.tp f (T.hd f) = if d₁ = d₂ then T.read f else no := by
      by_cases h : d₁ = d₂
      · simp [T₀, h, Tapes.read]
      · simp [T₀, h, Tapes.write_tp_self]
    have hT₀W : T₀.Within B := by
      intro i; rw [hT₀hd]; exact hT i
    have hcase : Spec (TM.casesD a sym (fun d => ifElse (.tape b (fun h => decide (h = sym d)))
        [] [Instr.write f no]) (List.finRange m)) x B T T₀ := by
      refine Spec.casesD hsym _ hT hra ?_ _ (List.mem_finRange d₁)
      by_cases h : d₁ = d₂
      · have : T₀ = T := by simp [T₀, h]
        rw [this]
        exact Spec.ifElse_true (by simp [Cond.eval, hrb, h]) hT (Spec.nil hT)
      · have : T₀ = T.write f no := by simp [T₀, h]
        rw [this]
        refine Spec.ifElse_false ?_ hT (Spec.write hT)
        simp only [Cond.eval, hrb, decide_eq_false_iff_not]
        exact fun e => h (hsym e).symm
    set T₁ := (T₀.setHead a (T₀.hd a + 1)).setHead b (T₀.hd b + 1) with hT₁def
    have hT₁hd_a : T₁.hd a = T.hd a + 1 := by simp [T₁, Tapes.setHead, hab, hT₀hd]
    have hT₁hd_b : T₁.hd b = T.hd b + 1 := by simp [T₁, Tapes.setHead, hT₀hd]
    have hT₁hd : ∀ i, i ≠ a → i ≠ b → T₁.hd i = T.hd i := fun i h1 h2 => by
      simp [T₁, Tapes.setHead, h1, h2, hT₀hd]
    have hT₁tp : T₁.tp = T₀.tp := rfl
    have hT₁W : T₁.Within B :=
      Tapes.within_setHead (Tapes.within_setHead hT₀W (by rw [hT₀hd]; omega))
        (by rw [hT₀hd]; omega)
    have hbody : Spec (cmpDBody a b f sym no) x B T T₁ := by
      have h2 := Spec.moveRight (x := x) (t := a) hT₀W (by rw [hT₀hd]; omega)
      have h3 := Spec.moveRight (x := x) (t := b)
        (Tapes.within_setHead (t := a) (n := T₀.hd a + 1) hT₀W (by rw [hT₀hd]; omega))
        (by rw [Tapes.setHead_hd_ne _ _ (Ne.symm hab), hT₀hd]; omega)
      rw [Tapes.setHead_hd_ne _ _ (Ne.symm hab)] at h3
      exact (hcase.seq h2).seq h3
    obtain ⟨T', hloop, hP1, hP2, hP3, hP4, hP5, hP6, hP7⟩ :=
      cmpD_aux hab haf hbf hsym l₁ l₂ T₁ hl'
        (by rw [hT₁hd_a, hT₁tp, hT₀tp a haf]; exact hrestA)
        (by rw [hT₁hd_b, hT₁tp, hT₀tp b hbf, ← hl']; rw [← hl'] at hrestB; exact hrestB)
        (fun d => by rw [hT₁hd_a, hT₁tp, hT₀tp a haf]; rw [Nat.add_assoc, Nat.add_comm 1]
                     exact hend d)
        hT₁W (by rw [hT₁hd_a]; omega) (by rw [hT₁hd_b]; omega)
    have hcond : Cond.eval x T (.tape a (isDigit sym)) = true := by
      simp only [Cond.eval, isDigit, hra, decide_eq_true_eq]; exact ⟨d₁, rfl⟩
    refine ⟨T', .iter hcond hT hbody hloop, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hf : T₁.hd f = T.hd f := hT₁hd f (Ne.symm haf) (Ne.symm hbf)
      rw [hf] at hP1
      rw [hP1]
      simp only [Tapes.read, hf, hT₁tp, hT₀flag, List.cons.injEq]
      by_cases h : d₁ = d₂ <;> by_cases h' : l₁ = l₂ <;> simp [h, h']
    · intro j hj
      have hf : T₁.hd f = T.hd f := hT₁hd f (Ne.symm haf) (Ne.symm hbf)
      rw [hP2 j (by rw [hf]; exact hj), hT₁tp, hT₀f j hj]
    · intro i hi
      rw [hP3 i hi, hT₁tp, hT₀tp i hi]
    · rw [hP4, hT₁hd_a]; simp only [List.length_cons]; omega
    · rw [hP5, hT₁hd_b]; simp only [List.length_cons]; omega
    · intro i h1 h2; rw [hP6 i h1 h2, hT₁hd i h1 h2]
    · rw [hP7]; simp [T₁, hT₀ih]

/-- **Digit-block compare.** Writes `yes` under head `f` iff the blocks are equal. -/
theorem Spec.cmpD {a b f : Fin k} (hab : a ≠ b) (haf : a ≠ f) (hbf : b ≠ f)
    {sym : Fin m → Γ} (hsym : Function.Injective sym) {yes no : Γ}
    (l₁ l₂ : List (Fin m)) (T : Tapes k Γ) (hl : l₁.length = l₂.length)
    (hsa : seg (T.tp a) (T.hd a) l₁.length = l₁.map sym)
    (hsb : seg (T.tp b) (T.hd b) l₂.length = l₂.map sym)
    (hend : ∀ d, T.tp a (T.hd a + l₁.length) ≠ sym d)
    (hT : T.Within B) (hBa : T.hd a + l₁.length < B) (hBb : T.hd b + l₁.length < B) :
    ∃ T', Spec (TM.cmpD a b f sym yes no) x B T T' ∧
      CmpPost a b f no (decide (l₁ = l₂)) l₁.length (T.write f yes) T' := by
  have hW := Tapes.within_write (t := f) (g := yes) hT
  obtain ⟨T', hloop, hpost⟩ := cmpD_aux (x := x) (no := no) hab haf hbf hsym l₁ l₂
    (T.write f yes) hl
    (by simp only [Tapes.write_hd]; rw [seg_congr (g := T.tp a) (fun j _ _ => by
      simp [Tapes.write, haf])]; exact hsa)
    (by simp only [Tapes.write_hd]; rw [seg_congr (g := T.tp b) (fun j _ _ => by
      simp [Tapes.write, hbf])]; exact hsb)
    (fun d => by simpa [Tapes.write, haf] using hend d)
    hW hBa hBb
  exact ⟨T', (Spec.write hT).seq (Spec.whileDo hloop), hpost⟩

end CmpD

end Savitch.TM
