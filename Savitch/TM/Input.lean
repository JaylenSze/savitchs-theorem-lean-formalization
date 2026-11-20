import Savitch.TM.Track

/-!
# Counters with a home cell, and a position-tracked input head

Phase 4b-4 groundwork (see `PLAN.md`).

**Counter layout.** `Holds t mk z o T l`: cell 0 of tape `t` holds the marker `mk`,
cells `1 … |l|` hold the bits `l`, the next cell is none of `z`, `o`, `mk`, and the
head is parked at cell 1. Counter operations keep this layout:
`incrH`, `decrH` (in place), `isZeroH` (into a flag).

**Input head.** The Savitch TM keeps a counter `P` equal to the input-head position.
* `inRight`: move right unless at the right end marker (exactly `moveIn … .right`).
* `inLeft`: move left unless at position 0.
* `seekIn`: apply `inRight` `c` times, where counter `C` holds `c`. The input head
  ends at `min (ih + c) (n + 1)`, which is how `decR` caps the encoded position.
-/

set_option linter.unusedSectionVars false

namespace Savitch.TM

open Machine (Dir inputSym moveIn)

variable {k : ℕ} {Γ : Type} [DecidableEq Γ] {x : List Bool} {B : ℕ}

/-! ### Small facts -/

theorem mem_seg (f : ℕ → Γ) : ∀ {s n i : ℕ}, i < n → f (s + i) ∈ seg f s n
  | _, 0, _, h => absurd h (Nat.not_lt_zero _)
  | s, n + 1, i, h => by
    simp only [seg, List.mem_cons]
    rcases i with _ | i
    · exact Or.inl rfl
    · right
      have := mem_seg f (s := s + 1) (n := n) (i := i) (by omega)
      rwa [show s + 1 + i = s + (i + 1) by omega] at this

theorem ne_of_seg {f : ℕ → Γ} {z o mk : Γ} (hmz : mk ≠ z) (hmo : mk ≠ o) {s : ℕ} {l : List Bool}
    (hseg : seg f s l.length = l.map (bsym z o)) {j : ℕ} (h1 : s ≤ j) (h2 : j < s + l.length) :
    f j ≠ mk := by
  have hm := mem_seg f (s := s) (n := l.length) (i := j - s) (by omega)
  rw [show s + (j - s) = j by omega, hseg, List.mem_map] at hm
  obtain ⟨b, _, hb⟩ := hm
  rw [← hb]
  cases b
  · exact Ne.symm hmz
  · exact Ne.symm hmo

theorem inputSym_eq_none (x : List Bool) (i : ℕ) : inputSym x i = none ↔ (i = 0 ∨ x.length < i) := by
  unfold inputSym
  split_ifs with h
  · simp [h]
  · rw [List.getElem?_eq_none_iff]; omega

/-! ### Counters with a home cell -/

/-- Counter tape `t` holds the bits `l` in the standard layout, head at cell 1. -/
def Holds (t : Fin k) (mk z o : Γ) (T : Tapes k Γ) (l : List Bool) : Prop :=
  T.tp t 0 = mk ∧ seg (T.tp t) 1 l.length = l.map (bsym z o) ∧
  T.tp t (l.length + 1) ≠ z ∧ T.tp t (l.length + 1) ≠ o ∧ T.tp t (l.length + 1) ≠ mk ∧
  T.hd t = 1

theorem Holds.congr {t : Fin k} {mk z o : Γ} {T T' : Tapes k Γ} {l : List Bool}
    (h : Holds t mk z o T l) (htp : T'.tp t = T.tp t) (hhd : T'.hd t = T.hd t) :
    Holds t mk z o T' l := by
  unfold Holds at *
  rw [htp, hhd]; exact h

/-- Return the head of tape `t` to cell 1 (just right of the marker). -/
def home (t : Fin k) (mk : Γ) : Code k Γ := TM.rewind t mk ++ [Instr.move t .right]

theorem Spec.home (t : Fin k) (mk : Γ) {T : Tapes k Γ} (h0 : T.tp t 0 = mk)
    (hne : ∀ j, 0 < j → j ≤ T.hd t → T.tp t j ≠ mk) (hT : T.Within B) (hB : 1 < B) :
    Spec (TM.home t mk) x B T (T.setHead t 1) := by
  have h1 := Spec.rewind (x := x) t mk h0 hne hT
  have h2 := Spec.moveRight (x := x) (t := t) (Tapes.within_setHead (t := t) (n := 0) hT (by omega))
    (by simp only [Tapes.setHead_hd_self]; omega)
  simp only [Tapes.setHead_hd_self, Tapes.setHead_setHead] at h2
  exact h1.seq h2

variable {mk z o : Γ}

omit [DecidableEq Γ] in
theorem Holds.within_end {t : Fin k} {T : Tapes k Γ} {l : List Bool} (_ : Holds t mk z o T l)
    (hB : l.length + 2 ≤ B) : T.hd t + l.length < B := by
  obtain ⟨_, _, _, _, _, hh⟩ := ‹Holds t mk z o T l›; omega

/-- In-place increment of a counter, head returned home. -/
def incrH (t : Fin k) (mk z o : Γ) : Code k Γ := TM.incr t z o ++ TM.home t mk

theorem Spec.incrH {t : Fin k} (hzo : z ≠ o) (hmz : mk ≠ z) (hmo : mk ≠ o) {l : List Bool}
    {T : Tapes k Γ} (hH : Holds t mk z o T l) (hT : T.Within B) (hB : l.length + 2 ≤ B) :
    ∃ T', Spec (TM.incrH t mk z o) x B T T' ∧ Holds t mk z o T' (binc l) ∧ T.Frame t T' ∧
      T'.Within B := by
  obtain ⟨h0, hseg, hz, ho, hm, hh⟩ := hH
  rw [← hh] at hseg
  obtain ⟨T₁, h1, p1, p2, p3, p4⟩ := Spec.incr (x := x) t z o hzo l T hseg
    (by rw [hh, Nat.add_comm]; exact hz) (by rw [hh, Nat.add_comm]; exact ho) hT (by omega)
  rw [hh] at p1 p2 p4
  have hT₁ : T₁.Within B := fun i => by
    by_cases hi : i = t
    · subst hi; omega
    · rw [(p3.2 i hi).2]; exact hT i
  have hlen := binc_length l
  have h2 := Spec.home (x := x) t mk (T := T₁) (by rw [p2 0 (Or.inl (by omega))]; exact h0)
    (fun j hj1 hj2 => by
      by_cases hj : j ≤ l.length
      · rw [← hlen] at p1
        exact ne_of_seg hmz hmo p1 (by omega) (by rw [hlen]; omega)
      · rw [p2 j (Or.inr (by omega)), show j = l.length + 1 by omega]; exact hm)
    hT₁ (by omega)
  refine ⟨T₁.setHead t 1, h1.seq h2, ⟨?_, ?_, ?_, ?_, ?_, by simp⟩,
    p3.trans (Tapes.Frame.setHead t _ _), Tapes.within_setHead hT₁ (by omega)⟩
  · simp only [Tapes.setHead_tp]; rw [p2 0 (Or.inl (by omega))]; exact h0
  · simp only [Tapes.setHead_tp]; rw [hlen]; exact p1
  · simp only [Tapes.setHead_tp]; rw [hlen, p2 _ (Or.inr (by omega))]; exact hz
  · simp only [Tapes.setHead_tp]; rw [hlen, p2 _ (Or.inr (by omega))]; exact ho
  · simp only [Tapes.setHead_tp]; rw [hlen, p2 _ (Or.inr (by omega))]; exact hm

/-- In-place decrement of a counter, head returned home. -/
def decrH (t : Fin k) (mk z o : Γ) : Code k Γ := TM.decr t z o ++ TM.home t mk

theorem Spec.decrH {t : Fin k} (hzo : z ≠ o) (hmz : mk ≠ z) (hmo : mk ≠ o) {l : List Bool}
    {T : Tapes k Γ} (hH : Holds t mk z o T l) (hT : T.Within B) (hB : l.length + 2 ≤ B) :
    ∃ T', Spec (TM.decrH t mk z o) x B T T' ∧ Holds t mk z o T' (bdec l) ∧ T.Frame t T' ∧
      T'.Within B := by
  obtain ⟨h0, hseg, hz, ho, hm, hh⟩ := hH
  rw [← hh] at hseg
  obtain ⟨T₁, h1, p1, p2, p3, p4⟩ := Spec.decr (x := x) t z o hzo l T hseg
    (by rw [hh, Nat.add_comm]; exact hz) (by rw [hh, Nat.add_comm]; exact ho) hT (by omega)
  rw [hh] at p1 p2 p4
  have hT₁ : T₁.Within B := fun i => by
    by_cases hi : i = t
    · subst hi; omega
    · rw [(p3.2 i hi).2]; exact hT i
  have hlen := bdec_length l
  have h2 := Spec.home (x := x) t mk (T := T₁) (by rw [p2 0 (Or.inl (by omega))]; exact h0)
    (fun j hj1 hj2 => by
      by_cases hj : j ≤ l.length
      · rw [← hlen] at p1
        exact ne_of_seg hmz hmo p1 (by omega) (by rw [hlen]; omega)
      · rw [p2 j (Or.inr (by omega)), show j = l.length + 1 by omega]; exact hm)
    hT₁ (by omega)
  refine ⟨T₁.setHead t 1, h1.seq h2, ⟨?_, ?_, ?_, ?_, ?_, by simp⟩,
    p3.trans (Tapes.Frame.setHead t _ _), Tapes.within_setHead hT₁ (by omega)⟩
  · simp only [Tapes.setHead_tp]; rw [p2 0 (Or.inl (by omega))]; exact h0
  · simp only [Tapes.setHead_tp]; rw [hlen]; exact p1
  · simp only [Tapes.setHead_tp]; rw [hlen, p2 _ (Or.inr (by omega))]; exact hz
  · simp only [Tapes.setHead_tp]; rw [hlen, p2 _ (Or.inr (by omega))]; exact ho
  · simp only [Tapes.setHead_tp]; rw [hlen, p2 _ (Or.inr (by omega))]; exact hm

/-- Zero test of a counter into the flag cell under head `f`, counter head returned home. -/
def isZeroH (t f : Fin k) (mk z o yes no : Γ) : Code k Γ :=
  TM.isZeroB t f z o yes no ++ TM.home t mk

/-- What `isZeroH` guarantees. -/
def ZeroPost (t f : Fin k) (yes no : Γ) (l : List Bool) (T T' : Tapes k Γ) : Prop :=
  T'.tp f (T.hd f) = (if bval l = 0 then yes else no) ∧
  (∀ j, j ≠ T.hd f → T'.tp f j = T.tp f j) ∧
  T'.tp t = T.tp t ∧ T'.hd t = T.hd t ∧ T'.hd f = T.hd f ∧
  T.Agree (fun i => i = t ∨ i = f) T' ∧ T'.ih = T.ih

theorem Spec.isZeroH {t f : Fin k} (htf : t ≠ f) (hzo : z ≠ o) (hmz : mk ≠ z) (hmo : mk ≠ o)
    {yes no : Γ} {l : List Bool} {T : Tapes k Γ} (hH : Holds t mk z o T l)
    (hT : T.Within B) (hB : l.length + 2 ≤ B) :
    ∃ T', Spec (TM.isZeroH t f mk z o yes no) x B T T' ∧ ZeroPost t f yes no l T T' ∧
      T'.Within B := by
  obtain ⟨h0, hseg, hz, ho, hm, hh⟩ := hH
  rw [← hh] at hseg
  obtain ⟨T₁, h1, p1, p2, p3, p4, p5, p6, p7⟩ := Spec.isZeroB (x := x) (yes := yes) (no := no)
    htf hzo l T hseg (by rw [hh, Nat.add_comm]; exact hz) (by rw [hh, Nat.add_comm]; exact ho)
    hT (by omega)
  have hT₁ : T₁.Within B := fun i => by
    by_cases hi : i = t
    · subst hi; rw [p4, hh]; omega
    · by_cases hif : i = f
      · subst hif; rw [p5]; exact hT _
      · rw [(p6 i (by tauto)).2]; exact hT i
  have h2 := Spec.home (x := x) t mk (T := T₁) (by rw [p3]; exact h0)
    (fun j hj1 hj2 => by
      rw [p3]
      by_cases hj : j ≤ l.length
      · exact ne_of_seg (s := T.hd t) hmz hmo hseg (by omega) (by omega)
      · rw [show j = l.length + 1 by rw [p4, hh] at hj2; omega]; exact hm)
    hT₁ (by omega)
  refine ⟨T₁.setHead t 1, h1.seq h2, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    Tapes.within_setHead hT₁ (by omega)⟩
  · simpa using p1
  · intro j hj; simpa using p2 j hj
  · simpa using p3
  · simp [hh]
  · rw [Tapes.setHead_hd_ne _ _ (Ne.symm htf)]; exact p5
  · intro i hi
    have hit : i ≠ t := fun e => hi (Or.inl e)
    exact ⟨(p6 i hi).1, by rw [Tapes.setHead_hd_ne _ _ hit]; exact (p6 i hi).2⟩
  · exact p7

/-! ### A position-tracked input head -/

omit [DecidableEq Γ] in
theorem Spec.moveIn {d : Dir} {T : Tapes k Γ} (hT : T.Within B) :
    Spec [Instr.moveIn d] x B T (T.moveInput x.length d) :=
  Spec.single rfl hT hT

/-- The input-head invariant: `P` holds the position, which is at most `n + 1`, and
`n + 1` fits in the counter. -/
def InPos (P : Fin k) (mk z o : Γ) (x : List Bool) (T : Tapes k Γ) (l : List Bool) : Prop :=
  Holds P mk z o T l ∧ bval l = T.ih ∧ T.ih ≤ x.length + 1 ∧ x.length + 1 < 2 ^ l.length

omit [DecidableEq Γ] in
theorem Tapes.Frame.toAgree {t : Fin k} {S : Fin k → Prop} (hS : S t) {T T' : Tapes k Γ}
    (h : T.Frame t T') : T.Agree S T' :=
  fun i hi => h.2 i (fun e => hi (e ▸ hS))

omit [DecidableEq Γ] in
theorem Tapes.Agree.mono {S S' : Fin k → Prop} (hS : ∀ i, S i → S' i) {T T' : Tapes k Γ}
    (h : T.Agree S T') : T.Agree S' T' :=
  fun i hi => h i (fun e => hi (hS i e))

/-- Move the input head right, keeping counter `P` equal to its position. At the
right end marker (input symbol `none`, position `≠ 0`) nothing happens. -/
def inRight (P F : Fin k) (mk z o yes no : Γ) : Code k Γ :=
  ifElse (.input (fun i => i.isNone))
    (TM.isZeroH P F mk z o yes no ++
      ifElse (.tape F (fun g => decide (g = yes)))
        ([Instr.moveIn .right] ++ TM.incrH P mk z o) [])
    ([Instr.moveIn .right] ++ TM.incrH P mk z o)

theorem Spec.inRight {P F : Fin k} (hPF : P ≠ F) (hzo : z ≠ o) (hmz : mk ≠ z) (hmo : mk ≠ o)
    {yes no : Γ} (hyn : yes ≠ no) {l : List Bool} {T : Tapes k Γ}
    (hI : InPos P mk z o x T l) (hT : T.Within B) (hB : l.length + 2 ≤ B) :
    ∃ T' l', Spec (TM.inRight P F mk z o yes no) x B T T' ∧ InPos P mk z o x T' l' ∧
      l'.length = l.length ∧ T'.ih = Machine.moveIn x.length T.ih .right ∧
      T.Agree (fun i => i = P ∨ i = F) T' ∧ T'.hd F = T.hd F ∧ T'.Within B := by
  obtain ⟨hH, hval, hle, hfit⟩ := hI
  have mv : ∀ T₀ : Tapes k Γ, Holds P mk z o T₀ l → T₀.ih = T.ih → T₀.Within B →
      T.ih < x.length + 1 → ∃ T', Spec ([Instr.moveIn .right] ++ TM.incrH P mk z o) x B T₀ T' ∧
        Holds P mk z o T' (binc l) ∧ T₀.Agree (fun i => i = P) T' ∧ T'.ih = T.ih + 1 ∧
        T'.Within B := by
    intro T₀ hH₀ hih₀ hT₀ hlt
    have hH₁ : Holds P mk z o (T₀.moveInput x.length .right) l := hH₀.congr rfl rfl
    obtain ⟨T', h, hH', hfr, hW'⟩ := Spec.incrH (x := x) hzo hmz hmo hH₁ hT₀ hB
    refine ⟨T', (Spec.moveIn hT₀).seq h, hH', fun i hi => hfr.2 i hi, ?_, hW'⟩
    rw [hfr.1]; simp only [Tapes.moveInput, Machine.moveIn, hih₀]; omega
  have hbinc : T.ih < x.length + 1 → bval (binc l) = T.ih + 1 := fun h => by
    rw [bval_binc l (by omega), hval]
  by_cases hnone : inputSym x T.ih = none
  · have hcond : Cond.eval x T (.input (fun i => i.isNone)) = true := by
      simp [Cond.eval, hnone]
    obtain ⟨T₁, hz1, ⟨q1, q2, q3, q4, q5, q6, q7⟩, hW1⟩ :=
      Spec.isZeroH (x := x) (yes := yes) (no := no) (f := F) hPF hzo hmz hmo hH hT hB
    have hH₁ : Holds P mk z o T₁ l := hH.congr q3 q4
    rcases (inputSym_eq_none x T.ih).1 hnone with h0 | hgt
    · -- at position 0: move right
      have hflag : T₁.read F = yes := by
        rw [Tapes.read, q5, q1, ite_pos' (by rw [hval, h0])]
      obtain ⟨T', hmv, hH', hag, hih', hW'⟩ := mv T₁ hH₁ q7 hW1 (by omega)
      refine ⟨T', binc l, Spec.ifElse_true hcond hT (hz1.seq
        (Spec.ifElse_true (by simp [Cond.eval, hflag]) hW1 hmv)),
        ⟨hH', by rw [hbinc (by omega), hih'], by omega, by rw [binc_length]; exact hfit⟩,
        binc_length l, by rw [hih', h0]; simp [Machine.moveIn],
        q6.trans (hag.mono (fun i h => Or.inl h)), ?_, hW'⟩
      rw [← q5]; exact (hag F (Ne.symm hPF)).2
    · -- at the right end marker: stay
      have hih : T.ih = x.length + 1 := by omega
      have hflag : T₁.read F = no := by
        rw [Tapes.read, q5, q1, ite_neg' (by rw [hval]; omega)]
      refine ⟨T₁, l, Spec.ifElse_true hcond hT (hz1.seq
        (Spec.ifElse_false (by simp [Cond.eval, hflag, Ne.symm hyn]) hW1 (Spec.nil hW1))),
        ⟨hH₁, by rw [q7]; exact hval, by rw [q7]; exact hle, hfit⟩, rfl,
        by rw [q7, hih]; simp [Machine.moveIn], q6, q5, hW1⟩
  · -- on an input symbol: move right
    have hcond : Cond.eval x T (.input (fun i => i.isNone)) = false := by
      simp [Cond.eval, Option.isSome_iff_ne_none, hnone]
    have hpos : T.ih ≤ x.length := by
      rw [inputSym_eq_none] at hnone; omega
    obtain ⟨T', hmv, hH', hag, hih', hW'⟩ := mv T hH rfl hT (by omega)
    refine ⟨T', binc l, Spec.ifElse_false hcond hT hmv,
      ⟨hH', by rw [hbinc (by omega), hih'], by omega, by rw [binc_length]; exact hfit⟩,
      binc_length l, by rw [hih']; simp [Machine.moveIn]; omega,
      hag.mono (fun i h => Or.inl h), (hag F (Ne.symm hPF)).2, hW'⟩

/-- Move the input head left, keeping counter `P` equal to its position. At
position 0 nothing happens. -/
def inLeft (P F : Fin k) (mk z o yes no : Γ) : Code k Γ :=
  TM.isZeroH P F mk z o yes no ++
    ifElse (.tape F (fun g => decide (g = yes))) [] ([Instr.moveIn .left] ++ TM.decrH P mk z o)

theorem Spec.inLeft {P F : Fin k} (hPF : P ≠ F) (hzo : z ≠ o) (hmz : mk ≠ z) (hmo : mk ≠ o)
    {yes no : Γ} (hyn : yes ≠ no) {l : List Bool} {T : Tapes k Γ}
    (hI : InPos P mk z o x T l) (hT : T.Within B) (hB : l.length + 2 ≤ B) :
    ∃ T' l', Spec (TM.inLeft P F mk z o yes no) x B T T' ∧ InPos P mk z o x T' l' ∧
      l'.length = l.length ∧ T'.ih = Machine.moveIn x.length T.ih .left ∧
      T.Agree (fun i => i = P ∨ i = F) T' ∧ T'.hd F = T.hd F ∧ T'.Within B := by
  obtain ⟨hH, hval, hle, hfit⟩ := hI
  obtain ⟨T₁, hz1, ⟨q1, q2, q3, q4, q5, q6, q7⟩, hW1⟩ :=
    Spec.isZeroH (x := x) (yes := yes) (no := no) (f := F) hPF hzo hmz hmo hH hT hB
  have hH₁ : Holds P mk z o T₁ l := hH.congr q3 q4
  by_cases h0 : T.ih = 0
  · have hflag : T₁.read F = yes := by
      rw [Tapes.read, q5, q1, ite_pos' (by rw [hval, h0])]
    refine ⟨T₁, l, hz1.seq (Spec.ifElse_true (by simp [Cond.eval, hflag]) hW1 (Spec.nil hW1)),
      ⟨hH₁, by rw [q7]; exact hval, by rw [q7]; exact hle, hfit⟩, rfl,
      by rw [q7, h0]; simp [Machine.moveIn], q6, q5, hW1⟩
  · have hflag : T₁.read F = no := by
      rw [Tapes.read, q5, q1, ite_neg' (by rw [hval]; exact h0)]
    have hH₂ : Holds P mk z o (T₁.moveInput x.length .left) l := hH₁.congr rfl rfl
    obtain ⟨T', hd, hH', hfr, hW'⟩ := Spec.decrH (x := x) hzo hmz hmo hH₂ hW1 hB
    have hih' : T'.ih = T.ih - 1 := by
      rw [hfr.1]; simp only [Tapes.moveInput, Machine.moveIn, q7]
    refine ⟨T', bdec l, hz1.seq (Spec.ifElse_false (by simp [Cond.eval, hflag, Ne.symm hyn])
        hW1 ((Spec.moveIn hW1).seq hd)),
      ⟨hH', by rw [bval_bdec l (by rw [hval]; omega), hval, hih'], by omega,
        by rw [bdec_length]; exact hfit⟩,
      bdec_length l, by rw [hih']; simp [Machine.moveIn],
      q6.trans (fun i hi => hfr.2 i (fun e => hi (Or.inl e))), ?_, hW'⟩
    rw [← q5]; exact (hfr.2 F (Ne.symm hPF)).2

/-! ### Seeking: move the input head right `c` times -/

def seekBody (C P F : Fin k) (mk z o yes no : Γ) : Code k Γ :=
  TM.decrH C mk z o ++ TM.inRight P F mk z o yes no ++ TM.isZeroH C F mk z o yes no

/-- Move the input head right `c` times (clamped at the right end), where counter
`C` holds `c`; counter `P` keeps tracking the position. `C` ends at zero. -/
def seekIn (C P F : Fin k) (mk z o yes no : Γ) : Code k Γ :=
  TM.isZeroH C F mk z o yes no ++
    whileDo (.tape F (fun g => decide (g = no))) (seekBody C P F mk z o yes no)

theorem seek_aux {C P F : Fin k} (hCP : C ≠ P) (hCF : C ≠ F) (hPF : P ≠ F) (hzo : z ≠ o)
    (hmz : mk ≠ z) (hmo : mk ≠ o) {yes no : Γ} (hyn : yes ≠ no) :
    ∀ (c : ℕ) (lc lp : List Bool) (T : Tapes k Γ), bval lc = c → Holds C mk z o T lc →
      InPos P mk z o x T lp → T.read F = (if c = 0 then yes else no) → T.Within B →
      lc.length + 2 ≤ B → lp.length + 2 ≤ B →
      ∃ T' lp' lc', Loop (.tape F (fun g => decide (g = no))) (seekBody C P F mk z o yes no)
          x B T T' ∧ InPos P mk z o x T' lp' ∧ lp'.length = lp.length ∧
        T'.ih = min (T.ih + c) (x.length + 1) ∧ Holds C mk z o T' lc' ∧
        lc'.length = lc.length ∧ bval lc' = 0 ∧
        T.Agree (fun i => i = C ∨ i = P ∨ i = F) T' ∧ T'.hd F = T.hd F ∧ T'.Within B
  | 0, lc, lp, T, hc, hC, hP, hF, hT, _, _ => by
    refine ⟨T, lp, lc, .stop (by simp [Cond.eval, hF, hyn]) hT, hP, rfl, ?_, hC, rfl, hc,
      Tapes.Agree.refl _ T, rfl, hT⟩
    have := hP.2.2.1; omega
  | c + 1, lc, lp, T, hc, hC, hP, hF, hT, hBc, hBp => by
    -- decrement `C`
    obtain ⟨T₁, s1, hC₁, hfr₁, hW₁⟩ := Spec.decrH (x := x) hzo hmz hmo hC hT hBc
    have hP₁ : InPos P mk z o x T₁ lp :=
      ⟨hP.1.congr (hfr₁.2 P (Ne.symm hCP)).1 (hfr₁.2 P (Ne.symm hCP)).2,
        by rw [hfr₁.1]; exact hP.2.1, by rw [hfr₁.1]; exact hP.2.2.1, hP.2.2.2⟩
    have hval₁ : bval (bdec lc) = c := by rw [bval_bdec lc (by omega), hc]; rfl
    -- move the input head
    obtain ⟨T₂, lp₂, s2, hP₂, hlen₂, hih₂, hag₂, hF₂, hW₂⟩ :=
      Spec.inRight (x := x) (yes := yes) (no := no) hPF hzo hmz hmo hyn hP₁ hW₁ hBp
    have hC₂ : Holds C mk z o T₂ (bdec lc) :=
      hC₁.congr (hag₂ C (fun h => h.elim hCP hCF)).1 (hag₂ C (fun h => h.elim hCP hCF)).2
    -- test `C` for zero
    obtain ⟨T₃, s3, ⟨q1, q2, q3, q4, q5, q6, q7⟩, hW₃⟩ :=
      Spec.isZeroH (x := x) (yes := yes) (no := no) (f := F) hCF hzo hmz hmo hC₂ hW₂
        (by rw [bdec_length]; exact hBc)
    have hC₃ : Holds C mk z o T₃ (bdec lc) := hC₂.congr q3 q4
    have hP₃ : InPos P mk z o x T₃ lp₂ :=
      ⟨hP₂.1.congr (q6 P (fun h => h.elim (fun e => hCP e.symm) hPF)).1
        (q6 P (fun h => h.elim (fun e => hCP e.symm) hPF)).2,
        by rw [q7]; exact hP₂.2.1, by rw [q7]; exact hP₂.2.2.1, hP₂.2.2.2⟩
    have hF₃ : T₃.read F = (if c = 0 then yes else no) := by
      rw [Tapes.read, q5, q1, hval₁]
    obtain ⟨T', lp', lc', hloop, hP', hlen', hih', hC', hlenc', hz', hag', hF', hW'⟩ :=
      seek_aux hCP hCF hPF hzo hmz hmo hyn c (bdec lc) lp₂ T₃ hval₁ hC₃ hP₃ hF₃ hW₃
        (by rw [bdec_length]; exact hBc) (by rw [hlen₂]; exact hBp)
    refine ⟨T', lp', lc', .iter (by simp [Cond.eval, hF]) hT ((s1.seq s2).seq s3) hloop,
      hP', by rw [hlen', hlen₂], ?_, hC', by rw [hlenc', bdec_length], hz', ?_, ?_, hW'⟩
    · rw [hih', q7, hih₂, hfr₁.1]
      have := hP.2.2.1
      simp only [Machine.moveIn]
      omega
    · exact ((hfr₁.toAgree (Or.inl rfl)).trans
        ((hag₂.mono (fun _ h => Or.inr h)).trans
          (q6.mono (fun _ h => h.elim Or.inl (fun h => Or.inr (Or.inr h)))))).trans hag'
    · rw [hF', q5, hF₂, (hfr₁.2 F (Ne.symm hCF)).2]

/-- **Seek.** With counter `C` holding `c`, `seekIn` moves the input head to
`min (ih + c) (n + 1)`, keeping `P` equal to the position, and leaves `C` at zero. -/
theorem Spec.seekIn {C P F : Fin k} (hCP : C ≠ P) (hCF : C ≠ F) (hPF : P ≠ F) (hzo : z ≠ o)
    (hmz : mk ≠ z) (hmo : mk ≠ o) {yes no : Γ} (hyn : yes ≠ no) {lc lp : List Bool}
    {T : Tapes k Γ} (hC : Holds C mk z o T lc) (hP : InPos P mk z o x T lp) (hT : T.Within B)
    (hBc : lc.length + 2 ≤ B) (hBp : lp.length + 2 ≤ B) :
    ∃ T' lp' lc', Spec (TM.seekIn C P F mk z o yes no) x B T T' ∧ InPos P mk z o x T' lp' ∧
      lp'.length = lp.length ∧ T'.ih = min (T.ih + bval lc) (x.length + 1) ∧
      Holds C mk z o T' lc' ∧ lc'.length = lc.length ∧ bval lc' = 0 ∧
      T.Agree (fun i => i = C ∨ i = P ∨ i = F) T' ∧ T'.hd F = T.hd F ∧ T'.Within B := by
  obtain ⟨T₀, s0, ⟨q1, q2, q3, q4, q5, q6, q7⟩, hW₀⟩ :=
    Spec.isZeroH (x := x) (yes := yes) (no := no) (f := F) hCF hzo hmz hmo hC hT hBc
  have hC₀ : Holds C mk z o T₀ lc := hC.congr q3 q4
  have hP₀ : InPos P mk z o x T₀ lp :=
    ⟨hP.1.congr (q6 P (fun h => h.elim (fun e => hCP e.symm) hPF)).1
      (q6 P (fun h => h.elim (fun e => hCP e.symm) hPF)).2,
      by rw [q7]; exact hP.2.1, by rw [q7]; exact hP.2.2.1, hP.2.2.2⟩
  obtain ⟨T', lp', lc', hloop, hP', hlen', hih', hC', hlenc', hz', hag', hF', hW'⟩ :=
    seek_aux hCP hCF hPF hzo hmz hmo hyn (bval lc) lc lp T₀ rfl hC₀ hP₀
      (by rw [Tapes.read, q5, q1]) hW₀ hBc hBp
  refine ⟨T', lp', lc', s0.seq (Spec.whileDo hloop), hP', hlen', by rw [hih', q7], hC', hlenc',
    hz', (q6.mono (fun _ h => h.elim Or.inl (fun h => Or.inr (Or.inr h)))).trans hag', by rw [hF', q5], hW'⟩

/-! ### Rewinding the input head to position 0 -/

def rewindBody (P F : Fin k) (mk z o yes no : Γ) : Code k Γ :=
  TM.inLeft P F mk z o yes no ++ TM.isZeroH P F mk z o yes no

/-- Move the input head back to position 0, keeping `P` equal to its position. -/
def rewindIn (P F : Fin k) (mk z o yes no : Γ) : Code k Γ :=
  TM.isZeroH P F mk z o yes no ++
    whileDo (.tape F (fun g => decide (g = no))) (rewindBody P F mk z o yes no)

theorem rewind_aux {P F : Fin k} (hPF : P ≠ F) (hzo : z ≠ o) (hmz : mk ≠ z) (hmo : mk ≠ o)
    {yes no : Γ} (hyn : yes ≠ no) :
    ∀ (c : ℕ) (lp : List Bool) (T : Tapes k Γ), T.ih = c → InPos P mk z o x T lp →
      T.read F = (if c = 0 then yes else no) → T.Within B → lp.length + 2 ≤ B →
      ∃ T' lp', Loop (.tape F (fun g => decide (g = no))) (rewindBody P F mk z o yes no)
          x B T T' ∧ InPos P mk z o x T' lp' ∧ lp'.length = lp.length ∧ T'.ih = 0 ∧
        T.Agree (fun i => i = P ∨ i = F) T' ∧ T'.hd F = T.hd F ∧ T'.Within B
  | 0, lp, T, hc, hP, hF, hT, _ => by
    exact ⟨T, lp, .stop (by simp [Cond.eval, hF, hyn]) hT, hP, rfl, hc,
      Tapes.Agree.refl _ T, rfl, hT⟩
  | c + 1, lp, T, hc, hP, hF, hT, hBp => by
    obtain ⟨T₁, lp₁, s1, hP₁, hlen₁, hih₁, hag₁, hF₁, hW₁⟩ :=
      Spec.inLeft (x := x) (yes := yes) (no := no) hPF hzo hmz hmo hyn hP hT hBp
    obtain ⟨T₂, s2, ⟨q1, q2, q3, q4, q5, q6, q7⟩, hW₂⟩ :=
      Spec.isZeroH (x := x) (yes := yes) (no := no) (f := F) hPF hzo hmz hmo hP₁.1 hW₁
        (by rw [hlen₁]; exact hBp)
    have hP₂ : InPos P mk z o x T₂ lp₁ :=
      ⟨hP₁.1.congr q3 q4, by rw [q7]; exact hP₁.2.1, by rw [q7]; exact hP₁.2.2.1, hP₁.2.2.2⟩
    have hih₂ : T₂.ih = c := by rw [q7, hih₁, hc]; simp [Machine.moveIn]
    have hF₂ : T₂.read F = (if c = 0 then yes else no) := by
      rw [Tapes.read, q5, q1, hP₁.2.1, hih₁, hc]; simp [Machine.moveIn]
    obtain ⟨T', lp', hloop, hP', hlen', hih', hag', hF', hW'⟩ :=
      rewind_aux hPF hzo hmz hmo hyn c lp₁ T₂ hih₂ hP₂ hF₂ hW₂ (by rw [hlen₁]; exact hBp)
    refine ⟨T', lp', .iter (by simp [Cond.eval, hF]) hT (s1.seq s2) hloop, hP',
      by rw [hlen', hlen₁], hih', (hag₁.trans q6).trans hag', ?_, hW'⟩
    rw [hF', q5, hF₁]

/-- **Rewind.** The input head returns to position 0, with `P` tracking it. -/
theorem Spec.rewindIn {P F : Fin k} (hPF : P ≠ F) (hzo : z ≠ o) (hmz : mk ≠ z) (hmo : mk ≠ o)
    {yes no : Γ} (hyn : yes ≠ no) {lp : List Bool} {T : Tapes k Γ}
    (hP : InPos P mk z o x T lp) (hT : T.Within B) (hBp : lp.length + 2 ≤ B) :
    ∃ T' lp', Spec (TM.rewindIn P F mk z o yes no) x B T T' ∧ InPos P mk z o x T' lp' ∧
      lp'.length = lp.length ∧ T'.ih = 0 ∧ T.Agree (fun i => i = P ∨ i = F) T' ∧
      T'.hd F = T.hd F ∧ T'.Within B := by
  obtain ⟨T₀, s0, ⟨q1, q2, q3, q4, q5, q6, q7⟩, hW₀⟩ :=
    Spec.isZeroH (x := x) (yes := yes) (no := no) (f := F) hPF hzo hmz hmo hP.1 hT hBp
  have hP₀ : InPos P mk z o x T₀ lp :=
    ⟨hP.1.congr q3 q4, by rw [q7]; exact hP.2.1, by rw [q7]; exact hP.2.2.1, hP.2.2.2⟩
  obtain ⟨T', lp', hloop, hP', hlen', hih', hag', hF', hW'⟩ :=
    rewind_aux hPF hzo hmz hmo hyn T₀.ih lp T₀ rfl hP₀
      (by rw [Tapes.read, q5, q1, hP.2.1, q7]) hW₀ hBp
  exact ⟨T', lp', s0.seq (Spec.whileDo hloop), hP', hlen', hih', q6.trans hag',
    by rw [hF', q5], hW'⟩

end Savitch.TM
