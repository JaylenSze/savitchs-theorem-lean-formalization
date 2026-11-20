import Savitch.Edge.Test

/-!
# Block stacks on tape

Phase 4b-5 of the Savitch formalization (see `PLAN.md`).

A **block stack** on tape `t` holds a list `bs` of digit blocks (bottom first), all
of length `L`: cell 0 is the marker, the blocks follow from cell 1, and the head
sits just after the top block (`StackLay`). A register `R` holding one block in the
standard layout serves as a ruler for moving `L` cells at a time.

* `pushBlk R t`: push the block held in `R` (`Spec.pushBlk`).
* `backBlk t R`: move the head of `t` back by `L` (`Spec.backBlk`), which pops the
  top block logically.
* `readTop t R`: copy the top block into `R`, leaving the stack unchanged (`Spec.readTop`).
-/

set_option linter.unusedSectionVars false

namespace Savitch.Edge

open TM Machine Machine.NTM

variable {Λ Γ : Type} [Fintype Λ] [Fintype Γ] [DecidableEq Λ] [DecidableEq Γ]
variable {k : ℕ} {x : List Bool} {B : ℕ}

theorem seg_append {α : Type} (f : ℕ → α) : ∀ (s a b : ℕ), seg f s (a + b) = seg f s a ++ seg f (s + a) b
  | s, 0, b => by simp [seg]
  | s, a + 1, b => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [seg, List.cons_append]
    rw [seg_append f (s + 1) a b, show s + 1 + a = s + (a + 1) by omega]

/-- Digit blocks as tape cells. -/
noncomputable def cellsOf (d : List (Fin (nR Λ Γ))) : List (Sym Λ Γ) := d.map symR

/-- Tape `t` holds the block stack `bs` (bottom first), head just after the top. -/
def StackLay (t : Fin k) (L : ℕ) (T : Tapes k (Sym Λ Γ)) (bs : List (List (Fin (nR Λ Γ)))) :
    Prop :=
  T.tp t 0 = .mk ∧ (∀ d ∈ bs, d.length = L) ∧
  seg (T.tp t) 1 (bs.length * L) = (bs.map cellsOf).flatten ∧ T.hd t = bs.length * L + 1

theorem flatten_length {bs : List (List (Fin (nR Λ Γ)))} {L : ℕ} (h : ∀ d ∈ bs, d.length = L) :
    ((bs.map (cellsOf (Λ := Λ) (Γ := Γ))).flatten).length = bs.length * L := by
  induction bs with
  | nil => simp
  | cons d bs ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    rw [ih (fun d' hd' => h d' (List.mem_cons_of_mem _ hd'))]
    simp [cellsOf, h d List.mem_cons_self, Nat.succ_mul, Nat.add_comm]

/-! ### Moving back one block -/

noncomputable def backBlk (t R : Fin k) : Code k (Sym Λ Γ) :=
  whileDo (.tape R isRec) ([Instr.move R .right] ++ [Instr.move t .left]) ++ TM.home R .mk

theorem back_aux {t R : Fin k} (htR : t ≠ R) :
    ∀ (m : ℕ) (T : Tapes k (Sym Λ Γ)), (∀ j < m, isRec (T.tp R (T.hd R + j)) = true) →
      isRec (T.tp R (T.hd R + m)) = false → T.Within B → T.hd R + m < B → m ≤ T.hd t →
      Loop (.tape R isRec) ([Instr.move R .right] ++ [Instr.move t .left]) x B T
        ((T.setHead R (T.hd R + m)).setHead t (T.hd t - m))
  | 0, T, _, hq, hT, _, _ => by
    simp only [Nat.add_zero, Nat.sub_zero, Tapes.setHead_self]
    exact .stop (by simpa [Cond.eval, Tapes.read] using hq) hT
  | m + 1, T, hp, hq, hT, hB, hm => by
    have hW₁ : (T.setHead R (T.hd R + 1)).Within B := Tapes.within_setHead hT (by omega)
    have hbody : Spec ([Instr.move R .right] ++ [Instr.move t .left]) x B T
        ((T.setHead R (T.hd R + 1)).setHead t (T.hd t - 1)) := by
      have h2 := Spec.moveLeft (x := x) (t := t) hW₁
      rw [Tapes.setHead_hd_ne _ _ htR] at h2
      exact (Spec.moveRight hT (by omega)).seq h2
    set T₁ := (T.setHead R (T.hd R + 1)).setHead t (T.hd t - 1)
    have hT₁R : T₁.hd R = T.hd R + 1 := by
      simp [T₁, Tapes.setHead_hd_ne _ _ (Ne.symm htR)]
    have hT₁t : T₁.hd t = T.hd t - 1 := by simp [T₁]
    have hT₁tp : T₁.tp = T.tp := rfl
    have hW₂ : T₁.Within B := Tapes.within_setHead hW₁ (by have := hT t; omega)
    refine .iter (by simpa [Cond.eval, Tapes.read] using hp 0 (by omega)) hT hbody ?_
    have := back_aux htR m T₁
      (fun j hj => by
        rw [hT₁R, hT₁tp, show T.hd R + 1 + j = T.hd R + (j + 1) by omega]
        exact hp (j + 1) (by omega))
      (by rw [hT₁R, hT₁tp, show T.hd R + 1 + m = T.hd R + (m + 1) by omega]; exact hq)
      hW₂ (by rw [hT₁R]; omega) (by rw [hT₁t]; omega)
    have e : (T₁.setHead R (T₁.hd R + m)).setHead t (T₁.hd t - m) =
        (T.setHead R (T.hd R + (m + 1))).setHead t (T.hd t - (m + 1)) := by
      rw [hT₁R, hT₁t]
      ext i
      · rfl
      · simp only [T₁, Tapes.setHead, Function.update_apply]
        split_ifs <;> omega
      · rfl
    rwa [e] at this

theorem Spec.backBlk {t R : Fin k} (htR : t ≠ R) {L : ℕ} {lr : List (Sym Λ Γ)}
    {T : Tapes k (Sym Λ Γ)} (hR : Lay R .mk .blank T lr) (hrec : ∀ g ∈ lr, isRec g = true)
    (hlr : lr.length = L) (hm : L ≤ T.hd t) (hT : T.Within B) (hB : L + 2 ≤ B) :
    Spec (Edge.backBlk t R) x B T (T.setHead t (T.hd t - L)) := by
  have hmb : (Sym.mk : Sym Λ Γ) ≠ .blank := fun h => by cases h
  have hl := back_aux (x := x) htR L T (fun j hj => hrec _ (by rw [← hlr] at hj; exact hR.cell hj))
    (by rw [← hlr, hR.endCell]; rfl) hT (by rw [hR.2.2.2]; omega) hm
  set T₁ := (T.setHead R (T.hd R + L)).setHead t (T.hd t - L)
  have hW₁ : T₁.Within B := (Spec.whileDo hl).target_within
  have hh := Spec.home (x := x) R .mk (T := T₁) (by simp [T₁]; exact hR.1)
    (by simp only [T₁, Tapes.setHead_tp, Tapes.setHead_hd_ne _ _ (Ne.symm htR),
          Tapes.setHead_hd_self]
        exact home_ok hmb (fun g hg => by
          have := hrec g hg; intro h; subst h; simp [isRec] at this) hR.2.1 hR.2.2.1
          (by rw [hR.2.2.2, hlr]; omega))
    hW₁ (by omega)
  have e : T₁.setHead R 1 = T.setHead t (T.hd t - L) := by
    ext i
    · rfl
    · simp only [T₁, Tapes.setHead, Function.update_apply]
      split_ifs <;> simp_all [hR.2.2.2]
    · rfl
  rw [← e]
  exact (Spec.whileDo hl).seq hh

/-! ### Pushing a block -/

noncomputable def pushBlk (R t : Fin k) : Code k (Sym Λ Γ) :=
  copyMapWhile R t isRec id ++ TM.home R .mk

theorem Spec.pushBlk {R t : Fin k} (hRt : R ≠ t) {L : ℕ} {d : List (Fin (nR Λ Γ))}
    {bs : List (List (Fin (nR Λ Γ)))} {T : Tapes k (Sym Λ Γ)}
    (hR : Lay R .mk .blank T (cellsOf d)) (hd : d.length = L) (hS : StackLay t L T bs)
    (hT : T.Within B) (hB : (bs.length + 1) * L + 2 ≤ B) :
    ∃ T', Spec (Edge.pushBlk R t) x B T T' ∧ Lay R .mk .blank T' (cellsOf d) ∧
      StackLay t L T' (bs ++ [d]) ∧ T.Agree (fun i => i = t) T' ∧ T'.ih = T.ih ∧
      T'.Within B := by
  have hmb : (Sym.mk : Sym Λ Γ) ≠ .blank := fun h => by cases h
  have hcl : (cellsOf (Λ := Λ) (Γ := Γ) d).length = L := by simp [cellsOf, hd]
  have hrec : ∀ g ∈ cellsOf (Λ := Λ) (Γ := Γ) d, isRec g = true := by
    intro g hg; obtain ⟨e, _, rfl⟩ := List.mem_map.1 hg; rfl
  have hmul : (bs.length + 1) * L = bs.length * L + L := Nat.succ_mul _ _
  have hc := Spec.copyMapWhile (x := x) hRt isRec id L T
    (fun j hj => hrec _ (by rw [← hcl] at hj; exact hR.cell hj))
    (by rw [← hcl, hR.endCell]; rfl) hT (by rw [hR.2.2.2]; omega) (by rw [hS.2.2.2]; omega)
  set T₁ := T.copyMapRes R t id L
  have hW₁ : T₁.Within B := hc.target_within
  have hT₁R : T₁.tp R = T.tp R := Tapes.copyMapRes_tp_ne hRt T L
  have hh := Spec.home (x := x) R .mk (T := T₁) (by rw [hT₁R]; exact hR.1)
    (by rw [hT₁R, Tapes.copyMapRes_hd_a hRt, hR.2.2.2]
        exact home_ok hmb (fun g hg => by
          obtain ⟨e, _, rfl⟩ := List.mem_map.1 hg; exact fun h => by simp [symR] at h)
          hR.2.1 hR.2.2.1 (by rw [hcl]; omega))
    hW₁ (by omega)
  refine ⟨T₁.setHead R 1, hc.seq hh, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, rfl,
    Tapes.within_setHead hW₁ (by omega)⟩
  · exact hR.congr (by simp [hT₁R]) (by simp [hR.2.2.2])
  · simp only [Tapes.setHead_tp]
    rw [Tapes.copyMapRes_tp_b_out T L (Or.inl (by rw [hS.2.2.2]; omega))]; exact hS.1
  · intro d' hd'
    rcases List.mem_append.1 hd' with h | h
    · exact hS.2.1 d' h
    · rw [List.mem_singleton.1 h]; exact hd
  · simp only [Tapes.setHead_tp, List.length_append, List.length_singleton]
    rw [hmul, seg_append]
    have h1 : seg (T₁.tp t) 1 (bs.length * L) = seg (T.tp t) 1 (bs.length * L) :=
      seg_congr (fun j _ h2 => Tapes.copyMapRes_tp_b_out T L (Or.inl (by rw [hS.2.2.2]; omega)))
    have h2 : seg (T₁.tp t) (1 + bs.length * L) L = cellsOf d := by
      have := Tapes.seg_copyMapRes (a := R) (b := t) (h := id) T L
      rw [hS.2.2.2, hR.2.2.2, show bs.length * L + 1 = 1 + bs.length * L by omega,
        List.map_id] at this
      have hsegR : seg (T.tp R) 1 L = cellsOf d := by have := hR.2.1; rwa [hcl] at this
      exact (show seg ((T.copyMapRes R t id L).tp t) (1 + bs.length * L) L = _ from this).trans
        hsegR
    rw [h1, h2, hS.2.2.1]
    simp
  · simp only [List.length_append, List.length_singleton]
    rw [Tapes.setHead_hd_ne _ _ (Ne.symm hRt), Tapes.copyMapRes_hd_b, hS.2.2.2, hmul]; omega
  · intro i hi
    refine ⟨Tapes.copyMapRes_tp_ne hi T L, ?_⟩
    by_cases hiR : i = R
    · subst hiR; simp [hR.2.2.2]
    · rw [Tapes.setHead_hd_ne _ _ hiR]; exact Tapes.copyMapRes_hd_ne hiR hi T L

/-! ### Reading and popping the top block -/

theorem seg_top {t : Fin k} {L : ℕ} {T : Tapes k (Sym Λ Γ)} {bs : List (List (Fin (nR Λ Γ)))}
    {d : List (Fin (nR Λ Γ))} (hS : StackLay t L T (bs ++ [d])) :
    seg (T.tp t) 1 (bs.length * L) = (bs.map cellsOf).flatten ∧
      seg (T.tp t) (1 + bs.length * L) L = cellsOf d := by
  obtain ⟨_, hlen, hseg, _⟩ := hS
  have hd : d.length = L := hlen d (List.mem_append_right _ List.mem_cons_self)
  have hbs : ∀ d' ∈ bs, d'.length = L := fun d' h => hlen d' (List.mem_append_left _ h)
  rw [List.length_append, List.length_singleton, Nat.succ_mul, seg_append] at hseg
  simp only [List.map_append, List.map_cons, List.map_nil, List.flatten_append,
    List.flatten_cons, List.flatten_nil, List.append_nil] at hseg
  have hl1 : (seg (T.tp t) 1 (bs.length * L)).length = ((bs.map cellsOf).flatten).length := by
    rw [seg_length, flatten_length hbs]
  exact List.append_inj hseg hl1

theorem StackLay.pop {t : Fin k} {L : ℕ} {T : Tapes k (Sym Λ Γ)}
    {bs : List (List (Fin (nR Λ Γ)))} {d : List (Fin (nR Λ Γ))} (hS : StackLay t L T (bs ++ [d])) :
    StackLay t L (T.setHead t (T.hd t - L)) bs := by
  refine ⟨hS.1, fun d' h => hS.2.1 d' (List.mem_append_left _ h), (seg_top hS).1, ?_⟩
  simp only [Tapes.setHead_hd_self, hS.2.2.2, List.length_append, List.length_singleton,
    Nat.succ_mul]
  omega

theorem zipWith_snd {α β : Type} : ∀ (l₁ : List α) (l₂ : List β), l₁.length = l₂.length →
    List.zipWith (fun _ b => b) l₁ l₂ = l₂
  | [], [], _ => rfl
  | _ :: l₁, _ :: l₂, h => by
    simp only [List.zipWith_cons_cons, List.cons.injEq, true_and]
    exact zipWith_snd l₁ l₂ (by simpa using h)

noncomputable def readTop (t R : Fin k) : Code k (Sym Λ Γ) :=
  Edge.backBlk t R ++ zipWhile R t isRec (fun _ b => b) ++ TM.home R .mk

theorem Spec.readTop {t R : Fin k} (htR : t ≠ R) {L : ℕ} {lr : List (Sym Λ Γ)}
    {bs : List (List (Fin (nR Λ Γ)))} {d : List (Fin (nR Λ Γ))} {T : Tapes k (Sym Λ Γ)}
    (hR : Lay R .mk .blank T lr) (hrec : ∀ g ∈ lr, isRec g = true) (hlr : lr.length = L)
    (hS : StackLay t L T (bs ++ [d])) (hT : T.Within B) (hB : (bs.length + 1) * L + 2 ≤ B) :
    ∃ T', Spec (Edge.readTop t R) x B T T' ∧ Lay R .mk .blank T' (cellsOf d) ∧
      StackLay t L T' (bs ++ [d]) ∧ T.Agree (fun i => i = R) T' ∧ T'.ih = T.ih ∧
      T'.Within B := by
  have hmb : (Sym.mk : Sym Λ Γ) ≠ .blank := fun h => by cases h
  have hd : d.length = L := hS.2.1 d (List.mem_append_right _ List.mem_cons_self)
  have hmul : (bs.length + 1) * L = bs.length * L + L := Nat.succ_mul _ _
  have hhd : T.hd t = bs.length * L + L + 1 := by
    rw [hS.2.2.2]; simp [List.length_append, hmul]
  have s1 := Spec.backBlk (x := x) htR hR hrec hlr (by omega) hT (by omega)
  set T₁ := T.setHead t (T.hd t - L)
  have hW₁ : T₁.Within B := s1.target_within
  have hT₁t : T₁.hd t = 1 + bs.length * L := by simp [T₁]; omega
  have hT₁R : T₁.hd R = 1 := by simp [T₁, Tapes.setHead_hd_ne _ _ (Ne.symm htR), hR.2.2.2]
  have hR₁ : Lay R .mk .blank T₁ lr := hR.congr rfl (by rw [hT₁R, hR.2.2.2])
  have s2 := Spec.zipWhile (x := x) (Ne.symm htR) isRec (fun _ b => b) L T₁
    (fun j hj => hrec _ (by rw [← hlr] at hj; exact hR₁.cell hj))
    (by rw [← hlr, hR₁.endCell]; rfl) hW₁ (by rw [hT₁R]; omega) (by rw [hT₁t]; omega)
  set T₂ := T₁.zipRes R t (fun _ b => b) L
  have hW₂ : T₂.Within B := s2.target_within
  have hT₂t : T₂.tp t = T.tp t := Tapes.zipRes_tp_ne htR T₁ L
  have hsegR : seg (T₂.tp R) 1 L = cellsOf d := by
    have := Tapes.seg_zipRes (a := R) (b := t) (F := fun _ b => b) T₁ L
    rw [hT₁R, hT₁t, zipWith_snd _ _ (by rw [seg_length, seg_length])] at this
    exact (show seg ((T₁.zipRes R t (fun _ b => b) L).tp R) 1 L = _ from this).trans
      (by rw [show T₁.tp t = T.tp t from rfl]; exact (seg_top hS).2)
  have hcl : (cellsOf (Λ := Λ) (Γ := Γ) d).length = L := by simp [cellsOf, hd]
  have hT₂R0 : T₂.tp R 0 = .mk := by
    rw [Tapes.zipRes_tp_a_out T₁ L (Or.inl (by rw [hT₁R]; omega))]; exact hR.1
  have hT₂Rend : T₂.tp R (L + 1) = .blank := by
    rw [Tapes.zipRes_tp_a_out T₁ L (Or.inr (by rw [hT₁R]; omega))]
    have := hR.2.2.1; rwa [hlr] at this
  have hh := Spec.home (x := x) R .mk (T := T₂) hT₂R0
    (home_ok (l := cellsOf d) hmb (fun g hg => by
        obtain ⟨e, _, rfl⟩ := List.mem_map.1 hg; exact fun h => by simp [symR] at h)
      (by rw [hcl]; exact hsegR) (by rw [hcl]; exact hT₂Rend)
      (by rw [Tapes.zipRes_hd_a (Ne.symm htR), hT₁R, hcl]; omega))
    hW₂ (by omega)
  refine ⟨T₂.setHead R 1, (s1.seq s2).seq hh, ⟨?_, ?_, ?_, by simp⟩, ⟨?_, hS.2.1, ?_, ?_⟩, ?_, ?_,
    Tapes.within_setHead hW₂ (by omega)⟩
  · simp only [Tapes.setHead_tp]; exact hT₂R0
  · simp only [Tapes.setHead_tp]; rw [hcl]; exact hsegR
  · simp only [Tapes.setHead_tp]; rw [hcl]; exact hT₂Rend
  · simp only [Tapes.setHead_tp, hT₂t]; exact hS.1
  · simp only [Tapes.setHead_tp, hT₂t]; exact hS.2.2.1
  · rw [Tapes.setHead_hd_ne _ _ htR, Tapes.zipRes_hd_b, hT₁t]
    simp only [List.length_append, List.length_singleton, hmul]; omega
  · intro i hi
    refine ⟨by simp [T₂, Tapes.zipRes_tp_ne hi, T₁], ?_⟩
    rw [Tapes.setHead_hd_ne _ _ hi]
    by_cases hit : i = t
    · subst hit; rw [Tapes.zipRes_hd_b, hT₁t, hhd]; omega
    · rw [Tapes.zipRes_hd_ne hi hit]; simp [T₁, Tapes.setHead_hd_ne _ _ hit]
  · simp [T₂, Tapes.zipRes, T₁]

/-! ### The phase stack -/

/-- Tape `t` holds the bit stack `ps` (bottom first), head just after the top. -/
def PhLay (t : Fin k) (T : Tapes k (Sym Λ Γ)) (ps : List Bool) : Prop :=
  T.tp t 0 = .mk ∧ seg (T.tp t) 1 ps.length = ps.map bit ∧ T.hd t = ps.length + 1

theorem PhLay.congr {t : Fin k} {T T' : Tapes k (Sym Λ Γ)} {ps : List Bool} (h : PhLay t T ps)
    (htp : T'.tp t = T.tp t) (hhd : T'.hd t = T.hd t) : PhLay t T' ps := by
  unfold PhLay at *; rw [htp, hhd]; exact h

theorem PhLay.top {t : Fin k} {T : Tapes k (Sym Λ Γ)} {ps : List Bool} {b : Bool}
    (h : PhLay t T (ps ++ [b])) : T.tp t (ps.length + 1) = bit b ∧
      seg (T.tp t) 1 ps.length = ps.map bit := by
  obtain ⟨_, hseg, _⟩ := h
  rw [List.length_append, List.length_singleton, seg_append] at hseg
  simp only [List.map_append, List.map_cons, List.map_nil, seg] at hseg
  have hl : (seg (T.tp t) 1 ps.length).length = (ps.map (bit (Λ := Λ) (Γ := Γ))).length := by
    rw [seg_length, List.length_map]
  obtain ⟨h1, h2⟩ := List.append_inj hseg hl
  refine ⟨?_, h1⟩
  simp only [List.cons.injEq] at h2
  rw [Nat.add_comm]; exact h2.1

def pushPh (t : Fin k) (b : Bool) : Code k (Sym Λ Γ) :=
  [Instr.write t (bit b)] ++ [Instr.move t .right]

theorem Spec.pushPh {t : Fin k} {ps : List Bool} (b : Bool) {T : Tapes k (Sym Λ Γ)}
    (hP : PhLay t T ps) (hT : T.Within B) (hB : ps.length + 2 < B) :
    ∃ T', Spec (Edge.pushPh t b) x B T T' ∧ PhLay t T' (ps ++ [b]) ∧
      T.Agree (fun i => i = t) T' ∧ T'.ih = T.ih ∧ T'.Within B := by
  have hW₁ : (T.write t (bit b)).Within B := Tapes.within_write hT
  have hhd : (T.write t (bit b)).hd t = ps.length + 1 := by simp [hP.2.2]
  have s := (Spec.write (x := x) (t := t) (g := bit b) hT).seq
    (Spec.moveRight hW₁ (by rw [hhd]; omega))
  refine ⟨_, s, ⟨?_, ?_, ?_⟩, fun i hi => ⟨by simp [Tapes.write, hi],
    by simp [Tapes.setHead_hd_ne _ _ hi]⟩, rfl, Tapes.within_setHead hW₁ (by rw [hhd]; omega)⟩
  · simp only [Tapes.setHead_tp, Tapes.write_tp_self, hP.2.2]
    rw [ite_neg' (by omega)]; exact hP.1
  · simp only [Tapes.setHead_tp, List.length_append, List.length_singleton]
    rw [seg_append, List.map_append]
    congr 1
    · rw [seg_congr (g := T.tp t) (fun j h1 h2 => by
        rw [Tapes.write_tp_self, ite_neg' (by rw [hP.2.2]; omega)])]
      exact hP.2.1
    · simp [seg, Tapes.write_tp_self, hP.2.2, Nat.add_comm]
  · simp [hhd]

def popPh (t : Fin k) : Code k (Sym Λ Γ) := [Instr.move t .left]

theorem Spec.popPh {t : Fin k} {ps : List Bool} {b : Bool} {T : Tapes k (Sym Λ Γ)}
    (hP : PhLay t T (ps ++ [b])) (hT : T.Within B) :
    Spec (Edge.popPh t) x B T (T.setHead t (T.hd t - 1)) ∧
      PhLay t (T.setHead t (T.hd t - 1)) ps := by
  refine ⟨Spec.moveLeft hT, hP.1, hP.top.2, ?_⟩
  simp [hP.2.2]

def setPh (t : Fin k) (b : Bool) : Code k (Sym Λ Γ) :=
  [Instr.move t .left] ++ Edge.pushPh t b

theorem Spec.setPh {t : Fin k} {ps : List Bool} {b₀ : Bool} (b : Bool) {T : Tapes k (Sym Λ Γ)}
    (hP : PhLay t T (ps ++ [b₀])) (hT : T.Within B) (hB : ps.length + 3 < B) :
    ∃ T', Spec (Edge.setPh t b) x B T T' ∧ PhLay t T' (ps ++ [b]) ∧
      T.Agree (fun i => i = t) T' ∧ T'.ih = T.ih ∧ T'.Within B := by
  obtain ⟨s1, hP₁⟩ := Spec.popPh (x := x) hP hT
  have hW₁ : (T.setHead t (T.hd t - 1)).Within B :=
    Tapes.within_setHead hT (by have := hT t; omega)
  obtain ⟨T', s2, hP', ag, ih, hW'⟩ := Spec.pushPh (x := x) b hP₁ hW₁ (by omega)
  refine ⟨T', s1.seq s2, hP', ?_, ih, hW'⟩
  intro i hi
  exact ⟨(ag i hi).1, by rw [(ag i hi).2, Tapes.setHead_hd_ne _ _ hi]⟩

theorem step_back {t : Fin k} {T : Tapes k (Sym Λ Γ)} (hT : T.Within B) (h1 : 1 ≤ T.hd t) :
    Spec [Instr.move t .right] x B (T.setHead t (T.hd t - 1)) T := by
  have hW₁ : (T.setHead t (T.hd t - 1)).Within B :=
    Tapes.within_setHead hT (by have := hT t; omega)
  have := Spec.moveRight (x := x) (t := t) hW₁
    (by simp only [Tapes.setHead_hd_self]; have := hT t; omega)
  rwa [Tapes.setHead_hd_self, Tapes.setHead_setHead, show T.hd t - 1 + 1 = T.hd t by omega,
    Tapes.setHead_self] at this

/-- Branch on the top phase bit (stack nonempty). -/
def phBranch (t : Fin k) (cR cL : Code k (Sym Λ Γ)) : Code k (Sym Λ Γ) :=
  [Instr.move t .left] ++
    ifElse (.tape t isO) ([Instr.move t .right] ++ cR) ([Instr.move t .right] ++ cL)

theorem Spec.phBranch {t : Fin k} {ps : List Bool} {b : Bool} {T T' : Tapes k (Sym Λ Γ)}
    {cR cL : Code k (Sym Λ Γ)} (hP : PhLay t T (ps ++ [b])) (hT : T.Within B)
    (h : Spec (if b then cR else cL) x B T T') : Spec (Edge.phBranch t cR cL) x B T T' := by
  have hpos : T.hd t = ps.length + 2 := by rw [hP.2.2]; simp
  have hW₁ : (T.setHead t (T.hd t - 1)).Within B :=
    Tapes.within_setHead hT (by have := hT t; omega)
  have hcell : (T.setHead t (T.hd t - 1)).read t = bit b := by
    simp only [Tapes.read, Tapes.setHead_tp, Tapes.setHead_hd_self, hpos]
    exact hP.top.1
  have s2 := step_back (x := x) (t := t) hT (by omega)
  refine (Spec.moveLeft hT).seq ?_
  cases b
  · exact Spec.ifElse_false (by simp [Cond.eval, hcell, isO, bit, bsym]) hW₁ (s2.seq h)
  · exact Spec.ifElse_true (by simp [Cond.eval, hcell, isO, bit, bsym]) hW₁ (s2.seq h)

/-- Branch on whether the phase stack is empty. -/
def emptyBranch (t : Fin k) (cE cN : Code k (Sym Λ Γ)) : Code k (Sym Λ Γ) :=
  [Instr.move t .left] ++
    ifElse (.tape t isMk) ([Instr.move t .right] ++ cE) ([Instr.move t .right] ++ cN)

theorem Spec.emptyBranch {t : Fin k} {ps : List Bool} {T T' : Tapes k (Sym Λ Γ)}
    {cE cN : Code k (Sym Λ Γ)} (hP : PhLay t T ps) (hT : T.Within B)
    (h : Spec (if ps = [] then cE else cN) x B T T') : Spec (Edge.emptyBranch t cE cN) x B T T' := by
  have hW₁ : (T.setHead t (T.hd t - 1)).Within B :=
    Tapes.within_setHead hT (by have := hT t; omega)
  have s2 := step_back (x := x) (t := t) hT (by rw [hP.2.2]; omega)
  refine (Spec.moveLeft hT).seq ?_
  by_cases hps : ps = []
  · subst hps
    have hcell : (T.setHead t (T.hd t - 1)).read t = .mk := by
      simp only [Tapes.read, Tapes.setHead_tp, Tapes.setHead_hd_self, hP.2.2]; exact hP.1
    rw [ite_pos' rfl] at h
    exact Spec.ifElse_true (by simp [Cond.eval, hcell, isMk]) hW₁ (s2.seq h)
  · obtain ⟨ps', b, rfl⟩ := (List.eq_nil_or_concat ps).resolve_left hps
    rw [List.concat_eq_append] at hP h hps
    have hcell : (T.setHead t (T.hd t - 1)).read t = bit b := by
      simp only [Tapes.read, Tapes.setHead_tp, Tapes.setHead_hd_self, hP.2.2, List.length_append,
        List.length_singleton, Nat.add_sub_cancel]
      exact hP.top.1
    rw [ite_neg' hps] at h
    exact Spec.ifElse_false (by cases b <;> simp [Cond.eval, hcell, isMk, bit, bsym]) hW₁
      (s2.seq h)

end Savitch.Edge
