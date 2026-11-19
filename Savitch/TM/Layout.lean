import Savitch.TM.Input

/-!
# Blocks in the standard layout, and whole-block passes

Phase 4b-4 of the Savitch formalization (see `PLAN.md`).

`Lay t mk bl T l`: tape `t` has the marker `mk` in cell 0, the block `l` in cells
`1 … |l|`, the end symbol `bl` in the next cell, and its head parked at cell 1.

Whole-block passes, each returning its heads home:
* `copyPass a b p h`: block on `b` := block on `a` mapped by `h` (`Spec.copyPass`).
* `zipPass a b p F`: block on `a` := `zipWith F` of the blocks on `a` and `b`
  (`Spec.zipPass`).

Every routine that follows (building successor blocks, mark tracks) is a
sequence of such passes.
-/

set_option linter.unusedSectionVars false

namespace Savitch.TM

variable {k : ℕ} {Γ : Type} [DecidableEq Γ] [Fintype Γ] {x : List Bool} {B : ℕ}

/-- Tape `t` holds block `l` in the standard layout, head at cell 1. -/
def Lay (t : Fin k) (mk bl : Γ) (T : Tapes k Γ) (l : List Γ) : Prop :=
  T.tp t 0 = mk ∧ seg (T.tp t) 1 l.length = l ∧ T.tp t (l.length + 1) = bl ∧ T.hd t = 1

theorem Lay.congr {t : Fin k} {mk bl : Γ} {T T' : Tapes k Γ} {l : List Γ} (h : Lay t mk bl T l)
    (htp : T'.tp t = T.tp t) (hhd : T'.hd t = T.hd t) : Lay t mk bl T' l := by
  unfold Lay at *; rw [htp, hhd]; exact h

theorem Lay.cell {t : Fin k} {mk bl : Γ} {T : Tapes k Γ} {l : List Γ} (h : Lay t mk bl T l)
    {j : ℕ} (hj : j < l.length) : T.tp t (T.hd t + j) ∈ l := by
  rw [h.2.2.2, ← h.2.1]; exact mem_seg _ hj

theorem Lay.endCell {t : Fin k} {mk bl : Γ} {T : Tapes k Γ} {l : List Γ} (h : Lay t mk bl T l) :
    T.tp t (T.hd t + l.length) = bl := by
  rw [h.2.2.2, Nat.add_comm]; exact h.2.2.1

/-- Cells `1 … hd` hold no marker, so `home` works. -/
theorem home_ok {f : ℕ → Γ} {mk bl : Γ} {l : List Γ} (hmb : mk ≠ bl) (hml : ∀ g ∈ l, g ≠ mk)
    (hseg : seg f 1 l.length = l) (hend : f (l.length + 1) = bl) {hd : ℕ}
    (hhd : hd ≤ l.length + 1) : ∀ j, 0 < j → j ≤ hd → f j ≠ mk := by
  intro j h1 h2
  by_cases hj : j ≤ l.length
  · have := mem_seg f (s := 1) (n := l.length) (i := j - 1) (by omega)
    rw [show 1 + (j - 1) = j by omega, hseg] at this
    exact hml _ this
  · rw [show j = l.length + 1 by omega, hend]; exact Ne.symm hmb

theorem Tapes.copyMapRes_tp_b_out {a b : Fin k} {h : Γ → Γ} (T : Tapes k Γ) (m : ℕ) {j : ℕ}
    (hj : j < T.hd b ∨ T.hd b + m ≤ j) : (T.copyMapRes a b h m).tp b j = T.tp b j := by
  simp only [Tapes.copyMapRes, Function.update_self]
  rw [ite_neg' (by omega)]

/-! ### Copy pass -/

noncomputable def copyPass (a b : Fin k) (mk : Γ) (p : Γ → Bool) (h : Γ → Γ) : Code k Γ :=
  TM.copyMapWhile a b p h ++ TM.home a mk ++ TM.home b mk

/-- **Copy pass.** The block on `b` becomes the block on `a` mapped by `h`. -/
theorem Spec.copyPass {a b : Fin k} (hab : a ≠ b) {mk bl : Γ} (hmb : mk ≠ bl) {p : Γ → Bool}
    {h : Γ → Γ} {la lb : List Γ} {T : Tapes k Γ}
    (hA : Lay a mk bl T la) (hB' : Lay b mk bl T lb) (hlen : lb.length = la.length)
    (hp : ∀ g ∈ la, p g = true) (hpb : p bl = false) (hma : ∀ g ∈ la, g ≠ mk)
    (hmh : ∀ g ∈ la, h g ≠ mk) (hT : T.Within B) (hB : la.length + 2 ≤ B) :
    ∃ T', Spec (TM.copyPass a b mk p h) x B T T' ∧ Lay a mk bl T' la ∧
      Lay b mk bl T' (la.map h) ∧ T.Agree (fun i => i = b) T' ∧ T'.ih = T.ih ∧
      T'.Within B := by
  set L := la.length
  have hcp := Spec.copyMapWhile (x := x) hab p h L T
    (fun j hj => hp _ (hA.cell hj)) (by rw [hA.endCell]; exact hpb) hT
    (by rw [hA.2.2.2]; omega) (by rw [hB'.2.2.2]; omega)
  set T₁ := T.copyMapRes a b h L
  have hT₁a : T₁.tp a = T.tp a := Tapes.copyMapRes_tp_ne hab T L
  have hT₁hda : T₁.hd a = 1 + L := by rw [Tapes.copyMapRes_hd_a hab, hA.2.2.2]
  have hT₁hdb : T₁.hd b = 1 + L := by rw [Tapes.copyMapRes_hd_b, hB'.2.2.2]
  have hsegb : seg (T₁.tp b) 1 L = la.map h := by
    have := Tapes.seg_copyMapRes (a := a) (b := b) (h := h) T L
    rw [hB'.2.2.2, hA.2.2.2, hA.2.1] at this; exact this
  have hT₁b0 : T₁.tp b 0 = mk := by
    rw [Tapes.copyMapRes_tp_b_out T L (Or.inl (by rw [hB'.2.2.2]; omega))]; exact hB'.1
  have hT₁bend : T₁.tp b (L + 1) = bl := by
    rw [Tapes.copyMapRes_tp_b_out T L (Or.inr (by rw [hB'.2.2.2]; omega)), ← hlen]
    exact hB'.2.2.1
  have hW₁ : T₁.Within B := hcp.target_within
  -- home `a`
  have h2 := Spec.home (x := x) a mk (T := T₁) (by rw [hT₁a]; exact hA.1)
    (by rw [hT₁a]; exact home_ok hmb hma hA.2.1 hA.2.2.1 (by omega)) hW₁ (by omega)
  set T₂ := T₁.setHead a 1
  have hW₂ : T₂.Within B := Tapes.within_setHead hW₁ (by omega)
  -- home `b`
  have hlm : (la.map h).length = L := List.length_map h
  have h3 := Spec.home (x := x) b mk (T := T₂) (by simp only [T₂, Tapes.setHead_tp]; exact hT₁b0)
    (by
      simp only [T₂, Tapes.setHead_tp]
      rw [Tapes.setHead_hd_ne _ _ (Ne.symm hab)]
      refine home_ok (l := la.map h) hmb (fun g hg => ?_) (by rw [hlm]; exact hsegb)
        (by rw [hlm]; exact hT₁bend) (by rw [hlm]; omega)
      obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
      exact hmh g' hg')
    hW₂ (by omega)
  refine ⟨T₂.setHead b 1, (hcp.seq h2).seq h3, ?_, ?_, ?_, rfl, Tapes.within_setHead hW₂ (by omega)⟩
  · refine (hA.congr ?_ ?_)
    · simp only [T₂, Tapes.setHead_tp]; exact hT₁a
    · rw [Tapes.setHead_hd_ne _ _ hab]; simp [T₂, hA.2.2.2]
  · refine ⟨?_, ?_, ?_, by simp⟩
    · simp only [T₂, Tapes.setHead_tp]; exact hT₁b0
    · simp only [T₂, Tapes.setHead_tp]; rw [hlm]; exact hsegb
    · simp only [T₂, Tapes.setHead_tp]; rw [hlm]; exact hT₁bend
  · intro i hib
    refine ⟨?_, ?_⟩
    · simp only [T₂, Tapes.setHead_tp]; exact Tapes.copyMapRes_tp_ne hib T L
    · rw [Tapes.setHead_hd_ne _ _ hib]
      by_cases hia : i = a
      · subst hia; simp [T₂, hA.2.2.2]
      · rw [Tapes.setHead_hd_ne _ _ hia]; exact Tapes.copyMapRes_hd_ne hia hib T L

/-! ### Zip pass -/

noncomputable def zipPass (a b : Fin k) (mk : Γ) (p : Γ → Bool) (F : Γ → Γ → Γ) : Code k Γ :=
  TM.zipWhile a b p F ++ TM.home a mk ++ TM.home b mk

/-- **Zip pass.** The block on `a` becomes `zipWith F` of the blocks on `a` and `b`. -/
theorem Spec.zipPass {a b : Fin k} (hab : a ≠ b) {mk bl : Γ} (hmb : mk ≠ bl) {p : Γ → Bool}
    {F : Γ → Γ → Γ} {la lb : List Γ} {T : Tapes k Γ}
    (hA : Lay a mk bl T la) (hB' : Lay b mk bl T lb) (hlen : lb.length = la.length)
    (hp : ∀ g ∈ la, p g = true) (hpb : p bl = false) (hmb' : ∀ g ∈ lb, g ≠ mk)
    (hmz : ∀ g ∈ List.zipWith F la lb, g ≠ mk) (hT : T.Within B) (hB : la.length + 2 ≤ B) :
    ∃ T', Spec (TM.zipPass a b mk p F) x B T T' ∧ Lay a mk bl T' (List.zipWith F la lb) ∧
      Lay b mk bl T' lb ∧ T.Agree (fun i => i = a) T' ∧ T'.ih = T.ih ∧
      T'.Within B := by
  set L := la.length
  have hzp := Spec.zipWhile (x := x) hab p F L T
    (fun j hj => hp _ (hA.cell hj)) (by rw [hA.endCell]; exact hpb) hT
    (by rw [hA.2.2.2]; omega) (by rw [hB'.2.2.2]; omega)
  set T₁ := T.zipRes a b F L
  have hT₁b : T₁.tp b = T.tp b := Tapes.zipRes_tp_ne (Ne.symm hab) T L
  have hT₁hda : T₁.hd a = 1 + L := by rw [Tapes.zipRes_hd_a hab, hA.2.2.2]
  have hT₁hdb : T₁.hd b = 1 + L := by rw [Tapes.zipRes_hd_b, hB'.2.2.2]
  have hzl : (List.zipWith F la lb).length = L := by simp [List.length_zipWith, hlen, L]
  have hsega : seg (T₁.tp a) 1 L = List.zipWith F la lb := by
    have hsb : seg (T.tp b) 1 L = lb := by
      have : L = lb.length := hlen.symm
      rw [this]; exact hB'.2.1
    have := Tapes.seg_zipRes (a := a) (b := b) (F := F) T L
    rw [hA.2.2.2, hB'.2.2.2, hA.2.1, hsb] at this; exact this
  have hT₁a0 : T₁.tp a 0 = mk := by
    rw [Tapes.zipRes_tp_a_out T L (Or.inl (by rw [hA.2.2.2]; omega))]; exact hA.1
  have hT₁aend : T₁.tp a (L + 1) = bl := by
    rw [Tapes.zipRes_tp_a_out T L (Or.inr (by rw [hA.2.2.2]; omega))]; exact hA.2.2.1
  have hW₁ : T₁.Within B := hzp.target_within
  have h2 := Spec.home (x := x) a mk (T := T₁) hT₁a0
    (home_ok (l := List.zipWith F la lb) hmb hmz (by rw [hzl]; exact hsega)
      (by rw [hzl]; exact hT₁aend) (by rw [hzl]; omega)) hW₁ (by omega)
  set T₂ := T₁.setHead a 1
  have hW₂ : T₂.Within B := Tapes.within_setHead hW₁ (by omega)
  have h3 := Spec.home (x := x) b mk (T := T₂)
    (by simp only [T₂, Tapes.setHead_tp]; rw [hT₁b]; exact hB'.1)
    (by
      simp only [T₂, Tapes.setHead_tp]
      rw [Tapes.setHead_hd_ne _ _ (Ne.symm hab), hT₁b]
      exact home_ok hmb hmb' hB'.2.1 hB'.2.2.1 (by omega))
    hW₂ (by omega)
  refine ⟨T₂.setHead b 1, (hzp.seq h2).seq h3, ?_, ?_, ?_, rfl, Tapes.within_setHead hW₂ (by omega)⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [T₂, Tapes.setHead_tp]; exact hT₁a0
    · simp only [T₂, Tapes.setHead_tp]; rw [hzl]; exact hsega
    · simp only [T₂, Tapes.setHead_tp]; rw [hzl]; exact hT₁aend
    · rw [Tapes.setHead_hd_ne _ _ hab]; simp [T₂]
  · refine hB'.congr ?_ ?_
    · simp only [T₂, Tapes.setHead_tp]; exact hT₁b
    · simp [T₂, hB'.2.2.2]
  · intro i hia
    refine ⟨?_, ?_⟩
    · simp only [T₂, Tapes.setHead_tp]; exact Tapes.zipRes_tp_ne hia T L
    · by_cases hib : i = b
      · subst hib; simp [T₂, hB'.2.2.2]
      · rw [Tapes.setHead_hd_ne _ _ hib, Tapes.setHead_hd_ne _ _ hia]
        exact Tapes.zipRes_hd_ne hia hib T L

end Savitch.TM
