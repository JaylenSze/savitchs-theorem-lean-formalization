import Savitch.Sav.Stack
import Savitch.Space.Generic

/-!
# Representing the generic Phase 2 machine on tape

Phase 4b-5 of the Savitch formalization (see `PLAN.md`).

* `digs a`: the base-`|Rec|` digits of vertex `a`; on tape, `cellsOf (digs a)` is
  exactly the record block the edge test reads (`cellsOf_digs`).
* `StacksRep L T st`: the four stack tapes `tSA`, `tSB`, `tSC` (blocks) and `tSP`
  (phase bits) hold the frames `st`, bottom first.
* Composite operations: `popAll`, `pushAll` (push a whole frame), `zeroV` (load the
  zero vertex into `tV`), `incV` (increment the vertex in `tV`).
-/

set_option linter.unusedSectionVars false

namespace Savitch.Edge

open TM Machine Machine.NTM

variable {Λ Γ : Type} [Fintype Λ] [Fintype Γ] [DecidableEq Λ] [DecidableEq Γ]
variable {x : List Bool} {B : ℕ}

def tZ : Fin NT := 13
def tSA : Fin NT := 14
def tSB : Fin NT := 15
def tSC : Fin NT := 16
def tSP : Fin NT := 17
def tKc : Fin NT := 18
def tMd : Fin NT := 19
def tF₃ : Fin NT := 20
def tF₄ : Fin NT := 21

variable {L : ℕ}

/-! ### Vertices as digit lists -/

/-- The digits of a vertex. -/
noncomputable def digs (a : Fin (nV Λ Γ L)) : List (Fin (nR Λ Γ)) :=
  List.ofFn (finFunctionFinEquiv.symm a)

theorem digs_length (a : Fin (nV Λ Γ L)) : (digs a).length = L := List.length_ofFn

theorem dval_digs (a : Fin (nV Λ Γ L)) : dval (digs a) = a.val := by
  rw [digs, ← finFunctionFinEquiv_val, Equiv.apply_symm_apply]

theorem digs_inj {a b : Fin (nV Λ Γ L)} : digs a = digs b ↔ a = b :=
  ⟨fun h => Fin.ext (by rw [← dval_digs, h, dval_digs]), fun h => h ▸ rfl⟩

theorem cellsOf_digs (a : Fin (nV Λ Γ L)) :
    cellsOf (digs a) = (List.ofFn (recs a)).map Sym.rc := by
  rw [rc_digits]
  unfold cellsOf digs
  congr 1
  rw [List.map_ofFn]
  congr 1
  funext j
  simp [recs]

theorem cellsOf_rec (d : List (Fin (nR Λ Γ))) : ∀ g ∈ cellsOf (Λ := Λ) (Γ := Γ) d, isRec g = true := by
  intro g hg; obtain ⟨e, _, rfl⟩ := List.mem_map.1 hg; rfl

theorem cellsOf_not_mk (d : List (Fin (nR Λ Γ))) : ∀ g ∈ cellsOf (Λ := Λ) (Γ := Γ) d, g ≠ .mk := by
  intro g hg; obtain ⟨e, _, rfl⟩ := List.mem_map.1 hg; exact fun h => by simp [symR] at h

theorem cellsOf_length (d : List (Fin (nR Λ Γ))) : (cellsOf (Λ := Λ) (Γ := Γ) d).length = d.length :=
  List.length_map _

/-! ### Frames on the stack tapes -/

abbrev GF (Λ Γ : Type) [Fintype Λ] [Fintype Γ] (L : ℕ) := Gen.Frame (nV Λ Γ L)

def phBit (f : GF Λ Γ L) : Bool :=
  match f.phase with
  | .left => false
  | .right => true

/-- The four stack tapes hold the frames `st` (top first in `st`, bottom first on tape). -/
def StacksRep (L : ℕ) (T : Tapes NT (Sym Λ Γ)) (st : List (GF Λ Γ L)) : Prop :=
  StackLay tSA L T ((st.map fun f => digs f.a).reverse) ∧
  StackLay tSB L T ((st.map fun f => digs f.b).reverse) ∧
  StackLay tSC L T ((st.map fun f => digs f.c).reverse) ∧
  PhLay tSP T ((st.map phBit).reverse)

/-! ### Popping and pushing whole frames -/

noncomputable def popAll : Code NT (Sym Λ Γ) :=
  backBlk tSA tU ++ backBlk tSB tU ++ backBlk tSC tU ++ popPh tSP

theorem StacksRep.stackA_len {T : Tapes NT (Sym Λ Γ)} {f : GF Λ Γ L} {st : List (GF Λ Γ L)}
    (h : StacksRep L T (f :: st)) (t : Fin NT) (ht : t = tSA ∨ t = tSB ∨ t = tSC) :
    L ≤ T.hd t := by
  rcases ht with rfl | rfl | rfl
  · rw [h.1.2.2.2]; simp [Nat.succ_mul]; omega
  · rw [h.2.1.2.2.2]; simp [Nat.succ_mul]; omega
  · rw [h.2.2.1.2.2.2]; simp [Nat.succ_mul]; omega

theorem Spec.popAll {T : Tapes NT (Sym Λ Γ)} {f : GF Λ Γ L} {st : List (GF Λ Γ L)}
    {d : List (Fin (nR Λ Γ))} (hU : Lay tU .mk .blank T (cellsOf d)) (hd : d.length = L)
    (hS : StacksRep L T (f :: st)) (hT : T.Within B) (hB : L + 2 ≤ B) :
    ∃ T', Spec (popAll (Λ := Λ) (Γ := Γ)) x B T T' ∧ StacksRep L T' st ∧
      T.Agree (fun i => i = tSA ∨ i = tSB ∨ i = tSC ∨ i = tSP) T' ∧ T'.ih = T.ih ∧
      T'.Within B := by
  have hcl : (cellsOf (Λ := Λ) (Γ := Γ) d).length = L := by rw [cellsOf_length, hd]
  obtain ⟨hA, hB', hC, hP⟩ := hS
  simp only [List.map_cons, List.reverse_cons] at hA hB' hC hP
  -- A
  have s1 := Spec.backBlk (x := x) (t := tSA) (R := tU) (by decide) hU (cellsOf_rec d) hcl
    (by rw [hA.2.2.2]; simp [Nat.succ_mul]; omega) hT hB
  set T₁ := T.setHead tSA (T.hd tSA - L)
  have hW₁ : T₁.Within B := s1.target_within
  have hU₁ : Lay tU .mk .blank T₁ (cellsOf d) :=
    hU.congr rfl (Tapes.setHead_hd_ne _ _ (by decide) _)
  -- B
  have hB₁ : StackLay tSB L T₁ _ := ⟨hB'.1, hB'.2.1, hB'.2.2.1,
    by rw [Tapes.setHead_hd_ne _ _ (by decide)]; exact hB'.2.2.2⟩
  have s2 := Spec.backBlk (x := x) (t := tSB) (R := tU) (by decide) hU₁ (cellsOf_rec d) hcl
    (by rw [hB₁.2.2.2]; simp [Nat.succ_mul]; omega) hW₁ hB
  set T₂ := T₁.setHead tSB (T₁.hd tSB - L)
  have hW₂ : T₂.Within B := s2.target_within
  have hU₂ : Lay tU .mk .blank T₂ (cellsOf d) :=
    hU₁.congr rfl (Tapes.setHead_hd_ne _ _ (by decide) _)
  -- C
  have hC₂ : StackLay tSC L T₂ _ := ⟨hC.1, hC.2.1, hC.2.2.1,
    by simp only [T₂, T₁, Tapes.setHead_hd_ne _ _ (show tSC ≠ tSB by decide),
      Tapes.setHead_hd_ne _ _ (show tSC ≠ tSA by decide)]; exact hC.2.2.2⟩
  have s3 := Spec.backBlk (x := x) (t := tSC) (R := tU) (by decide) hU₂ (cellsOf_rec d) hcl
    (by rw [hC₂.2.2.2]; simp [Nat.succ_mul]; omega) hW₂ hB
  set T₃ := T₂.setHead tSC (T₂.hd tSC - L)
  have hW₃ : T₃.Within B := s3.target_within
  -- P
  have hP₃ : PhLay tSP T₃ _ := hP.congr rfl (by
    simp only [T₃, T₂, T₁, Tapes.setHead_hd_ne _ _ (show tSP ≠ tSC by decide),
      Tapes.setHead_hd_ne _ _ (show tSP ≠ tSB by decide),
      Tapes.setHead_hd_ne _ _ (show tSP ≠ tSA by decide)])
  obtain ⟨s4, hP₄⟩ := Spec.popPh (x := x) hP₃ hW₃
  set T₄ := T₃.setHead tSP (T₃.hd tSP - 1)
  refine ⟨T₄, ((s1.seq s2).seq s3).seq s4, ⟨?_, ?_, ?_, hP₄⟩, ?_, rfl,
    Tapes.within_setHead hW₃ (by have := hW₃ tSP; omega)⟩
  · have := hA.pop
    refine ⟨this.1, this.2.1, this.2.2.1, ?_⟩
    rw [← this.2.2.2]
    simp [T₄, T₃, T₂, T₁, Tapes.setHead_hd_ne _ _ (show tSA ≠ tSP by decide),
      Tapes.setHead_hd_ne _ _ (show tSA ≠ tSC by decide),
      Tapes.setHead_hd_ne _ _ (show tSA ≠ tSB by decide)]
  · have := hB₁.pop
    refine ⟨this.1, this.2.1, this.2.2.1, ?_⟩
    rw [← this.2.2.2]
    simp [T₄, T₃, T₂, Tapes.setHead_hd_ne _ _ (show tSB ≠ tSP by decide),
      Tapes.setHead_hd_ne _ _ (show tSB ≠ tSC by decide)]
  · have := hC₂.pop
    refine ⟨this.1, this.2.1, this.2.2.1, ?_⟩
    rw [← this.2.2.2]
    simp [T₄, T₃, Tapes.setHead_hd_ne _ _ (show tSC ≠ tSP by decide)]
  · intro i hi
    have hA' : i ≠ tSA := fun e => hi (Or.inl e)
    have hB'' : i ≠ tSB := fun e => hi (Or.inr (Or.inl e))
    have hC' : i ≠ tSC := fun e => hi (Or.inr (Or.inr (Or.inl e)))
    have hP' : i ≠ tSP := fun e => hi (Or.inr (Or.inr (Or.inr e)))
    exact ⟨rfl, by simp [T₄, T₃, T₂, T₁, Tapes.setHead_hd_ne _ _ hA', Tapes.setHead_hd_ne _ _ hB'',
      Tapes.setHead_hd_ne _ _ hC', Tapes.setHead_hd_ne _ _ hP']⟩

noncomputable def pushAll : Code NT (Sym Λ Γ) :=
  pushBlk tU tSA ++ pushBlk tV tSB ++ pushBlk tZ tSC ++ pushPh tSP false

theorem Spec.pushAll [NeZero (nV Λ Γ L)] (k : ℕ) {a b : Fin (nV Λ Γ L)} {T : Tapes NT (Sym Λ Γ)}
    {st : List (GF Λ Γ L)}
    (hU : Lay tU .mk .blank T (cellsOf (digs a))) (hV : Lay tV .mk .blank T (cellsOf (digs b)))
    (hZ : Lay tZ .mk .blank T (cellsOf (digs (Gen.zero : Fin (nV Λ Γ L)))))
    (hS : StacksRep L T st) (hT : T.Within B) (hB : (st.length + 1) * L + st.length + 3 ≤ B) :
    ∃ T', Spec (pushAll (Λ := Λ) (Γ := Γ)) x B T T' ∧
      StacksRep L T' (⟨k, a, b, Gen.zero, .left⟩ :: st) ∧
      T.Agree (fun i => i = tSA ∨ i = tSB ∨ i = tSC ∨ i = tSP) T' ∧ T'.ih = T.ih ∧
      T'.Within B := by
  obtain ⟨hA, hB', hC, hP⟩ := hS
  have hlA : ((st.map fun f => digs f.a).reverse).length = st.length := by simp
  have hlB : ((st.map fun f => digs f.b).reverse).length = st.length := by simp
  have hlC : ((st.map fun f => digs f.c).reverse).length = st.length := by simp
  obtain ⟨T₁, s1, hU₁, hA₁, ag1, ih1, hW₁⟩ := Spec.pushBlk (x := x) (R := tU) (t := tSA)
    (by decide) hU (digs_length a) hA hT (by rw [hlA]; omega)
  have hV₁ := hV.congr (ag1 tV (by decide)).1 (ag1 tV (by decide)).2
  have hB₁ : StackLay tSB L T₁ _ := ⟨by rw [(ag1 tSB (by decide)).1]; exact hB'.1, hB'.2.1,
    by rw [(ag1 tSB (by decide)).1]; exact hB'.2.2.1, by rw [(ag1 tSB (by decide)).2]; exact hB'.2.2.2⟩
  obtain ⟨T₂, s2, hV₂, hB₂, ag2, ih2, hW₂⟩ := Spec.pushBlk (x := x) (R := tV) (t := tSB)
    (by decide) hV₁ (digs_length b) hB₁ hW₁ (by rw [hlB]; omega)
  have ag12 : T.Agree (fun i => i = tSA ∨ i = tSB) T₂ :=
    (ag1.mono (fun i h => Or.inl h)).trans (ag2.mono (fun i h => Or.inr h))
  have hZ₂ := hZ.congr (ag12 tZ (by decide)).1 (ag12 tZ (by decide)).2
  have hC₂ : StackLay tSC L T₂ _ := ⟨by rw [(ag12 tSC (by decide)).1]; exact hC.1, hC.2.1,
    by rw [(ag12 tSC (by decide)).1]; exact hC.2.2.1, by rw [(ag12 tSC (by decide)).2]; exact hC.2.2.2⟩
  obtain ⟨T₃, s3, _, hC₃, ag3, ih3, hW₃⟩ := Spec.pushBlk (x := x) (R := tZ) (t := tSC)
    (by decide) hZ₂ (digs_length _) hC₂ hW₂ (by rw [hlC]; omega)
  have ag123 : T.Agree (fun i => i = tSA ∨ i = tSB ∨ i = tSC) T₃ :=
    (ag12.mono (fun i h => by rcases h with h | h <;> simp [h])).trans
      (ag3.mono (fun i h => by simp [h]))
  have hP₃ := hP.congr (ag123 tSP (by decide)).1 (ag123 tSP (by decide)).2
  obtain ⟨T₄, s4, hP₄, ag4, ih4, hW₄⟩ := Spec.pushPh (x := x) false hP₃ hW₃
    (by simp; omega)
  refine ⟨T₄, ((s1.seq s2).seq s3).seq s4, ⟨?_, ?_, ?_, ?_⟩, ?_, by rw [ih4, ih3, ih2, ih1],
    hW₄⟩
  · have g : T₄.tp tSA = T₁.tp tSA ∧ T₄.hd tSA = T₁.hd tSA :=
      ⟨((ag4 tSA (by decide)).1.trans (ag3 tSA (by decide)).1).trans (ag2 tSA (by decide)).1,
       ((ag4 tSA (by decide)).2.trans (ag3 tSA (by decide)).2).trans (ag2 tSA (by decide)).2⟩
    simp only [List.map_cons, List.reverse_cons]
    exact ⟨by rw [g.1]; exact hA₁.1, hA₁.2.1, by rw [g.1]; exact hA₁.2.2.1,
      by rw [g.2]; exact hA₁.2.2.2⟩
  · have g : T₄.tp tSB = T₂.tp tSB ∧ T₄.hd tSB = T₂.hd tSB :=
      ⟨(ag4 tSB (by decide)).1.trans (ag3 tSB (by decide)).1,
       (ag4 tSB (by decide)).2.trans (ag3 tSB (by decide)).2⟩
    simp only [List.map_cons, List.reverse_cons]
    exact ⟨by rw [g.1]; exact hB₂.1, hB₂.2.1, by rw [g.1]; exact hB₂.2.2.1,
      by rw [g.2]; exact hB₂.2.2.2⟩
  · have g := ag4 tSC (by decide)
    simp only [List.map_cons, List.reverse_cons]
    exact ⟨by rw [g.1]; exact hC₃.1, hC₃.2.1, by rw [g.1]; exact hC₃.2.2.1,
      by rw [g.2]; exact hC₃.2.2.2⟩
  · simp only [List.map_cons, List.reverse_cons]; exact hP₄
  · exact (ag123.mono (fun i h => by rcases h with h | h | h <;> simp [h])).trans
      (ag4.mono (fun i h => by simp [h]))

/-! ### Loading zero, incrementing -/

noncomputable def zeroV : Code NT (Sym Λ Γ) := zipPass tV tZ .mk isRec (fun _ b => b)

theorem Spec.zeroV {lv lz : List (Fin (nR Λ Γ))} {T : Tapes NT (Sym Λ Γ)}
    (hV : Lay tV .mk .blank T (cellsOf lv)) (hZ : Lay tZ .mk .blank T (cellsOf lz))
    (hlen : lz.length = lv.length) (hT : T.Within B) (hB : lv.length + 2 ≤ B) :
    ∃ T', Spec (zeroV (Λ := Λ) (Γ := Γ)) x B T T' ∧ Lay tV .mk .blank T' (cellsOf lz) ∧
      Lay tZ .mk .blank T' (cellsOf lz) ∧ T.Agree (fun i => i = tV) T' ∧ T'.ih = T.ih ∧
      T'.Within B := by
  have hmb : (Sym.mk : Sym Λ Γ) ≠ .blank := fun h => by cases h
  obtain ⟨T', s, hV', hZ', ag, ih, hW⟩ := Spec.zipPass (x := x) (a := tV) (b := tZ)
    (p := isRec) (F := fun _ b => b) (by decide) hmb hV (hZ.toW hmb)
    (by rw [cellsOf_length, cellsOf_length, hlen]) (cellsOf_rec lv) rfl (cellsOf_not_mk lz)
    (by rw [zipWith_snd _ _ (by rw [cellsOf_length, cellsOf_length, hlen])]; exact cellsOf_not_mk lz)
    hT (by rw [cellsOf_length]; exact hB)
  rw [zipWith_snd _ _ (by rw [cellsOf_length, cellsOf_length, hlen])] at hV'
  exact ⟨T', s, hV', hZ.congr (ag tZ (by decide)).1 (ag tZ (by decide)).2, ag, ih, hW⟩

noncomputable def incV [NeZero (nR Λ Γ)] : Code NT (Sym Λ Γ) := TM.incrD tV symR ++ TM.home tV .mk

theorem Spec.incV [NeZero (nR Λ Γ)] {l : List (Fin (nR Λ Γ))} {T : Tapes NT (Sym Λ Γ)}
    (hV : Lay tV .mk .blank T (cellsOf l)) (hT : T.Within B) (hB : l.length + 2 ≤ B) :
    ∃ T', Spec (incV (Λ := Λ) (Γ := Γ)) x B T T' ∧ Lay tV .mk .blank T' (cellsOf (dinc l)) ∧
      T.Agree (fun i => i = tV) T' ∧ T'.ih = T.ih ∧ T'.Within B := by
  have hmb : (Sym.mk : Sym Λ Γ) ≠ .blank := fun h => by cases h
  have hcl := cellsOf_length (Λ := Λ) (Γ := Γ) l
  obtain ⟨T₁, s1, p1, p2, p3, p4⟩ := Spec.incrD (x := x) (t := tV) symR_inj l T
    (by rw [hV.2.2.2]; have := hV.2.1; rwa [hcl] at this)
    (fun d => by
      rw [hV.2.2.2, Nat.add_comm]; have := hV.2.2.1; rw [hcl] at this; rw [this]
      exact fun h => by simp [symR] at h)
    hT (by rw [hV.2.2.2]; omega)
  rw [hV.2.2.2] at p1 p2 p4
  have hW₁ : T₁.Within B := fun i => by
    by_cases hi : i = tV
    · subst hi; omega
    · rw [(p3.2 i hi).2]; exact hT i
  have hdl := dinc_length l
  have hcl' := cellsOf_length (Λ := Λ) (Γ := Γ) (dinc l)
  have hh := Spec.home (x := x) tV .mk (T := T₁) (by rw [p2 0 (Or.inl (by omega))]; exact hV.1)
    (home_ok (l := cellsOf (dinc l)) hmb (cellsOf_not_mk _) (by rw [hcl', hdl]; exact p1)
      (by rw [hcl', hdl, p2 _ (Or.inr (by omega))]; have := hV.2.2.1; rwa [hcl] at this)
      (by rw [hcl', hdl]; omega))
    hW₁ (by omega)
  refine ⟨T₁.setHead tV 1, s1.seq hh, ⟨?_, ?_, ?_, by simp⟩, ?_, ?_,
    Tapes.within_setHead hW₁ (by omega)⟩
  · simp only [Tapes.setHead_tp]; rw [p2 0 (Or.inl (by omega))]; exact hV.1
  · simp only [Tapes.setHead_tp]; rw [hcl', hdl]; exact p1
  · simp only [Tapes.setHead_tp]; rw [hcl', hdl, p2 _ (Or.inr (by omega))]
    have := hV.2.2.1; rwa [hcl] at this
  · intro i hi
    exact ⟨(p3.2 i hi).1, by rw [Tapes.setHead_hd_ne _ _ hi]; exact (p3.2 i hi).2⟩
  · exact p3.1

end Savitch.Edge
