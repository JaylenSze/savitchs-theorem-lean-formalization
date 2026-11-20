import Savitch.Outer.Step

/-!
# Setting up the work tapes for a given width `L`

Phase 4b-6 of the Savitch formalization (see `PLAN.md`).

When the ruler tape `tRu` holds `L` copies of `rInit₀ M`, all block/counter/stack
tapes have `.mk` at cell 0 and their head at cell 1 (`AllHome`), `T.ih = 0`, and
`x.length + 1 < 2 ^ L`, `setupWidth M` initializes every register, counter and
scratch tape for width `L`, establishing `Rep L x K K T' (.done false)` and
`Regs K K (encV (M.initB hL)) Gen.zero T'` with `K = nR Λ Γ * L` (`Spec.setupWidth`).
-/

set_option linter.unusedSectionVars false

namespace Savitch.Edge

open TM Machine Machine.NTM

variable {Λ Γ : Type} [Fintype Λ] [Fintype Γ] [DecidableEq Λ] [DecidableEq Γ]
variable {x : List Bool} {B : ℕ} {L : ℕ}

/-! ### Nonemptiness and depth bounds from an `NTM` -/

theorem nR_pos (M : NTM Λ Γ) : 0 < nR Λ Γ :=
  @Fintype.card_pos (Rec Λ Γ) _ ⟨(M.blank, false, false, M.start)⟩

theorem nV_pos (M : NTM Λ Γ) (L : ℕ) : 0 < nV Λ Γ L :=
  Nat.pow_pos (nR_pos M)

theorem nV_le_two_pow (L : ℕ) : nV Λ Γ L ≤ 2 ^ (nR Λ Γ * L) := by
  rw [Nat.pow_mul]
  exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le L

/-! ### Zero and initial vertex blocks -/

theorem dval_replicate_zero [NeZero (nR Λ Γ)] : ∀ L, dval (List.replicate L (0 : Fin (nR Λ Γ))) = 0
  | 0 => rfl
  | L + 1 => by simp [List.replicate_succ, dval, dval_replicate_zero L]

theorem digs_zero [NeZero (nR Λ Γ)] [NeZero (nV Λ Γ L)] :
    digs (Gen.zero : Fin (nV Λ Γ L)) = List.replicate L 0 := by
  apply dval_inj (by rw [digs_length, List.length_replicate])
  rw [dval_digs, dval_replicate_zero]; rfl

theorem cellsOf_digs_zero [NeZero (nR Λ Γ)] [NeZero (nV Λ Γ L)] :
    cellsOf (digs (Gen.zero : Fin (nV Λ Γ L))) = List.replicate L (symR 0) := by
  rw [digs_zero, cellsOf, List.map_replicate]

def rInit₀ (M : NTM Λ Γ) : Sym Λ Γ := .rc (M.blank, false, false, M.start)
def rInit₁ (M : NTM Λ Γ) : Sym Λ Γ := .rc (M.blank, true, false, M.start)

theorem toBits_zero : ∀ L, toBits 0 L = List.replicate L false
  | 0 => rfl
  | L + 1 => by simp [toBits, toBits_zero L, List.replicate_succ]

theorem getD_replicate_false : ∀ (L j : ℕ), (List.replicate L false).getD j false = false
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | L + 1, j + 1 => getD_replicate_false L j

theorem write_initB (M : NTM Λ Γ) {n L : ℕ} (hL : 0 < L) {T : Tapes NT (Sym Λ Γ)}
    (hI : Lay tI .mk .blank T (List.replicate L (rInit₀ M))) :
    Lay tI .mk .blank (T.write tI (rInit₁ M))
      (cellsOf (digs (encV (n := n) (M.initB hL)))) := by
  rw [cellsOf_digs]
  have hrec : recs (encV (n := n) (M.initB hL)) = encR (M.initB hL) := recs_unrecs _
  rw [hrec]
  obtain ⟨h0, hseg, hend, hhd⟩ := hI
  rw [List.length_replicate] at hseg hend
  refine ⟨?_, ?_, ?_, hhd⟩
  · rw [Tapes.write_tp_self, hhd, ite_neg' (by decide), h0]
  · rw [List.length_map, List.length_ofFn, seg_ofFn, List.map_ofFn]
    rw [seg_ofFn, ← List.ofFn_const] at hseg
    have hcell := congrFun (List.ofFn_injective hseg)
    congr 1; funext j
    rw [Tapes.write_tp_self, hhd]
    simp only [Function.comp_apply, encR, NTM.initB, toBits_zero,
      getD_replicate_false]
    by_cases hj : j.val = 0
    · have hj' : j = ⟨0, hL⟩ := Fin.ext hj
      rw [ite_pos' (by omega), hj']; rfl
    · have hj' : j ≠ ⟨0, hL⟩ := fun e => hj (by rw [e])
      rw [ite_neg' (by omega), hcell j]
      simp [rInit₀, hj']
  · rw [List.length_map, List.length_ofFn, Tapes.write_tp_self, hhd,
      ite_neg' (by omega), hend]

/-! ### Tapes with a home cell -/

def HomeT (i : Fin NT) : Prop :=
  i = tU ∨ i = tV ∨ i = tS ∨ i = tA₁ ∨ i = tA₂ ∨ i = tP ∨ i = tP₂ ∨ i = tCU ∨
  i = tZ ∨ i = tSA ∨ i = tSB ∨ i = tSC ∨ i = tSP ∨ i = tKc ∨ i = tW ∨ i = tI ∨ i = tKK

instance : DecidablePred HomeT := fun i => by unfold HomeT; infer_instance

def AllHome (T : Tapes NT (Sym Λ Γ)) : Prop :=
  ∀ i, HomeT i → T.tp i 0 = .mk ∧ T.hd i = 1

theorem allHome_of_rep_regs [NeZero (nV Λ Γ L)] {K WK : ℕ} {a v : Fin (nV Λ Γ L)} {r : Bool}
    {T : Tapes NT (Sym Λ Γ)} (hR : Rep L x K WK T (.done r)) (hG : Regs K WK a v T) :
    AllHome T := by
  obtain ⟨_, ⟨_, hU⟩, ⟨_, hV⟩, ⟨_, _, hKc, _, _⟩, ⟨hSA, hSB, hSC, hSP⟩, hZ,
    ⟨_, hA₁, _⟩, ⟨_, hP, _⟩, ⟨_, hCU, _⟩, ⟨_, hS, _, _⟩, ⟨_, hA₂, _, _, _⟩, ⟨_, hP₂, _⟩⟩ := hR
  obtain ⟨hI, hW, _, hKK, _, _⟩ := hG
  intro i hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact ⟨hU.1, hU.2.2.2⟩
  · exact ⟨hV.1, hV.2.2.2⟩
  · exact ⟨hS.1, hS.2.2.2⟩
  · exact ⟨hA₁.1, hA₁.2.2.2⟩
  · exact ⟨hA₂.1, hA₂.2.2.2⟩
  · exact ⟨hP.1.1, hP.1.2.2.2.2.2⟩
  · exact ⟨hP₂.1, hP₂.2.2.2.2.2⟩
  · exact ⟨hCU.1, hCU.2.2.2.2.2⟩
  · exact ⟨hZ.1, hZ.2.2.2⟩
  · exact ⟨hSA.1, by simpa using hSA.2.2.2⟩
  · exact ⟨hSB.1, by simpa using hSB.2.2.2⟩
  · exact ⟨hSC.1, by simpa using hSC.2.2.2⟩
  · exact ⟨hSP.1, by simpa using hSP.2.2⟩
  · exact ⟨hKc.1, hKc.2.2.2.2.2⟩
  · exact ⟨hW.1, hW.2.2.2⟩
  · exact ⟨hI.1, hI.2.2.2⟩
  · exact ⟨hKK.1, hKK.2.2.2.2.2⟩

/-! ### Per-width setup -/

noncomputable def initList [NeZero (nR Λ Γ)] (M : NTM Λ Γ) : List (Fin NT × Sym Λ Γ) :=
  [(tU, symR 0), (tV, symR 0), (tZ, symR 0), (tW, symR 0), (tI, rInit₀ M),
   (tS, symR 0), (tA₁, .z), (tA₂, .z), (tP, .z), (tP₂, .z), (tCU, .z)]

noncomputable def setupWidth [NeZero (nR Λ Γ)] (M : NTM Λ Γ) : Code NT (Sym Λ Γ) :=
  makeBlocks (initList M) ++ [Instr.write tI (rInit₁ M)] ++
    [Instr.write tMd (.md (.done false))] ++
    makeBlockN tKc .z (nR Λ Γ) ++ makeBlockN tKK .z (nR Λ Γ) ++ loadK (nR Λ Γ)

def InInit (i : Fin NT) : Prop :=
  i = tU ∨ i = tV ∨ i = tZ ∨ i = tW ∨ i = tI ∨ i = tS ∨ i = tA₁ ∨ i = tA₂ ∨
  i = tP ∨ i = tP₂ ∨ i = tCU

instance : DecidablePred InInit := fun i => by unfold InInit; infer_instance

theorem mem_initList_fst [NeZero (nR Λ Γ)] (M : NTM Λ Γ) (i : Fin NT) :
    (∃ p ∈ initList M, p.1 = i) ↔ InInit i := by
  simp [initList, InInit, eq_comm]

theorem Spec.setupWidth [NeZero (nV Λ Γ L)] [NeZero (nR Λ Γ)] (M : NTM Λ Γ) (hL : 0 < L)
    (hfit : x.length + 1 < 2 ^ L) {T : Tapes NT (Sym Λ Γ)}
    (hRu : Lay tRu .mk .blank T (List.replicate L (rInit₀ M)))
    (hH : AllHome T) (hih : T.ih = 0) (hT : T.Within B)
    (hB : nR Λ Γ * L + L + 3 ≤ B) :
    ∃ T', Spec (Edge.setupWidth M) x B T T' ∧
      Rep L x (nR Λ Γ * L) (nR Λ Γ * L) T' (.done false) ∧
      Regs (nR Λ Γ * L) (nR Λ Γ * L) (encV (n := x.length) (M.initB hL)) Gen.zero T' ∧
      Lay tRu .mk .blank T' (List.replicate L (rInit₀ M)) ∧
      T'.ih = 0 ∧ T'.Within B := by
  have hmb : (Sym.mk : Sym Λ Γ) ≠ .blank := fun h => by cases h
  set lr := List.replicate L (rInit₀ M)
  have hlr : lr.length = L := List.length_replicate
  have hrec : ∀ g ∈ lr, isRec g = true := fun g hg => by
    rw [List.eq_of_mem_replicate hg]; rfl
  have hLB : lr.length + 2 ≤ B := by omega
  -- 1. make the L-cell blocks
  have hnd : ((initList M).map Prod.fst).Nodup := by
    simp only [initList, List.map]; decide
  have hok : ∀ p ∈ initList M, tRu ≠ p.1 ∧ p.2 ≠ .mk := by
    intro p hp
    simp only [initList, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      dsimp only <;> refine ⟨by decide, ?_⟩ <;> intro h <;> simp [symR, rInit₀] at h
  have hpre : ∀ p ∈ initList M, T.tp p.1 0 = .mk ∧ T.hd p.1 = 1 := by
    intro p hp
    apply hH p.1
    have h1 : InInit p.1 := (mem_initList_fst M p.1).1 ⟨p, hp, rfl⟩
    have h2 : ∀ i, InInit i → HomeT i := by decide
    exact h2 p.1 h1
  obtain ⟨T₁, s1, hL₁, hRu₁, ag1, ih1, hW₁⟩ :=
    Spec.makeBlocks (x := x) hrec (initList M) hnd hok hRu hpre hT hLB
  have ag1' : T.Agree InInit T₁ := fun i hi =>
    ag1 i (fun h => hi ((mem_initList_fst M i).1 h))
  -- 2. write cell 1 of `tI` and mode `.done false` on `tMd`
  have s2 := Spec.write (x := x) (t := tI) (g := rInit₁ M) hW₁
  set T₂ := T₁.write tI (rInit₁ M)
  have hW₂ : T₂.Within B := Tapes.within_write hW₁
  have s3 := Spec.write (x := x) (t := tMd) (g := (Sym.md (.done false) : Sym Λ Γ)) hW₂
  set T₃ := T₂.write tMd (.md (.done false))
  have hW₃ : T₃.Within B := Tapes.within_write hW₂
  have ag13 : T₁.Agree (fun i => i = tI ∨ i = tMd) T₃ := fun i hi => by
    have h1 : i ≠ tI := fun e => hi (Or.inl e)
    have h2 : i ≠ tMd := fun e => hi (Or.inr e)
    exact ⟨by simp [T₃, T₂, Tapes.write, h1, h2], rfl⟩
  have ag03 : T.Agree (fun i => InInit i ∨ i = tMd) T₃ :=
    (ag1'.mono (fun _ h => Or.inl h)).trans
      (ag13.mono (fun i h => h.elim (fun e => Or.inl (by subst e; decide)) Or.inr))
  -- 3. `tKc` and `tKK`
  have hRu₃ := agree_lay ag13 (by decide) hRu₁
  have gKc := ag03 tKc (by decide)
  have hKc0 : T₃.tp tKc 0 = .mk := by rw [gKc.1]; exact (hH tKc (by decide)).1
  have hKc1 : T₃.hd tKc = 1 := by rw [gKc.2]; exact (hH tKc (by decide)).2
  obtain ⟨T₄, s4, hLKc, hRu₄, ag4, ih4, hW₄⟩ :=
    Spec.makeBlockN (x := x) (t := tKc) (g := .z) (by decide) (fun h => by cases h) (nR Λ Γ)
      hRu₃ hrec hKc0 hKc1 hW₃ (by rw [hlr]; exact hB)
  have gKK := ag03 tKK (by decide)
  have gKK₄ := ag4 tKK (by decide)
  have hKK0 : T₄.tp tKK 0 = .mk := by rw [gKK₄.1, gKK.1]; exact (hH tKK (by decide)).1
  have hKK1 : T₄.hd tKK = 1 := by rw [gKK₄.2, gKK.2]; exact (hH tKK (by decide)).2
  obtain ⟨T₅, s5, hLKK, hRu₅, ag5, ih5, hW₅⟩ :=
    Spec.makeBlockN (x := x) (t := tKK) (g := .z) (by decide) (fun h => by cases h) (nR Λ Γ)
      hRu₄ hrec hKK0 hKK1 hW₄ (by rw [hlr]; exact hB)
  rw [hlr] at hLKc hLKK
  have hHKK₅ : Holds tKK .mk .z .o T₅ (List.replicate (nR Λ Γ * L) false) :=
    Lay.toHolds_replicate false hLKK
  obtain ⟨T₆, lK, s6, hKK₆, hlK, hvK, hRu₆, ag6, ih6, hW₆⟩ :=
    Spec.loadK (x := x) hrec (nR Λ Γ) hRu₅ hHKK₅
      (by rw [bval_replicate_false, Nat.zero_add, hlr, List.length_replicate]
          exact Nat.lt_two_pow_self)
      hW₅ hLB (by rw [List.length_replicate]; omega)
  rw [List.length_replicate] at hlK
  rw [bval_replicate_false, Nat.zero_add, hlr] at hvK
  have ag36 : T₃.Agree (fun i => i = tKc ∨ i = tKK) T₆ :=
    ((ag4.mono (fun _ h => Or.inl h)).trans (ag5.mono (fun _ h => Or.inr h))).trans
      (ag6.mono (fun _ h => Or.inr h))
  have ag16 : T₁.Agree (fun i => i = tI ∨ i = tMd ∨ i = tKc ∨ i = tKK) T₆ :=
    (ag13.mono (fun i h => h.elim Or.inl (fun h => Or.inr (Or.inl h)))).trans
      (ag36.mono (fun i h => Or.inr (Or.inr h)))
  have ag06 : T.Agree (fun i => InInit i ∨ i = tMd ∨ i = tKc ∨ i = tKK) T₆ :=
    (ag03.mono (fun i h => h.elim Or.inl (fun h => Or.inr (Or.inl h)))).trans
      (ag36.mono (fun i h => Or.inr (Or.inr h)))
  have hih₆ : T₆.ih = 0 := by
    rw [ih6, ih5, ih4]; show T₁.ih = 0; rw [ih1, hih]
  have get1 : ∀ t g, (t, g) ∈ initList M → Lay t .mk .blank T₁ (List.replicate L g) := by
    intro t g hmem
    have := hL₁ (t, g) hmem
    rwa [hlr] at this
  have hU₆ : Lay tU .mk .blank T₆ (cellsOf (digs (Gen.zero : Fin (nV Λ Γ L)))) := by
    rw [cellsOf_digs_zero]
    exact agree_lay ag16 (by decide) (get1 tU (symR 0) (by simp [initList]))
  have hV₆ : Lay tV .mk .blank T₆ (cellsOf (digs (Gen.zero : Fin (nV Λ Γ L)))) := by
    rw [cellsOf_digs_zero]
    exact agree_lay ag16 (by decide) (get1 tV (symR 0) (by simp [initList]))
  have hZ₆ : Lay tZ .mk .blank T₆ (cellsOf (digs (Gen.zero : Fin (nV Λ Γ L)))) := by
    rw [cellsOf_digs_zero]
    exact agree_lay ag16 (by decide) (get1 tZ (symR 0) (by simp [initList]))
  have hW₆' : Lay tW .mk .blank T₆ (cellsOf (digs (Gen.zero : Fin (nV Λ Γ L)))) := by
    rw [cellsOf_digs_zero]
    exact agree_lay ag16 (by decide) (get1 tW (symR 0) (by simp [initList]))
  have hS₆ : Lay tS .mk .blank T₆ (List.replicate L (symR 0)) :=
    agree_lay ag16 (by decide) (get1 tS (symR 0) (by simp [initList]))
  have hA₁₆ : Lay tA₁ .mk .blank T₆ (List.replicate L .z) :=
    agree_lay ag16 (by decide) (get1 tA₁ .z (by simp [initList]))
  have hA₂₆ : Lay tA₂ .mk .blank T₆ (List.replicate L .z) :=
    agree_lay ag16 (by decide) (get1 tA₂ .z (by simp [initList]))
  have hP₆ : Holds tP .mk .z .o T₆ (List.replicate L false) :=
    Lay.toHolds_replicate false (agree_lay ag16 (by decide) (get1 tP .z (by simp [initList])))
  have hP₂₆ : Holds tP₂ .mk .z .o T₆ (List.replicate L false) :=
    Lay.toHolds_replicate false (agree_lay ag16 (by decide) (get1 tP₂ .z (by simp [initList])))
  have hCU₆ : Holds tCU .mk .z .o T₆ (List.replicate L false) :=
    Lay.toHolds_replicate false (agree_lay ag16 (by decide) (get1 tCU .z (by simp [initList])))
  have hI₂ : Lay tI .mk .blank T₂ (cellsOf (digs (encV (n := x.length) (M.initB hL)))) :=
    write_initB M hL (get1 tI (rInit₀ M) (by simp [initList]))
  have hI₃ : Lay tI .mk .blank T₃ (cellsOf (digs (encV (n := x.length) (M.initB hL)))) :=
    hI₂.congr (by simp [T₃, Tapes.write, show tI ≠ tMd by decide]) rfl
  have hI₆ : Lay tI .mk .blank T₆ (cellsOf (digs (encV (n := x.length) (M.initB hL)))) :=
    agree_lay ag36 (by decide) hI₃
  have hKc₆ : Holds tKc .mk .z .o T₆ (List.replicate (nR Λ Γ * L) false) := by
    have hKc₄ := Lay.toHolds_replicate false hLKc
    have ag46 : T₄.Agree (fun i => i = tKK) T₆ := ag5.trans ag6
    exact hKc₄.congr (ag46 tKc (by decide)).1 (ag46 tKc (by decide)).2
  have hSt : StacksRep L T₆ [] := by
    have mkStack : ∀ t, ¬ (InInit t ∨ t = tMd ∨ t = tKc ∨ t = tKK) →
        HomeT t → StackLay t L T₆ [] := fun t hnot hhome => by
      have g := ag06 t hnot
      exact ⟨by rw [g.1]; exact (hH t hhome).1, fun _ h => absurd h List.not_mem_nil,
        by simp [seg], by simp [g.2, (hH t hhome).2]⟩
    refine ⟨mkStack tSA (by decide) (by decide), mkStack tSB (by decide) (by decide),
      mkStack tSC (by decide) (by decide), ?_⟩
    have g := ag06 tSP (by decide)
    exact ⟨by rw [g.1]; exact (hH tSP (by decide)).1, by simp [seg],
      by simp [g.2, (hH tSP (by decide)).2]⟩
  have hA₂W : LayW tA₂ .mk T₆ ((List.replicate L false).map bit) := by
    rw [map_bit_replicate L false]; exact hA₂₆.toW hmb
  have hSc₆ : Scratch L T₆ := by
    refine And.intro ⟨_, And.intro hS₆ ⟨List.length_replicate, fun g hg => by
        rw [List.eq_of_mem_replicate hg]; exact fun h => by simp [symR] at h⟩⟩ (And.intro ?_ ?_)
    · refine ⟨List.replicate L false, And.intro hA₂W ⟨List.length_replicate, ?_, ?_⟩⟩
      · have := hA₂₆.2.2.1; rw [List.length_replicate] at this; rw [this]; exact fun h => by cases h
      · have := hA₂₆.2.2.1; rw [List.length_replicate] at this; rw [this]; exact fun h => by cases h
    · exact ⟨_, And.intro hP₂₆ List.length_replicate⟩
  have hPIn : InPos tP .mk .z .o x T₆ (List.replicate L false) :=
    ⟨hP₆, by rw [bval_replicate_false, hih₆], by rw [hih₆]; omega,
      by rw [List.length_replicate]; exact hfit⟩
  have hEInv : EInv (x := x) L T₆ :=
    And.intro ⟨_, And.intro hA₁₆ List.length_replicate⟩
      (And.intro ⟨List.replicate L false, And.intro hPIn List.length_replicate⟩
        (And.intro ⟨_, And.intro hCU₆ List.length_replicate⟩ hSc₆))
  have hMd₆ : T₆.read tMd = .md (.done false) := by
    rw [Tapes.read, (ag36 tMd (by decide)).1, (ag36 tMd (by decide)).2]
    simp [T₃, Tapes.write_tp_self]
  have hCtr₆ : Ctr (nR Λ Γ * L) 0 T₆ :=
    ⟨List.replicate (nR Λ Γ * L) false,
      And.intro hKc₆ ⟨List.length_replicate, bval_replicate_false _⟩⟩
  have hRep₆ : Rep L x (nR Λ Γ * L) (nR Λ Γ * L) T₆ (.done false) :=
    And.intro hMd₆ (And.intro ⟨Gen.zero, hU₆⟩ (And.intro ⟨Gen.zero, hV₆⟩
      (And.intro ⟨0, hCtr₆⟩ (And.intro hSt (And.intro hZ₆ hEInv)))))
  have hRegs₆ : Regs (nR Λ Γ * L) (nR Λ Γ * L) (encV (n := x.length) (M.initB hL)) Gen.zero T₆ :=
    And.intro hI₆ (And.intro hW₆' ⟨lK, And.intro hKK₆ ⟨hlK, hvK⟩⟩)
  exact ⟨T₆, ((((s1.seq s2).seq s3).seq s4).seq s5).seq s6, hRep₆, hRegs₆, hRu₆, hih₆, hW₆⟩

end Savitch.Edge
