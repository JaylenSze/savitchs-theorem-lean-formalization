import Savitch.Outer.Reach

/-!
# Processing one vertex

Phase 4b-6 of the Savitch formalization (see `PLAN.md`).

For the vertex `v` held in `tW`, `perVertex M` runs `reachSub` from the start block
(in `tI`) to `v`. If `v` is reachable it loads `v` into `tU`, runs the escape test
and the accept test, and records a positive answer on `tEsc` / `tAcc`.
-/

set_option linter.unusedSectionVars false

namespace Savitch.Edge

open TM Machine Machine.NTM

variable {Λ Γ : Type} [Fintype Λ] [Fintype Γ] [DecidableEq Λ] [DecidableEq Γ]
variable {x : List Bool} {B : ℕ} {L : ℕ}

/-- Record `yes` on `tAcc` if the block under `tU` decodes to the accepting state. -/
noncomputable def accTest (M : NTM Λ Γ) : Code NT (Sym Λ Γ) :=
  TM.cases tU (fun g => match g with
    | .rc r => if r.2.2.2 = M.accept then [Instr.write tAcc .yes] else []
    | _ => []) Finset.univ.toList

open Classical in
theorem Spec.accTest (M : NTM Λ Γ) (hL : 0 < L) (u : Fin (nV Λ Γ L)) {T : Tapes NT (Sym Λ Γ)}
    (hU : Lay tU .mk .blank T ((List.ofFn (recs u)).map .rc)) (hT : T.Within B) :
    ∃ T', Spec (accTest M) x B T T' ∧
      T'.tp tAcc (T.hd tAcc) = (if (decV (n := x.length) hL u).1 = M.accept then .yes
        else T.tp tAcc (T.hd tAcc)) ∧
      T.Agree (fun i => i = tAcc) T' ∧ T'.hd = T.hd ∧ T'.ih = T.ih ∧ T'.Within B := by
  have hread : T.read tU = .rc (recs u ⟨0, hL⟩) := by
    have h := hU.2.1
    rw [List.length_map, List.length_ofFn, seg_ofFn, List.map_ofFn] at h
    have := congrFun (List.ofFn_injective h) ⟨0, hL⟩
    rw [Tapes.read, hU.2.2.2]; simpa using this
  by_cases ha : (recs u ⟨0, hL⟩).2.2.2 = M.accept
  · refine ⟨T.write tAcc .yes, Spec.cases tU _ _ (by simp) hT (by
        rw [hread]; simp only [ha, ↓reduceIte]; exact Spec.write hT), ?_,
      fun i hi => ⟨by simp [Tapes.write, hi], rfl⟩, rfl, rfl, Tapes.within_write hT⟩
    rw [ite_pos' (show (decV (n := x.length) hL u).1 = M.accept from ha), Tapes.write_tp_self,
      ite_pos' rfl]
  · refine ⟨T, Spec.cases tU _ _ (by simp) hT (by
        rw [hread]; simp only [ha, ↓reduceIte]; exact Spec.nil hT), ?_,
      Tapes.Agree.refl _ T, rfl, rfl, hT⟩
    rw [ite_neg' (show ¬ (decV (n := x.length) hL u).1 = M.accept from ha)]

/-! ### One vertex -/

/-- Tapes a vertex step may change. -/
def Lo₂ (i : Fin NT) : Prop := i.val < 22 ∨ i = tEsc ∨ i = tAcc

instance : DecidablePred Lo₂ := fun i => inferInstanceAs (Decidable (i.val < 22 ∨ i = tEsc ∨ i = tAcc))

noncomputable def perVertex [NeZero (nR Λ Γ)] (M : NTM Λ Γ) : Code NT (Sym Λ Γ) :=
  reachSub M ++
    ifElse (.tape tMd (fun g => decide (g = .md (.done true))))
      (zipPass tU tW .mk isRec (fun _ b => b) ++ escTest M ++
        ifElse (.tape tR (fun g => decide (g = .yes))) [Instr.write tEsc .yes] [] ++ accTest M)
      []

open Classical in
theorem Spec.perVertex [NeZero (nV Λ Γ L)] [NeZero (nR Λ Γ)] (M : NTM Λ Γ) (hL : 0 < L)
    (hfit : x.length + 1 < 2 ^ L) {K WK : ℕ} (hWK : K < 2 ^ WK) (hN : nV Λ Γ L ≤ 2 ^ K)
    {a v : Fin (nV Λ Γ L)} {r₀ : Bool} {T : Tapes NT (Sym Λ Γ)}
    (hR : Rep L x K WK T (.done r₀)) (hG : Regs K WK a v T) (hT : T.Within B)
    (hB : (K + 1) * (L + 1) + WK + 8 ≤ B) :
    ∃ T' r, Spec (perVertex M) x B T T' ∧ Rep L x K WK T' (.done r) ∧ Regs K WK a v T' ∧
      T'.tp tEsc (T.hd tEsc) = (if Relation.ReflTransGen (M.GEdge x hL) a v ∧
          M.Escapes x (decV (n := x.length) hL v) then .yes else T.tp tEsc (T.hd tEsc)) ∧
      T'.tp tAcc (T.hd tAcc) = (if Relation.ReflTransGen (M.GEdge x hL) a v ∧
          (decV (n := x.length) hL v).1 = M.accept then .yes else T.tp tAcc (T.hd tAcc)) ∧
      T'.hd tEsc = T.hd tEsc ∧ T'.hd tAcc = T.hd tAcc ∧ T.Agree Lo₂ T' ∧ T'.Within B := by
  have hmb : (Sym.mk : Sym Λ Γ) ≠ .blank := fun h => by cases h
  have hLB : L + 2 ≤ B := by
    have := Nat.le_mul_of_pos_left (L + 1) (show 0 < K + 1 by omega); omega
  obtain ⟨T₁, s1, hR₁, hG₁, ag1, hW₁⟩ := Spec.reachSub (B := B) M hL hfit hWK hN hR hG hT hB
  have hE₁ := ag1 tEsc (by decide)
  have hA₁ := ag1 tAcc (by decide)
  by_cases hr : Relation.ReflTransGen (M.GEdge x hL) a v
  · have hMd : T₁.read tMd = .md (.done true) := by rw [hR₁.1]; simp [hr]
    obtain ⟨_, ⟨a₁, hU₁⟩, hV₁, hK₁, hS₁, hC₁⟩ := hR₁
    obtain ⟨hI₁, hW₁', hKK₁⟩ := hG₁
    -- load `v` into `tU`
    obtain ⟨T₂, s2, hU₂, _, ag2, ih2, hW₂⟩ := Spec.zipPass (x := x) (a := tU) (b := tW)
      (p := isRec) (F := fun _ b => b) (by decide) hmb hU₁ (hW₁'.toW hmb)
      (by rw [cellsOf_length, cellsOf_length, digs_length, digs_length]) (cellsOf_rec _) rfl
      (cellsOf_not_mk _)
      (by rw [zipWith_snd _ _ (by rw [cellsOf_length, cellsOf_length, digs_length, digs_length])]
          exact cellsOf_not_mk _)
      hW₁ (by rw [cellsOf_length, digs_length]; exact hLB)
    rw [zipWith_snd _ _ (by rw [cellsOf_length, cellsOf_length, digs_length, digs_length])] at hU₂
    have hEI₂ : EInv (x := x) L T₂ := hC₁.2.agree ag2 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) ih2
    -- escape test
    obtain ⟨T₃, s3, hR₃, hU₃, hEI₃, ag3, hRhd₃, hW₃⟩ := Spec.escTest (x := x) M hL hfit v
      (by rw [← cellsOf_digs]; exact hU₂) hEI₂ hW₂ hLB
    have hR₃' : T₃.read tR = if M.Escapes x (decV (n := x.length) hL v) then .yes else .no := by
      rw [Tapes.read, hRhd₃]; exact hR₃
    -- record an escape
    have hEsc₃ : T₃.tp tEsc = T.tp tEsc ∧ T₃.hd tEsc = T.hd tEsc :=
      ⟨((ag3 tEsc (by decide)).1.trans (ag2 tEsc (by decide)).1).trans hE₁.1,
       ((ag3 tEsc (by decide)).2.trans (ag2 tEsc (by decide)).2).trans hE₁.2⟩
    obtain ⟨T₄, s4, hEsc₄, ag4, ih4, hd4, hW₄⟩ : ∃ T₄, Spec (ifElse (.tape tR
        (fun g => decide (g = (Sym.yes : Sym Λ Γ)))) [Instr.write tEsc (Sym.yes : Sym Λ Γ)] [])
        x B T₃ T₄ ∧
        T₄.tp tEsc (T.hd tEsc) = (if M.Escapes x (decV (n := x.length) hL v) then .yes
          else T.tp tEsc (T.hd tEsc)) ∧ T₃.Agree (fun i => i = tEsc) T₄ ∧ T₄.ih = T₃.ih ∧
        T₄.hd = T₃.hd ∧ T₄.Within B := by
      by_cases he : M.Escapes x (decV (n := x.length) hL v)
      · refine ⟨T₃.write tEsc .yes, Spec.ifElse_true (by simp [Cond.eval, hR₃', he]) hW₃
          (Spec.write hW₃), ?_, fun i hi => ⟨by simp [Tapes.write, hi], rfl⟩, rfl, rfl,
          Tapes.within_write hW₃⟩
        rw [ite_pos' he, Tapes.write_tp_self, ite_pos' hEsc₃.2.symm]
      · refine ⟨T₃, Spec.ifElse_false (by simp [Cond.eval, hR₃', he]) hW₃ (Spec.nil hW₃), ?_,
          Tapes.Agree.refl _ T₃, rfl, rfl, hW₃⟩
        rw [ite_neg' he, hEsc₃.1]
    -- accept test
    have hU₄ := agree_lay ag4 (by decide) hU₃
    obtain ⟨T₅, s5, hAcc₅, ag5, hd5, ih5, hW₅⟩ := Spec.accTest (x := x) M hL v hU₄ hW₄
    have hAcc₄ : T₄.tp tAcc = T.tp tAcc ∧ T₄.hd tAcc = T.hd tAcc :=
      ⟨(((ag4 tAcc (by decide)).1.trans (ag3 tAcc (by decide)).1).trans
          (ag2 tAcc (by decide)).1).trans hA₁.1,
       (((ag4 tAcc (by decide)).2.trans (ag3 tAcc (by decide)).2).trans
          (ag2 tAcc (by decide)).2).trans hA₁.2⟩
    have ag15 : T₁.Agree (fun i => i = tU ∨ i = tS ∨ i = tA₁ ∨ i = tA₂ ∨ i = tP ∨ i = tP₂ ∨
        i = tCU ∨ i = tK ∨ i = tF ∨ i = tF₂ ∨ i = tG ∨ i = tR ∨ i = tEsc ∨ i = tAcc) T₅ :=
      (((ag2.mono (fun i h => by revert i h; decide)).trans
        (ag3.mono (fun i h => by revert i h; decide))).trans
        (ag4.mono (fun i h => by revert i h; decide))).trans
        (ag5.mono (fun i h => by revert i h; decide))
    have ag35 : T₃.Agree (fun i => i = tEsc ∨ i = tAcc) T₅ :=
      (ag4.mono (fun _ h => Or.inl h)).trans (ag5.mono (fun _ h => Or.inr h))
    have hih35 : T₅.ih = T₃.ih := by rw [ih5, ih4]
    refine ⟨T₅, true, s1.seq (Spec.ifElse_true (by simp [Cond.eval, hMd]) hW₁
      (((s2.seq s3).seq s4).seq s5)), ⟨?_, ⟨v, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_,
      by rw [hd5, hd4]; exact hEsc₃.2, by rw [hd5]; exact hAcc₄.2, ?_, hW₅⟩
    · rw [Tapes.read, (ag15 tMd (by decide)).1, (ag15 tMd (by decide)).2]; exact hMd
    · rw [cellsOf_digs]; exact agree_lay ag35 (by decide) hU₃
    · obtain ⟨b₁, hb⟩ := hV₁; exact ⟨b₁, agree_lay ag15 (by decide) hb⟩
    · obtain ⟨w₁, hw⟩ := hK₁; exact ⟨w₁, hw.agree ag15 (by decide)⟩
    · exact hS₁.agree ag15 (by decide) (by decide) (by decide) (by decide)
    · exact ⟨agree_lay ag15 (by decide) hC₁.1,
        hEI₃.agree ag35 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          hih35⟩
    · exact ⟨agree_lay ag15 (by decide) hI₁, agree_lay ag15 (by decide) hW₁',
        by obtain ⟨l, h1, h2, h3⟩ := hKK₁
           exact ⟨l, h1.congr (ag15 tKK (by decide)).1 (ag15 tKK (by decide)).2, h2, h3⟩⟩
    · rw [(ag5 tEsc (by decide)).1, hEsc₄]
      by_cases he : M.Escapes x (decV (n := x.length) hL v)
      · rw [ite_pos' he, ite_pos' ⟨hr, he⟩]
      · rw [ite_neg' he, ite_neg' (fun h => he h.2)]
    · rw [← hAcc₄.2, hAcc₅, hAcc₄.1, hAcc₄.2]
      by_cases ha : (decV (n := x.length) hL v).1 = M.accept
      · rw [ite_pos' ha, ite_pos' ⟨hr, ha⟩]
      · rw [ite_neg' ha, ite_neg' (fun h => ha h.2)]
    · exact (ag1.mono (fun i h => Or.inl h)).trans (ag15.mono (fun i h => by revert i h; decide))
  · -- not reachable: nothing to record
    have hMd : T₁.read tMd = .md (.done false) := by rw [hR₁.1]; simp [hr]
    refine ⟨T₁, _, s1.seq (Spec.ifElse_false (by simp [Cond.eval, hMd]) hW₁ (Spec.nil hW₁)), hR₁,
      hG₁, ?_, ?_, hE₁.2, hA₁.2, ag1.mono (fun i h => Or.inl h), hW₁⟩
    · rw [hE₁.1, ite_neg' (fun h => hr h.1)]
    · rw [hA₁.1, ite_neg' (fun h => hr h.1)]

end Savitch.Edge
