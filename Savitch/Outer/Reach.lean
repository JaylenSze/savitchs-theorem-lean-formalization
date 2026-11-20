import Savitch.Sav.Loop
import Savitch.Outer.Esc

/-!
# Reachability from a fixed source, as a subroutine

Phase 4b-6 of the Savitch formalization (see `PLAN.md`).

`reachSub M` loads the source block from `tI` into `tU`, the target from `tW` into
`tV`, the depth `K` from `tKK` into the level counter, sets the mode to `call` and
runs the main loop. `Spec.reachSub`: afterwards the tapes represent `done r` with
`r = true` iff the target is reachable from the source along `GEdge`.
-/

set_option linter.unusedSectionVars false

namespace Savitch.Edge

open TM Machine Machine.NTM

variable {Λ Γ : Type} [Fintype Λ] [Fintype Γ] [DecidableEq Λ] [DecidableEq Γ]
variable {x : List Bool} {B : ℕ} {L : ℕ}

def tW : Fin NT := 22
def tI : Fin NT := 23
def tKK : Fin NT := 24
def tEsc : Fin NT := 25
def tAcc : Fin NT := 26
def tC₅ : Fin NT := 27
def tRu : Fin NT := 28

noncomputable def reachSub [NeZero (nR Λ Γ)] (M : NTM Λ Γ) : Code NT (Sym Λ Γ) :=
  zipPass tU tI .mk isRec (fun _ b => b) ++ zipPass tV tW .mk isRec (fun _ b => b) ++
    copyPass tKK tKc .mk (TM.isBit .z .o) id ++ setMd .call ++ mainLoop M

theorem gen_rel_eq (M : NTM Λ Γ) (hL : 0 < L) :
    Gen.Rel (EO M x hL) = M.GEdge x hL := by
  funext u v; simp [Gen.Rel, EO]

/-- What a finished Savitch run leaves behind, plus the constant registers. -/
def Regs [NeZero (nV Λ Γ L)] (K WK : ℕ) (a v : Fin (nV Λ Γ L)) (T : Tapes NT (Sym Λ Γ)) : Prop :=
  Lay tI .mk .blank T (cellsOf (digs a)) ∧ Lay tW .mk .blank T (cellsOf (digs v)) ∧
  ∃ l : List Bool, Holds tKK .mk .z .o T l ∧ l.length = WK ∧ bval l = K

open Classical in
theorem Spec.reachSub [NeZero (nV Λ Γ L)] [NeZero (nR Λ Γ)] (M : NTM Λ Γ) (hL : 0 < L)
    (hfit : x.length + 1 < 2 ^ L) {K WK : ℕ} (hWK : K < 2 ^ WK) (hN : nV Λ Γ L ≤ 2 ^ K)
    {a v : Fin (nV Λ Γ L)} {r₀ : Bool} {T : Tapes NT (Sym Λ Γ)}
    (hR : Rep L x K WK T (.done r₀)) (hG : Regs K WK a v T) (hT : T.Within B)
    (hB : (K + 1) * (L + 1) + WK + 8 ≤ B) :
    ∃ T', Spec (reachSub M) x B T T' ∧
      Rep L x K WK T' (.done (decide (Relation.ReflTransGen (M.GEdge x hL) a v))) ∧
      Regs K WK a v T' ∧ T.Agree Lo T' ∧ T'.Within B := by
  obtain ⟨hMd, ⟨a₀, hU⟩, ⟨b₀, hV⟩, ⟨_, lk, hK, hlk, _⟩, hS, hC⟩ := hR
  obtain ⟨hI, hW, lK, hKK, hlK, hvK⟩ := hG
  have hmb : (Sym.mk : Sym Λ Γ) ≠ .blank := fun h => by cases h
  have hLB : L + 2 ≤ B := by
    have := Nat.le_mul_of_pos_left (L + 1) (show 0 < K + 1 by omega); omega
  -- 1. source into `tU`
  obtain ⟨T₁, s1, hU₁, hI₁, ag1, ih1, hW₁⟩ := Spec.zipPass (x := x) (a := tU) (b := tI)
    (p := isRec) (F := fun _ b => b) (by decide) hmb hU (hI.toW hmb)
    (by rw [cellsOf_length, cellsOf_length, digs_length, digs_length]) (cellsOf_rec _) rfl
    (cellsOf_not_mk _)
    (by rw [zipWith_snd _ _ (by rw [cellsOf_length, cellsOf_length, digs_length, digs_length])]
        exact cellsOf_not_mk _)
    hT (by rw [cellsOf_length, digs_length]; exact hLB)
  rw [zipWith_snd _ _ (by rw [cellsOf_length, cellsOf_length, digs_length, digs_length])] at hU₁
  -- 2. target into `tV`
  have hV₁ := agree_lay ag1 (by decide) hV
  have hW₁' := agree_lay ag1 (by decide) hW
  obtain ⟨T₂, s2, hV₂, _, ag2, ih2, hW₂⟩ := Spec.zipPass (x := x) (a := tV) (b := tW)
    (p := isRec) (F := fun _ b => b) (by decide) hmb hV₁ (hW₁'.toW hmb)
    (by rw [cellsOf_length, cellsOf_length, digs_length, digs_length]) (cellsOf_rec _) rfl
    (cellsOf_not_mk _)
    (by rw [zipWith_snd _ _ (by rw [cellsOf_length, cellsOf_length, digs_length, digs_length])]
        exact cellsOf_not_mk _)
    hW₁ (by rw [cellsOf_length, digs_length]; exact hLB)
  rw [zipWith_snd _ _ (by rw [cellsOf_length, cellsOf_length, digs_length, digs_length])] at hV₂
  have ag12 : T.Agree (fun i => i = tU ∨ i = tV) T₂ :=
    (ag1.mono (fun _ h => Or.inl h)).trans (ag2.mono (fun _ h => Or.inr h))
  -- 3. the depth into the level counter
  have hKK₂ := hKK.congr (ag12 tKK (by decide)).1 (ag12 tKK (by decide)).2
  have hK₂ := hK.congr (ag12 tKc (by decide)).1 (ag12 tKc (by decide)).2
  have hbl : (lK.map (bit (Λ := Λ) (Γ := Γ))).length = lK.length := List.length_map _
  obtain ⟨T₃, s3, _, hKw₃, _, hKend₃, ag3, ih3, hW₃⟩ :=
    Spec.copyPassW (x := x) (p := TM.isBit (Sym.z : Sym Λ Γ) .o) (h := id) (show tKK ≠ tKc by decide)
      hKK₂.toW (by rw [hbl]; simp [TM.isBit, hKK₂.2.2.1, hKK₂.2.2.2.1]) hK₂.toW
      (by rw [List.length_map, hbl, hlk, hlK])
      (fun g hg => by obtain ⟨b, _, rfl⟩ := List.mem_map.1 hg; exact isBit_bit b)
      (fun g hg => by obtain ⟨b, _, rfl⟩ := List.mem_map.1 hg; exact bit_ne_mk b)
      (fun g hg => by obtain ⟨b, _, rfl⟩ := List.mem_map.1 hg; exact bit_ne_mk b) hW₂
      (by rw [hbl, hlK]; omega)
  rw [List.map_id] at hKw₃
  rw [hbl] at hKend₃
  have hK₃ : Holds tKc .mk .z .o T₃ lK := Holds.ofW hKw₃
    (by rw [hKend₃, hlK, ← hlk]; exact hK₂.2.2.1) (by rw [hKend₃, hlK, ← hlk]; exact hK₂.2.2.2.1)
  -- 4. mode `call`
  have s4 := Spec.write (x := x) (t := tMd) (g := (Sym.md .call : Sym Λ Γ)) hW₃
  set T₄ := T₃.write tMd (.md .call)
  have ag4 : T₃.Agree (fun i => i = tMd) T₄ := fun i hi => ⟨by simp [T₄, Tapes.write, hi], rfl⟩
  have ag04 : T.Agree (fun i => i = tU ∨ i = tV ∨ i = tKc ∨ i = tMd) T₄ :=
    ((ag12.mono (fun i h => by rcases h with h | h <;> simp [h])).trans
      (ag3.mono (fun i h => by simp [h]))).trans (ag4.mono (fun i h => by simp [h]))
  have hih : T₄.ih = T.ih := by show T₃.ih = T.ih; rw [ih3, ih2, ih1]
  have hRep : Rep L x K WK T₄ (Gen.init K a v) := by
    refine ⟨by simp [T₄, Tapes.read, Tapes.write_tp_self],
      agree_lay ((ag2.mono (fun _ h => (Or.inl h : _ ∨ _ ∨ _))).trans
        ((ag3.mono (fun _ h => (Or.inr (Or.inl h) : _ ∨ _ ∨ _))).trans
          (ag4.mono (fun _ h => (Or.inr (Or.inr h) : _ ∨ _ ∨ _))))) (by decide) hU₁,
      agree_lay ((ag3.mono (fun _ h => (Or.inl h : _ ∨ _))).trans
        (ag4.mono (fun _ h => (Or.inr h : _ ∨ _)))) (by decide) hV₂,
      ⟨lK, hK₃.congr (ag4 tKc (by decide)).1 (ag4 tKc (by decide)).2, hlK, hvK⟩,
      hS.agree ag04 (by decide) (by decide) (by decide) (by decide),
      hC.agree ag04 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) hih⟩
  -- 5. run the main loop
  have hrun := Gen.run_correct (EO M x hL) K a v
  have hdec := Gen.decides (EO M x hL) hN a v
  have hrel : Relation.ReflTransGen (Gen.Rel (EO M x hL)) a v ↔
      Relation.ReflTransGen (M.GEdge x hL) a v := by rw [gen_rel_eq]
  have hans : savitch (Gen.Rel (EO M x hL)) K a v =
      decide (Relation.ReflTransGen (M.GEdge x hL) a v) :=
    Bool.eq_iff_iff.2 ⟨fun h => decide_eq_true (hrel.1 (hdec.1 h)),
      fun h => hdec.2 (hrel.2 (of_decide_eq_true h))⟩
  rw [hans] at hrun
  obtain ⟨T₅, hl, hR₅, ag5⟩ := loop_done (B := B) M hL hfit hWK hB _ (Gen.init K a v) hrun T₄ hRep
    (Gen.reachable_depthInv (EO M x hL) K a v .refl) (Tapes.within_write hW₃)
  have s5 := Spec.whileDo hl
  have hW₅ : T₅.Within B := s5.target_within
  refine ⟨T₅, (((s1.seq s2).seq s3).seq s4).seq s5, hR₅, ?_,
    (ag04.mono (by decide)).trans ag5, hW₅⟩
  -- the constant registers survive: the loop only works on tapes below 22
  have hreg : Regs K WK a v T₄ := by
    refine ⟨agree_lay ag04 (by decide) hI, agree_lay ag04 (by decide) hW,
      lK, hKK.congr (ag04 tKK (by decide)).1 (ag04 tKK (by decide)).2, hlK, hvK⟩
  obtain ⟨h1, h2, l, h3, h4, h5⟩ := hreg
  exact ⟨h1.congr (ag5 tI (by decide)).1 (ag5 tI (by decide)).2,
    h2.congr (ag5 tW (by decide)).1 (ag5 tW (by decide)).2,
    l, h3.congr (ag5 tKK (by decide)).1 (ag5 tKK (by decide)).2, h4, h5⟩

end Savitch.Edge
