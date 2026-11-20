import Savitch.Sav.Rep

/-!
# The Savitch main-loop body: one step of the generic Phase 2 machine

Phase 4b-5 of the Savitch formalization (see `PLAN.md`).

`Rep K WK T s` says the tapes `T` represent the state `s` of `Gen` (the Phase 2
machine over `Fin (|Rec|^L)` with edge oracle `GEdge`):
* the mode cell `tMd` holds `call` / `ret r` / `done r`;
* for `call k a b st`, the registers `tU`, `tV` hold `a`, `b`, and counter `tKc`
  holds `k`; for `ret r st`, `tKc` holds the level of the top frame (or `K`);
* the stack tapes hold `st` (`StacksRep`), `tZ` holds the zero vertex, and the
  edge-test tapes satisfy `EInv`.

`body M` dispatches on the mode cell. One lemma per case of `Gen.step` shows that
running `body M` takes `Rep … s` to `Rep … (Gen.step E s)`.
-/

set_option linter.unusedSectionVars false

namespace Savitch.Edge

open TM Machine Machine.NTM

variable {Λ Γ : Type} [Fintype Λ] [Fintype Γ] [DecidableEq Λ] [DecidableEq Γ]
variable {x : List Bool} {B : ℕ} {L : ℕ}

/-! ### The edge oracle and the represented states -/

open Classical in
/-- The edge oracle of the Savitch graph. -/
noncomputable def EO (M : NTM Λ Γ) (x : List Bool) (hL : 0 < L) :
    Fin (nV Λ Γ L) → Fin (nV Λ Γ L) → Bool :=
  fun u v => decide (M.GEdge x hL u v)

/-- The level stored in the counter in `ret` mode. -/
def topK (K : ℕ) : List (GF Λ Γ L) → ℕ
  | [] => K
  | f :: _ => f.k

/-- Invariants shared by all modes. -/
def Common (L : ℕ) [NeZero (nV Λ Γ L)] (x : List Bool) (T : Tapes NT (Sym Λ Γ)) : Prop :=
  Lay tZ .mk .blank T (cellsOf (digs (Gen.zero : Fin (nV Λ Γ L)))) ∧ EInv (x := x) L T

def Ctr (WK v : ℕ) (T : Tapes NT (Sym Λ Γ)) : Prop :=
  ∃ l : List Bool, Holds tKc .mk .z .o T l ∧ l.length = WK ∧ bval l = v

/-- The tapes represent the state `s`. -/
def Rep (L : ℕ) [NeZero (nV Λ Γ L)] (x : List Bool) (K WK : ℕ) (T : Tapes NT (Sym Λ Γ)) :
    Gen.State (nV Λ Γ L) → Prop
  | .call k a b st => T.read tMd = .md .call ∧ Lay tU .mk .blank T (cellsOf (digs a)) ∧
      Lay tV .mk .blank T (cellsOf (digs b)) ∧ Ctr WK k T ∧ StacksRep L T st ∧
      Common L x T
  | .ret r st => T.read tMd = .md (.ret r) ∧
      (∃ a : Fin (nV Λ Γ L), Lay tU .mk .blank T (cellsOf (digs a))) ∧
      (∃ b : Fin (nV Λ Γ L), Lay tV .mk .blank T (cellsOf (digs b))) ∧
      Ctr WK (topK K st) T ∧ StacksRep L T st ∧ Common L x T
  | .done r => T.read tMd = .md (.done r) ∧
      (∃ a : Fin (nV Λ Γ L), Lay tU .mk .blank T (cellsOf (digs a))) ∧
      (∃ b : Fin (nV Λ Γ L), Lay tV .mk .blank T (cellsOf (digs b))) ∧
      (∃ v, Ctr WK v T) ∧ StacksRep L T [] ∧ Common L x T

/-! ### The code -/

def setMd (m : Mode) : Code NT (Sym Λ Γ) := [Instr.write tMd (.md m)]

/-- The tapes the Savitch machine works on (all others are left alone). -/
def Lo (i : Fin NT) : Prop := i.val < 22

instance : DecidablePred Lo := fun i => inferInstanceAs (Decidable (i.val < 22))

noncomputable def baseCode (M : NTM Λ Γ) : Code NT (Sym Λ Γ) :=
  cmpD tU tV tF₃ symR .yes .no ++ TM.home tU .mk ++ TM.home tV .mk ++ edgeTest M ++
    ifElse (.tape tF₃ (fun g => decide (g = .yes))) (setMd (.ret true))
      (ifElse (.tape tR (fun g => decide (g = .yes))) (setMd (.ret true)) (setMd (.ret false)))

noncomputable def recCode : Code NT (Sym Λ Γ) :=
  pushAll ++ zeroV ++ TM.decrH tKc .mk .z .o

noncomputable def callCode (M : NTM Λ Γ) : Code NT (Sym Λ Γ) :=
  TM.isZeroH tKc tF₄ .mk .z .o .yes .no ++
    ifElse (.tape tF₄ (fun g => decide (g = .yes))) (baseCode M) recCode

theorem bit_mem_rec {l : List Bool} : ∀ g ∈ l.map (bit (Λ := Λ) (Γ := Γ)), isRec g = false := by
  intro g hg; obtain ⟨b, _, rfl⟩ := List.mem_map.1 hg; cases b <;> rfl

/-! ### Transporting invariants across steps that do not touch them -/

section Transport

variable {S' : Fin NT → Prop} {T T' : Tapes NT (Sym Λ Γ)}

theorem EInv.agree (h : T.Agree S' T') (h1 : ¬S' tA₁) (h2 : ¬S' tP) (h3 : ¬S' tCU) (h4 : ¬S' tS)
    (h5 : ¬S' tA₂) (h6 : ¬S' tP₂) (hih : T'.ih = T.ih) (hI : EInv (x := x) L T) :
    EInv (x := x) L T' := by
  obtain ⟨⟨la, hA, hla⟩, ⟨lp, hP, hlp⟩, ⟨lc, hC, hlc⟩, ⟨⟨ls, hS, hls, hlsm⟩,
    ⟨l₂, hA₂, hl₂, hz, ho⟩, ⟨l₃, hP₂, hl₃⟩⟩⟩ := hI
  refine ⟨⟨la, agree_lay h h1 hA, hla⟩,
    ⟨lp, ⟨hP.1.congr (h tP h2).1 (h tP h2).2, by rw [hih]; exact hP.2.1,
      by rw [hih]; exact hP.2.2.1, hP.2.2.2⟩, hlp⟩,
    ⟨lc, hC.congr (h tCU h3).1 (h tCU h3).2, hlc⟩,
    ⟨⟨ls, agree_lay h h4 hS, hls, hlsm⟩,
      ⟨l₂, agree_layW h h5 hA₂, hl₂, by rw [(h tA₂ h5).1]; exact hz, by rw [(h tA₂ h5).1]; exact ho⟩,
      ⟨l₃, hP₂.congr (h tP₂ h6).1 (h tP₂ h6).2, hl₃⟩⟩⟩

theorem StackLay.agree {t : Fin NT} (h : T.Agree S' T') (ht : ¬S' t)
    {bs : List (List (Fin (nR Λ Γ)))} (hS : StackLay t L T bs) : StackLay t L T' bs :=
  ⟨by rw [(h t ht).1]; exact hS.1, hS.2.1, by rw [(h t ht).1]; exact hS.2.2.1,
    by rw [(h t ht).2]; exact hS.2.2.2⟩

theorem StacksRep.agree (h : T.Agree S' T') (h1 : ¬S' tSA) (h2 : ¬S' tSB) (h3 : ¬S' tSC)
    (h4 : ¬S' tSP) {st : List (GF Λ Γ L)} (hS : StacksRep L T st) : StacksRep L T' st :=
  ⟨hS.1.agree h h1, hS.2.1.agree h h2, hS.2.2.1.agree h h3,
    hS.2.2.2.congr (h tSP h4).1 (h tSP h4).2⟩

theorem Ctr.agree {WK v : ℕ} (h : T.Agree S' T') (h1 : ¬S' tKc) (hC : Ctr WK v T) : Ctr WK v T' := by
  obtain ⟨l, hl, hlen, hv⟩ := hC
  exact ⟨l, hl.congr (h tKc h1).1 (h tKc h1).2, hlen, hv⟩

theorem Common.agree [NeZero (nV Λ Γ L)] (h : T.Agree S' T') (hz : ¬S' tZ) (h1 : ¬S' tA₁)
    (h2 : ¬S' tP) (h3 : ¬S' tCU) (h4 : ¬S' tS) (h5 : ¬S' tA₂) (h6 : ¬S' tP₂) (hih : T'.ih = T.ih)
    (hC : Common L x T) : Common L x T' :=
  ⟨agree_lay h hz hC.1, hC.2.agree h h1 h2 h3 h4 h5 h6 hih⟩

end Transport

theorem topK_zero {K : ℕ} {st : List (GF Λ Γ L)} {a b : Fin (nV Λ Γ L)}
    (hD : Gen.DepthInv K (Gen.State.call 0 a b st)) : topK K st = 0 := by
  obtain ⟨hst, hk⟩ := hD
  cases st with
  | nil => simp [topK] at hk ⊢; omega
  | cons f st => simp only [Gen.StackOK, List.length_cons] at hst hk; simp only [topK]; omega

/-! ### Case `call 0`: the base case -/

open Classical in
theorem Spec.call_zero [NeZero (nV Λ Γ L)] (M : NTM Λ Γ) (hL : 0 < L)
    (hfit : x.length + 1 < 2 ^ L) {K WK : ℕ} {a b : Fin (nV Λ Γ L)} {st : List (GF Λ Γ L)}
    {T : Tapes NT (Sym Λ Γ)} (hR : Rep L x K WK T (.call 0 a b st))
    (hD : Gen.DepthInv K (Gen.State.call 0 a b st)) (hT : T.Within B) (hB : L + WK + 4 ≤ B) :
    ∃ T', Spec (callCode M) x B T T' ∧
      Rep L x K WK T' (Gen.step (EO M x hL) (.call 0 a b st)) ∧
      T.Agree (fun i => i = tS ∨ i = tA₁ ∨ i = tA₂ ∨ i = tP ∨ i = tP₂ ∨ i = tCU ∨ i = tK ∨
        i = tF ∨ i = tF₂ ∨ i = tG ∨ i = tR ∨ i = tF₃ ∨ i = tF₄ ∨ i = tMd ∨ i = tU ∨ i = tV ∨
        i = tKc) T' ∧
      T'.hd tMd = T.hd tMd ∧ T'.Within B := by
  obtain ⟨hMd, hU, hV, ⟨lk, hK, hlk, hvk⟩, hS, hZ, hE⟩ := hR
  have hzo : (Sym.z : Sym Λ Γ) ≠ .o := fun h => by cases h
  have hmz : (Sym.mk : Sym Λ Γ) ≠ .z := fun h => by cases h
  have hmo : (Sym.mk : Sym Λ Γ) ≠ .o := fun h => by cases h
  have hmb : (Sym.mk : Sym Λ Γ) ≠ .blank := fun h => by cases h
  have hla := digs_length a
  have hlb := digs_length b
  have hcla : (cellsOf (Λ := Λ) (Γ := Γ) (digs a)).length = L := by rw [cellsOf_length, hla]
  have hclb : (cellsOf (Λ := Λ) (Γ := Γ) (digs b)).length = L := by rw [cellsOf_length, hlb]
  -- 1. test the level for zero
  obtain ⟨T₁, s1, ⟨q1, q2, q3, q4, q5, q6, q7⟩, hW₁⟩ :=
    Spec.isZeroH (x := x) (t := tKc) (f := tF₄) (yes := .yes) (no := .no) (by decide) hzo hmz hmo
      hK hT (by rw [hlk]; omega)
  have hF₄ : T₁.read tF₄ = .yes := by rw [Tapes.read, q5, q1, hvk]; rfl
  have hU₁ := agree_lay q6 (by decide) hU
  have hV₁ := agree_lay q6 (by decide) hV
  -- 2. compare `a` and `b`
  obtain ⟨T₂, s2, c1, c2, c3, c4, c5, c6, c7⟩ := Spec.cmpD (x := x) (a := tU) (b := tV)
    (f := tF₃) (by decide) (by decide) (by decide) symR_inj (yes := .yes) (no := .no)
    (digs a) (digs b) T₁ (by rw [hla, hlb])
    (by rw [hU₁.2.2.2]; have := hU₁.2.1; rwa [cellsOf_length] at this)
    (by rw [hV₁.2.2.2]; have := hV₁.2.1; rwa [cellsOf_length] at this)
    (fun d => by
      rw [hU₁.2.2.2, Nat.add_comm, ← cellsOf_length (Λ := Λ) (Γ := Γ), hU₁.2.2.1]
      exact fun h => by simp [symR] at h)
    hW₁ (by rw [hU₁.2.2.2, hla]; omega) (by rw [hV₁.2.2.2, hla]; omega)
  simp only [Tapes.write_hd] at c1 c2 c4 c5 c6
  have hW₂ : T₂.Within B := s2.target_within
  have hT₂tp : ∀ i, i ≠ tF₃ → T₂.tp i = T₁.tp i := fun i hi => by
    rw [c3 i hi]; simp [Tapes.write, hi]
  have hF₃ : T₂.tp tF₃ (T₁.hd tF₃) = if digs a = digs b then .yes else .no := by
    rw [c1]; simp [Tapes.read, Tapes.write_tp_self]
  -- heads home
  have hh1 := Spec.home (x := x) tU .mk (T := T₂) (by rw [hT₂tp tU (by decide)]; exact hU₁.1)
    (by rw [hT₂tp tU (by decide)]
        exact home_ok hmb (cellsOf_not_mk _) hU₁.2.1 hU₁.2.2.1
          (by rw [c4, hU₁.2.2.2, hcla, hla]; omega))
    hW₂ (by omega)
  set T₃ := T₂.setHead tU 1
  have hW₃ : T₃.Within B := Tapes.within_setHead hW₂ (by omega)
  have hh2 := Spec.home (x := x) tV .mk (T := T₃)
    (by simp only [T₃, Tapes.setHead_tp]; rw [hT₂tp tV (by decide)]; exact hV₁.1)
    (by simp only [T₃, Tapes.setHead_tp]; rw [hT₂tp tV (by decide)]
        exact home_ok hmb (cellsOf_not_mk _) hV₁.2.1 hV₁.2.2.1
          (by rw [Tapes.setHead_hd_ne _ _ (by decide), c5, hV₁.2.2.2, hclb, hla]; omega))
    hW₃ (by omega)
  set T₄ := T₃.setHead tV 1
  have hW₄ : T₄.Within B := Tapes.within_setHead hW₃ (by omega)
  have ag14 : T₁.Agree (fun i => i = tF₃) T₄ := by
    intro i hi
    refine ⟨by simp only [T₄, T₃, Tapes.setHead_tp]; exact hT₂tp i hi, ?_⟩
    by_cases hiU : i = tU
    · subst hiU; simp [T₄, T₃, Tapes.setHead_hd_ne _ _ (show tU ≠ tV by decide), hU₁.2.2.2]
    · by_cases hiV : i = tV
      · subst hiV; simp [T₄, hV₁.2.2.2]
      · simp only [T₄, T₃, Tapes.setHead_hd_ne _ _ hiV, Tapes.setHead_hd_ne _ _ hiU]
        exact c6 i hiU hiV
  have hU₄ := agree_lay ag14 (by decide) hU₁
  have hV₄ := agree_lay ag14 (by decide) hV₁
  have ag04 : T.Agree (fun i => i = tKc ∨ i = tF₄ ∨ i = tF₃) T₄ :=
    (q6.mono (fun i h => by rcases h with h | h <;> simp [h])).trans
      (ag14.mono (fun i h => by simp [h]))
  have hih₄ : T₄.ih = T.ih := by
    show T₂.ih = T.ih; rw [c7]; simp [Tapes.write, q7]
  have hE₄ : EInv (x := x) L T₄ := hE.agree ag04 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hih₄
  -- 3. the edge test
  obtain ⟨T₅, s5, hR₅, hU₅, hV₅, hE₅, ag5, hRhd₅, hW₅⟩ := Spec.edgeTest (x := x) M hL hfit a b
    (by rw [← cellsOf_digs]; exact hU₄) (by rw [← cellsOf_digs]; exact hV₄.toW hmb) hE₄ hW₄
    (by omega)
  have hU₅' : Lay tU .mk .blank T₅ (cellsOf (digs a)) := agree_lay ag5 (by decide) hU₄
  have hV₅' : Lay tV .mk .blank T₅ (cellsOf (digs b)) := agree_lay ag5 (by decide) hV₄
  have hF₃₅ : T₅.read tF₃ = if digs a = digs b then .yes else .no := by
    rw [Tapes.read, (ag5 tF₃ (by decide)).2, (ag5 tF₃ (by decide)).1]
    simp only [T₄, T₃, Tapes.setHead_tp, Tapes.setHead_hd_ne _ _ (show tF₃ ≠ tV by decide),
      Tapes.setHead_hd_ne _ _ (show tF₃ ≠ tU by decide)]
    rw [c6 tF₃ (by decide) (by decide)]; exact hF₃
  have hR₅' : T₅.read tR = if M.GEdge x hL a b then (Sym.yes : Sym Λ Γ) else .no := by
    rw [Tapes.read, hRhd₅]; exact hR₅
  -- 4. set the mode
  set r := decide (a = b) || EO M x hL a b with hr
  have s6 : Spec (ifElse (.tape tF₃ (fun g => decide (g = .yes))) (setMd (.ret true))
      (ifElse (.tape tR (fun g => decide (g = .yes))) (setMd (.ret true)) (setMd (.ret false))))
      x B T₅ (T₅.write tMd (.md (.ret r))) := by
    by_cases hab : a = b
    · have : r = true := by simp [r, hab]
      rw [this]
      exact Spec.ifElse_true (by simp [Cond.eval, hF₃₅, hab]) hW₅ (Spec.write hW₅)
    · have hne : digs a ≠ digs b := fun h => hab (digs_inj.1 h)
      refine Spec.ifElse_false (by simp [Cond.eval, hF₃₅, hne]) hW₅ ?_
      by_cases hg : M.GEdge x hL a b
      · have : r = true := by simp [r, EO, hg]
        rw [this]
        exact Spec.ifElse_true (by simp [Cond.eval, hR₅', hg]) hW₅ (Spec.write hW₅)
      · have : r = false := by simp [r, EO, hg, hab]
        rw [this]
        exact Spec.ifElse_false (by simp [Cond.eval, hR₅', hg]) hW₅ (Spec.write hW₅)
  set T₆ := T₅.write tMd (.md (.ret r))
  have ag6 : T₅.Agree (fun i => i = tMd) T₆ := fun i hi => ⟨by simp [T₆, Tapes.write, hi], rfl⟩
  have agAll : T.Agree (fun i => i = tS ∨ i = tA₁ ∨ i = tA₂ ∨ i = tP ∨ i = tP₂ ∨ i = tCU ∨
      i = tK ∨ i = tF ∨ i = tF₂ ∨ i = tG ∨ i = tR ∨ i = tF₃ ∨ i = tF₄ ∨ i = tMd ∨ i = tU ∨
      i = tV ∨ i = tKc) T₆ :=
    ((ag04.mono (fun i h => by rcases h with h | h | h <;> simp [h])).trans
      (ag5.mono (fun i h => by
        rcases h with h | h | h | h | h | h | h | h | h | h | h <;> simp [h]))).trans
      (ag6.mono (fun i h => by simp [h]))
  have hMdhd : T₆.hd tMd = T.hd tMd := by
    have := (ag5 tMd (by decide)).2
    simp only [T₆, Tapes.write_hd]; rw [this, (ag04 tMd (by decide)).2]
  have hstep : Gen.step (EO M x hL) (.call 0 a b st) = .ret r st := rfl
  refine ⟨T₆, (s1.seq (Spec.ifElse_true (by simp [Cond.eval, hF₄]) hW₁
    ((((s2.seq hh1).seq hh2).seq s5).seq s6))), ?_, agAll, hMdhd, Tapes.within_write hW₅⟩
  rw [hstep]
  have agT := agAll
  refine ⟨by simp [T₆, Tapes.read, Tapes.write_tp_self], ⟨a, agree_lay ag6 (by decide) hU₅'⟩,
    ⟨b, agree_lay ag6 (by decide) hV₅'⟩, ⟨lk, ?_, hlk, by rw [hvk, topK_zero hD]⟩,
    hS.agree agT (by decide) (by decide) (by decide) (by decide), agree_lay agT (by decide) hZ,
    ?_⟩
  · have g5 := ag5 tKc (by decide)
    have g14 := ag14 tKc (by decide)
    exact hK.congr ((ag6 tKc (by decide)).1.trans (g5.1.trans (g14.1.trans q3)))
      ((ag6 tKc (by decide)).2.trans (g5.2.trans (g14.2.trans q4)))
  · exact hE₅.agree ag6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl


/-! ### Case `call (k+1)`: push a frame -/

theorem Spec.call_succ [NeZero (nV Λ Γ L)] (M : NTM Λ Γ) (hL : 0 < L) {K WK k : ℕ}
    {a b : Fin (nV Λ Γ L)} {st : List (GF Λ Γ L)} {T : Tapes NT (Sym Λ Γ)}
    (hR : Rep L x K WK T (.call (k + 1) a b st)) (hT : T.Within B)
    (hB : (st.length + 1) * L + st.length + WK + 4 ≤ B) :
    ∃ T', Spec (callCode M) x B T T' ∧
      Rep L x K WK T' (Gen.step (EO M x hL) (.call (k + 1) a b st)) ∧ T.Agree Lo T' ∧
      T'.Within B := by
  obtain ⟨hMd, hU, hV, ⟨lk, hK, hlk, hvk⟩, hS, hZ, hE⟩ := hR
  have hzo : (Sym.z : Sym Λ Γ) ≠ .o := fun h => by cases h
  have hmz : (Sym.mk : Sym Λ Γ) ≠ .z := fun h => by cases h
  have hmo : (Sym.mk : Sym Λ Γ) ≠ .o := fun h => by cases h
  have hyn : (Sym.yes : Sym Λ Γ) ≠ .no := fun h => by cases h
  have hLB : L + 2 ≤ B := by have := Nat.le_mul_of_pos_left L (show 0 < st.length + 1 by omega); omega
  -- 1. the level is not zero
  obtain ⟨T₁, s1, ⟨q1, q2, q3, q4, q5, q6, q7⟩, hW₁⟩ :=
    Spec.isZeroH (x := x) (t := tKc) (f := tF₄) (yes := .yes) (no := .no) (by decide) hzo hmz hmo
      hK hT (by rw [hlk]; omega)
  have hF₄ : T₁.read tF₄ = .no := by rw [Tapes.read, q5, q1, hvk]; rfl
  have hU₁ := agree_lay q6 (by decide) hU
  have hV₁ := agree_lay q6 (by decide) hV
  have hZ₁ := agree_lay q6 (by decide) hZ
  have hS₁ := hS.agree q6 (by decide) (by decide) (by decide) (by decide)
  -- 2. push the frame
  obtain ⟨T₂, s2, hS₂, ag2, ih2, hW₂⟩ := Spec.pushAll (x := x) k hU₁ hV₁ hZ₁ hS₁ hW₁ (by omega)
  have hV₂ := agree_lay ag2 (by decide) hV₁
  have hZ₂ := agree_lay ag2 (by decide) hZ₁
  -- 3. load zero into `tV`
  obtain ⟨T₃, s3, hV₃, hZ₃, ag3, ih3, hW₃⟩ := Spec.zeroV (x := x) hV₂ hZ₂
    (by rw [digs_length, digs_length]) hW₂ (by rw [digs_length]; exact hLB)
  -- 4. decrement the level
  have hK₃ : Holds tKc .mk .z .o T₃ lk := by
    have g := (q6.mono (fun i h => by simp [h]) : T.Agree (fun i => i = tKc ∨ i = tF₄) T₁)
    exact (hK.congr q3 q4).congr ((ag3 tKc (by decide)).1.trans (ag2 tKc (by decide)).1)
      ((ag3 tKc (by decide)).2.trans (ag2 tKc (by decide)).2)
  obtain ⟨T₄, s4, hK₄, hfr₄, hW₄⟩ := Spec.decrH (x := x) hzo hmz hmo hK₃ hW₃ (by rw [hlk]; omega)
  have ag4 := hfr₄.toAgree (S := fun i => i = tKc) rfl
  have ag14 : T₁.Agree (fun i => i = tSA ∨ i = tSB ∨ i = tSC ∨ i = tSP ∨ i = tV ∨ i = tKc) T₄ :=
    ((ag2.mono (fun i h => by rcases h with h | h | h | h <;> simp [h])).trans
      (ag3.mono (fun i h => by simp [h]))).trans (ag4.mono (fun i h => by simp [h]))
  have ag04 : T.Agree (fun i => i = tSA ∨ i = tSB ∨ i = tSC ∨ i = tSP ∨ i = tV ∨ i = tKc ∨
      i = tF₄) T₄ :=
    (q6.mono (fun i h => by rcases h with h | h <;> simp [h])).trans
      (ag14.mono (fun i h => by rcases h with h | h | h | h | h | h <;> simp [h]))
  have hih : T₄.ih = T.ih := by rw [hfr₄.1, ih3, ih2, q7]
  refine ⟨T₄, s1.seq (Spec.ifElse_false (by simp [Cond.eval, hF₄, Ne.symm hyn]) hW₁
    ((s2.seq s3).seq s4)), ?_, ag04.mono (by decide), hW₄⟩
  show Rep L x K WK T₄ (.call k a Gen.zero (⟨k, a, b, Gen.zero, .left⟩ :: st))
  refine ⟨?_, agree_lay ag04 (by decide) hU, agree_lay ag4 (by decide) hV₃,
    ⟨bdec lk, hK₄, by rw [bdec_length, hlk], by rw [bval_bdec lk (by omega), hvk]; rfl⟩,
    hS₂.agree ((ag3.mono (fun i h => Or.inl h)).trans
      (ag4.mono (fun i h => (Or.inr h : i = tV ∨ i = tKc)))) (by decide) (by decide) (by decide)
      (by decide),
    agree_lay ag04 (by decide) hZ,
    hE.agree ag04 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hih⟩
  rw [Tapes.read, (ag04 tMd (by decide)).1, (ag04 tMd (by decide)).2]; exact hMd

/-! ### The `ret` code -/

noncomputable def retTL : Code NT (Sym Λ Γ) :=
  readTop tSC tU ++ readTop tSB tV ++ setPh tSP true ++ setMd .call

noncomputable def retTR : Code NT (Sym Λ Γ) := popAll ++ TM.incrH tKc .mk .z .o

noncomputable def advCode [NeZero (nR Λ Γ)] : Code NT (Sym Λ Γ) :=
  readTop tSC tV ++ incV ++ cmpD tV tZ tF₄ symR .yes .no ++ TM.home tV .mk ++ TM.home tZ .mk ++
    ifElse (.tape tF₄ (fun g => decide (g = .yes)))
      (popAll ++ TM.incrH tKc .mk .z .o ++ setMd (.ret false))
      (backBlk tSC tU ++ pushBlk tV tSC ++ setPh tSP false ++ readTop tSA tU ++ setMd .call)

noncomputable def retCode [NeZero (nR Λ Γ)] (r : Bool) : Code NT (Sym Λ Γ) :=
  emptyBranch tSP (setMd (.done r))
    (phBranch tSP (if r then retTR else advCode) (if r then retTL else advCode))

theorem topK_succ {K : ℕ} {f : GF Λ Γ L} {st : List (GF Λ Γ L)}
    (h : Gen.StackOK K (f :: st)) : topK K st = topK K (f :: st) + 1 := by
  obtain ⟨h1, h2⟩ := h
  cases st with
  | nil => simp [topK] at h1 ⊢; omega
  | cons g st => obtain ⟨h3, _⟩ := h2; simp only [List.length_cons] at h1 h3; simp [topK]; omega

theorem phLay_cons {T : Tapes NT (Sym Λ Γ)} {f : GF Λ Γ L} {st : List (GF Λ Γ L)}
    (h : PhLay tSP T (((f :: st).map phBit).reverse)) :
    PhLay tSP T ((st.map phBit).reverse ++ [phBit f]) := by
  simpa using h

theorem stack_cons {t : Fin NT} {T : Tapes NT (Sym Λ Γ)} {f : GF Λ Γ L} {st : List (GF Λ Γ L)}
    {g : GF Λ Γ L → List (Fin (nR Λ Γ))} (h : StackLay t L T (((f :: st).map g).reverse)) :
    StackLay t L T ((st.map g).reverse ++ [g f]) := by
  simpa using h

/-! ### Case `ret r []`: halt -/

theorem Spec.ret_nil [NeZero (nV Λ Γ L)] [NeZero (nR Λ Γ)] (M : NTM Λ Γ) (hL : 0 < L) {K WK : ℕ}
    {r : Bool} {T : Tapes NT (Sym Λ Γ)} (hR : Rep L x K WK T (.ret r [])) (hT : T.Within B) :
    ∃ T', Spec (retCode (Λ := Λ) (Γ := Γ) r) x B T T' ∧
      Rep L x K WK T' (Gen.step (EO M x hL) (.ret r [])) ∧ T.Agree Lo T' ∧ T'.Within B := by
  obtain ⟨hMd, ⟨a, hU⟩, ⟨b, hV⟩, hK, hS, hC⟩ := hR
  have ag : T.Agree (fun i => i = tMd) (T.write tMd (.md (.done r))) :=
    fun i hi => ⟨by simp [Tapes.write, hi], rfl⟩
  refine ⟨T.write tMd (.md (.done r)), Spec.emptyBranch hS.2.2.2 hT
    (by rw [ite_pos' (by simp)]; exact Spec.write hT), ?_, ag.mono (by decide),
    Tapes.within_write hT⟩
  refine ⟨by simp [Tapes.read, Tapes.write_tp_self], ⟨a, agree_lay ag (by decide) hU⟩,
    ⟨b, agree_lay ag (by decide) hV⟩, ⟨_, hK.agree ag (by decide)⟩,
    hS.agree ag (by decide) (by decide) (by decide) (by decide),
    hC.agree ag (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) rfl⟩

/-! ### Case `ret true` on a left frame: call the right half -/

theorem Spec.ret_true_left [NeZero (nV Λ Γ L)] [NeZero (nR Λ Γ)] (M : NTM Λ Γ) (hL : 0 < L)
    {K WK k : ℕ} {a b c : Fin (nV Λ Γ L)} {st : List (GF Λ Γ L)} {T : Tapes NT (Sym Λ Γ)}
    (hR : Rep L x K WK T (.ret true (⟨k, a, b, c, .left⟩ :: st))) (hT : T.Within B)
    (hB : (st.length + 1) * L + st.length + 4 ≤ B) :
    ∃ T', Spec (retCode (Λ := Λ) (Γ := Γ) true) x B T T' ∧
      Rep L x K WK T' (Gen.step (EO M x hL) (.ret true (⟨k, a, b, c, .left⟩ :: st))) ∧
      T.Agree Lo T' ∧ T'.Within B := by
  obtain ⟨hMd, ⟨a₀, hU⟩, ⟨b₀, hV⟩, hK, hS, hC⟩ := hR
  obtain ⟨hSA, hSB, hSC, hSP⟩ := hS
  have hLB : L + 2 ≤ B := by have := Nat.le_mul_of_pos_left L (show 0 < st.length + 1 by omega); omega
  have hSC' := stack_cons hSC
  have hSB' := stack_cons hSB
  have hSP' := phLay_cons hSP
  have hlen : ((st.map fun f => digs f.c).reverse).length = st.length := by simp
  -- load `c` into `tU`
  obtain ⟨T₁, s1, hU₁, hSC₁, ag1, ih1, hW₁⟩ := Spec.readTop (x := x) (t := tSC) (R := tU)
    (by decide) hU (cellsOf_rec _) (by rw [cellsOf_length, digs_length]) hSC' hT
    (by rw [hlen]; omega)
  -- load `b` into `tV`
  have hV₁ := agree_lay ag1 (by decide) hV
  have hSB₁ := hSB'.agree ag1 (by decide)
  have hlenB : ((st.map fun f => digs f.b).reverse).length = st.length := by simp
  obtain ⟨T₂, s2, hV₂, hSB₂, ag2, ih2, hW₂⟩ := Spec.readTop (x := x) (t := tSB) (R := tV)
    (by decide) hV₁ (cellsOf_rec _) (by rw [cellsOf_length, digs_length]) hSB₁ hW₁
    (by rw [hlenB]; omega)
  have ag12 : T.Agree (fun i => i = tU ∨ i = tV) T₂ :=
    (ag1.mono (fun i h => Or.inl h)).trans (ag2.mono (fun i h => Or.inr h))
  -- flip the phase
  have hSP₂ := hSP'.congr (ag12 tSP (by decide)).1 (ag12 tSP (by decide)).2
  obtain ⟨T₃, s3, hSP₃, ag3, ih3, hW₃⟩ := Spec.setPh (x := x) (b₀ := false) true hSP₂ hW₂
    (by simp; omega)
  -- set the mode
  have s4 := Spec.write (x := x) (t := tMd) (g := (Sym.md .call : Sym Λ Γ)) hW₃
  set T₄ := T₃.write tMd (.md .call)
  have ag4 : T₃.Agree (fun i => i = tMd) T₄ := fun i hi => ⟨by simp [T₄, Tapes.write, hi], rfl⟩
  have agA : T.Agree (fun i => i = tU ∨ i = tV ∨ i = tSP ∨ i = tMd) T₄ :=
    ((ag12.mono (fun i h => by rcases h with h | h <;> simp [h])).trans
      (ag3.mono (fun i h => by simp [h]))).trans (ag4.mono (fun i h => by simp [h]))
  have hih : T₄.ih = T.ih := by
    show T₃.ih = T.ih; rw [ih3, ih2, ih1]
  have hNe : ((⟨k, a, b, c, .left⟩ :: st : List (GF Λ Γ L)).map phBit).reverse ≠ [] := by simp
  refine ⟨T₄, Spec.emptyBranch hSP hT (by
      rw [ite_neg' hNe]
      exact Spec.phBranch (b := false) hSP' hT (((s1.seq s2).seq s3).seq s4)), ?_,
    agA.mono (by decide), Tapes.within_write hW₃⟩
  show Rep L x K WK T₄ (.call k c b (⟨k, a, b, c, .right⟩ :: st))
  have g23 := (ag2.mono (fun i h => (Or.inl h : i = tV ∨ i = tSP ∨ i = tMd))).trans
    ((ag3.mono (fun i h => (Or.inr (Or.inl h) : i = tV ∨ i = tSP ∨ i = tMd))).trans
      (ag4.mono (fun i h => (Or.inr (Or.inr h) : i = tV ∨ i = tSP ∨ i = tMd))))
  have g34 : T₂.Agree (fun i => i = tSP ∨ i = tMd) T₄ :=
    (ag3.mono (fun _ h => Or.inl h)).trans (ag4.mono (fun _ h => Or.inr h))
  refine ⟨by simp [T₄, Tapes.read, Tapes.write_tp_self], agree_lay g23 (by decide) hU₁,
    agree_lay g34 (by decide) hV₂,
    hK.agree agA (by decide), ⟨?_, ?_, ?_, ?_⟩,
    hC.agree agA (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) hih⟩
  · simpa using hSA.agree agA (by decide)
  · simpa using hSB₂.agree g34 (by decide)
  · simpa using hSC₁.agree g23 (by decide)
  · have := hSP₃.congr (ag4 tSP (by decide)).1 (ag4 tSP (by decide)).2
    simpa [phBit] using this

/-! ### Case `ret true` on a right frame: pop and return -/

theorem Spec.ret_true_right [NeZero (nV Λ Γ L)] [NeZero (nR Λ Γ)] (M : NTM Λ Γ) (hL : 0 < L)
    {K WK k : ℕ} {a b c : Fin (nV Λ Γ L)} {st : List (GF Λ Γ L)} {T : Tapes NT (Sym Λ Γ)}
    (hR : Rep L x K WK T (.ret true (⟨k, a, b, c, .right⟩ :: st)))
    (hD : Gen.DepthInv K (Gen.State.ret true (⟨k, a, b, c, .right⟩ :: st)))
    (hWK : K < 2 ^ WK) (hT : T.Within B) (hB : L + WK + 4 ≤ B) :
    ∃ T', Spec (retCode (Λ := Λ) (Γ := Γ) true) x B T T' ∧
      Rep L x K WK T' (Gen.step (EO M x hL) (.ret true (⟨k, a, b, c, .right⟩ :: st))) ∧
      T.Agree Lo T' ∧ T'.Within B := by
  obtain ⟨hMd, ⟨a₀, hU⟩, ⟨b₀, hV⟩, ⟨lk, hK, hlk, hvk⟩, hS, hC⟩ := hR
  have hzo : (Sym.z : Sym Λ Γ) ≠ .o := fun h => by cases h
  have hmz : (Sym.mk : Sym Λ Γ) ≠ .z := fun h => by cases h
  have hmo : (Sym.mk : Sym Λ Γ) ≠ .o := fun h => by cases h
  have hSP' := phLay_cons hS.2.2.2
  -- pop the frame
  obtain ⟨T₁, s1, hS₁, ag1, ih1, hW₁⟩ := Spec.popAll (x := x) hU (digs_length a₀) hS hT
    (by omega)
  -- the level goes up by one
  have hK₁ := hK.congr (ag1 tKc (by decide)).1 (ag1 tKc (by decide)).2
  have hk : topK K (⟨k, a, b, c, .right⟩ :: st : List (GF Λ Γ L)) + 1 ≤ K := by
    have h1 : k + (st.length + 1) = K := hD.1
    show k + 1 ≤ K; omega
  obtain ⟨T₂, s2, hK₂, hfr₂, hW₂⟩ := Spec.incrH (x := x) hzo hmz hmo hK₁ hW₁ (by rw [hlk]; omega)
  have ag2 := hfr₂.toAgree (S := fun i => i = tKc) rfl
  have hNe : ((⟨k, a, b, c, .right⟩ :: st : List (GF Λ Γ L)).map phBit).reverse ≠ [] := by simp
  have agA : T.Agree (fun i => i = tSA ∨ i = tSB ∨ i = tSC ∨ i = tSP ∨ i = tKc) T₂ :=
    (ag1.mono (fun i h => by rcases h with h | h | h | h <;> simp [h])).trans
      (ag2.mono (fun i h => by simp [h]))
  refine ⟨T₂, Spec.emptyBranch hS.2.2.2 hT (by
      rw [ite_neg' hNe]
      exact Spec.phBranch (b := true) hSP' hT (s1.seq s2)), ?_, agA.mono (by decide), hW₂⟩
  show Rep L x K WK T₂ (.ret true st)
  refine ⟨?_, ⟨a₀, agree_lay agA (by decide) hU⟩, ⟨b₀, agree_lay agA (by decide) hV⟩,
    ⟨binc lk, hK₂, by rw [binc_length, hlk], ?_⟩, hS₁.agree ag2 (by decide) (by decide)
      (by decide) (by decide),
    hC.agree agA (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by rw [hfr₂.1, ih1])⟩
  · rw [Tapes.read, (agA tMd (by decide)).1, (agA tMd (by decide)).2]; exact hMd
  · rw [bval_binc lk (by rw [hvk, hlk]; omega), hvk, topK_succ hD]

/-! ### Case `ret false`: advance to the next midpoint -/

theorem dval_dinc_digs [NeZero (nR Λ Γ)] (c : Fin (nV Λ Γ L)) :
    dval (dinc (digs c)) = (c.val + 1) % nV Λ Γ L := by
  rw [dval_dinc_mod, dval_digs, digs_length]

theorem wrap_iff [NeZero (nR Λ Γ)] [NeZero (nV Λ Γ L)] (c : Fin (nV Λ Γ L)) :
    dinc (digs c) = digs (Gen.zero : Fin (nV Λ Γ L)) ↔ ¬ (c.val + 1 < nV Λ Γ L) := by
  have hc := c.isLt
  constructor
  · intro h hlt
    have := congrArg dval h
    rw [dval_dinc_digs, dval_digs, Nat.mod_eq_of_lt hlt] at this
    simp [Gen.zero] at this
  · intro h
    apply dval_inj (by rw [dinc_length, digs_length, digs_length])
    rw [dval_dinc_digs, dval_digs, show c.val + 1 = nV Λ Γ L by omega, Nat.mod_self]
    rfl

theorem next_digs [NeZero (nR Λ Γ)] (c : Fin (nV Λ Γ L)) (h : c.val + 1 < nV Λ Γ L) :
    dinc (digs c) = digs (⟨c.val + 1, h⟩ : Fin (nV Λ Γ L)) := by
  apply dval_inj (by rw [dinc_length, digs_length, digs_length])
  rw [dval_dinc_digs, dval_digs, Nat.mod_eq_of_lt h]

theorem Spec.advCode [NeZero (nV Λ Γ L)] [NeZero (nR Λ Γ)] {K WK k : ℕ} {a b c : Fin (nV Λ Γ L)}
    {ph : Gen.Phase} {st : List (GF Λ Γ L)} {T : Tapes NT (Sym Λ Γ)}
    (hR : Rep L x K WK T (.ret false (⟨k, a, b, c, ph⟩ :: st)))
    (hD : Gen.DepthInv K (Gen.State.ret false (⟨k, a, b, c, ph⟩ :: st)))
    (hWK : K < 2 ^ WK) (hT : T.Within B) (hB : (st.length + 1) * L + st.length + WK + 4 ≤ B) :
    ∃ T', Spec (advCode (Λ := Λ) (Γ := Γ)) x B T T' ∧
      Rep L x K WK T' (Gen.advance k a b c st) ∧ T.Agree Lo T' ∧ T'.Within B := by
  obtain ⟨hMd, ⟨a₀, hU⟩, ⟨b₀, hV⟩, ⟨lk, hK, hlk, hvk⟩, hS, hC⟩ := hR
  have hzo : (Sym.z : Sym Λ Γ) ≠ .o := fun h => by cases h
  have hmz : (Sym.mk : Sym Λ Γ) ≠ .z := fun h => by cases h
  have hmo : (Sym.mk : Sym Λ Γ) ≠ .o := fun h => by cases h
  have hmb : (Sym.mk : Sym Λ Γ) ≠ .blank := fun h => by cases h
  have hLB : L + 2 ≤ B := by have := Nat.le_mul_of_pos_left L (show 0 < st.length + 1 by omega); omega
  obtain ⟨hSA, hSB, hSC, hSP⟩ := hS
  have hSC' := stack_cons hSC
  have hlenC : ((st.map fun f => digs f.c).reverse).length = st.length := by simp
  -- 1. load `c`
  obtain ⟨T₁, s1, hV₁, hSC₁, ag1, ih1, hW₁⟩ := Spec.readTop (x := x) (t := tSC) (R := tV)
    (by decide) hV (cellsOf_rec _) (by rw [cellsOf_length, digs_length]) hSC' hT
    (by rw [hlenC]; omega)
  -- 2. increment it
  obtain ⟨T₂, s2, hV₂, ag2, ih2, hW₂⟩ := Spec.incV (x := x) hV₁ hW₁ (by rw [digs_length]; omega)
  have ag12 : T.Agree (fun i => i = tV) T₂ := ag1.trans ag2
  have hZ₂ := agree_lay ag12 (by decide) hC.1
  -- 3. compare with zero
  have hl1 := dinc_length (digs c)
  have hl2 := digs_length (Gen.zero : Fin (nV Λ Γ L))
  have hlc := digs_length c
  obtain ⟨T₃, s3, c1, c2, c3, c4, c5, c6, c7⟩ := Spec.cmpD (x := x) (a := tV) (b := tZ)
    (f := tF₄) (by decide) (by decide) (by decide) symR_inj (yes := .yes) (no := .no)
    (dinc (digs c)) (digs Gen.zero) T₂ (by rw [hl1, hl2, hlc])
    (by rw [hV₂.2.2.2]; have := hV₂.2.1; rwa [cellsOf_length] at this)
    (by rw [hZ₂.2.2.2]; have := hZ₂.2.1; rwa [cellsOf_length] at this)
    (fun d => by
      rw [hV₂.2.2.2, Nat.add_comm, ← cellsOf_length (Λ := Λ) (Γ := Γ), hV₂.2.2.1]
      exact fun h => by simp [symR] at h)
    hW₂ (by rw [hV₂.2.2.2, hl1, hlc]; omega) (by rw [hZ₂.2.2.2, hl1, hlc]; omega)
  simp only [Tapes.write_hd] at c1 c2 c4 c5 c6
  have hW₃ : T₃.Within B := s3.target_within
  have hT₃tp : ∀ i, i ≠ tF₄ → T₃.tp i = T₂.tp i := fun i hi => by
    rw [c3 i hi]; simp [Tapes.write, hi]
  have hF₄ : T₃.tp tF₄ (T₂.hd tF₄) =
      if dinc (digs c) = digs (Gen.zero : Fin (nV Λ Γ L)) then .yes else .no := by
    rw [c1]; simp [Tapes.read, Tapes.write_tp_self]
  -- 4. heads home
  have hh1 := Spec.home (x := x) tV .mk (T := T₃) (by rw [hT₃tp tV (by decide)]; exact hV₂.1)
    (by rw [hT₃tp tV (by decide)]
        exact home_ok hmb (cellsOf_not_mk _) hV₂.2.1 hV₂.2.2.1
          (by rw [c4, hV₂.2.2.2, cellsOf_length, hl1]; omega))
    hW₃ (by omega)
  set T₄ := T₃.setHead tV 1
  have hW₄ : T₄.Within B := Tapes.within_setHead hW₃ (by omega)
  have hh2 := Spec.home (x := x) tZ .mk (T := T₄)
    (by simp only [T₄, Tapes.setHead_tp]; rw [hT₃tp tZ (by decide)]; exact hZ₂.1)
    (by simp only [T₄, Tapes.setHead_tp]; rw [hT₃tp tZ (by decide)]
        exact home_ok hmb (cellsOf_not_mk _) hZ₂.2.1 hZ₂.2.2.1
          (by rw [Tapes.setHead_hd_ne _ _ (by decide), c5, hZ₂.2.2.2, cellsOf_length, hl2, hl1,
            hlc]; omega))
    hW₄ (by omega)
  set T₅ := T₄.setHead tZ 1
  have hW₅ : T₅.Within B := Tapes.within_setHead hW₄ (by omega)
  have ag25 : T₂.Agree (fun i => i = tF₄) T₅ := by
    intro i hi
    refine ⟨by simp only [T₅, T₄, Tapes.setHead_tp]; exact hT₃tp i hi, ?_⟩
    by_cases hiZ : i = tZ
    · subst hiZ; simp [T₅, hZ₂.2.2.2]
    · by_cases hiV : i = tV
      · subst hiV; simp [T₅, T₄, Tapes.setHead_hd_ne _ _ (show tV ≠ tZ by decide), hV₂.2.2.2]
      · simp only [T₅, T₄, Tapes.setHead_hd_ne _ _ hiZ, Tapes.setHead_hd_ne _ _ hiV]
        exact c6 i hiV hiZ
  have hF4hd : T₅.hd tF₄ = T₂.hd tF₄ := by
    simp only [T₅, T₄, Tapes.setHead_hd_ne _ _ (show tF₄ ≠ tZ by decide),
      Tapes.setHead_hd_ne _ _ (show tF₄ ≠ tV by decide)]
    exact c6 tF₄ (by decide) (by decide)
  have hread : T₅.read tF₄ =
      if dinc (digs c) = digs (Gen.zero : Fin (nV Λ Γ L)) then .yes else .no := by
    rw [Tapes.read, hF4hd]; simp only [T₅, T₄, Tapes.setHead_tp]; exact hF₄
  have ag15 : T.Agree (fun i => i = tV ∨ i = tF₄) T₅ :=
    (ag12.mono (fun _ h => Or.inl h)).trans (ag25.mono (fun _ h => Or.inr h))
  have hV₅ : Lay tV .mk .blank T₅ (cellsOf (dinc (digs c))) := by
    refine hV₂.congr ?_ ?_
    · simp only [T₅, T₄, Tapes.setHead_tp]; exact hT₃tp tV (by decide)
    · simp [T₅, T₄, Tapes.setHead_hd_ne _ _ (show tV ≠ tZ by decide), hV₂.2.2.2]
  have hU₅ := agree_lay ag15 (by decide) hU
  have hih₅ : T₅.ih = T.ih := by
    show T₃.ih = T.ih; rw [c7]; simp [Tapes.write, ih2, ih1]
  have hSfull : StacksRep L T₅ (⟨k, a, b, c, ph⟩ :: st) :=
    ⟨hSA.agree ag15 (by decide), hSB.agree ag15 (by decide), hSC.agree ag15 (by decide),
      hSP.congr (ag15 tSP (by decide)).1 (ag15 tSP (by decide)).2⟩
  by_cases hlt : c.val + 1 < nV Λ Γ L
  · -- continue with the next midpoint
    have hne : dinc (digs c) ≠ digs (Gen.zero : Fin (nV Λ Γ L)) := fun h => (wrap_iff c).1 h hlt
    have hc' := next_digs c hlt
    rw [hc'] at hV₅
    set c' : Fin (nV Λ Γ L) := ⟨c.val + 1, hlt⟩
    have hSC₅ := stack_cons hSfull.2.2.1
    have hm : L ≤ T₅.hd tSC := by
      rw [hSC₅.2.2.2]; simp [Nat.succ_mul]; omega
    have s6 := Spec.backBlk (x := x) (t := tSC) (R := tU) (by decide) hU₅ (cellsOf_rec _)
      (by rw [cellsOf_length, digs_length]) hm hW₅ hLB
    set T₆ := T₅.setHead tSC (T₅.hd tSC - L)
    have hW₆ : T₆.Within B := s6.target_within
    have hSC₆ : StackLay tSC L T₆ ((st.map fun f => digs f.c).reverse) := hSC₅.pop
    have hV₆ : Lay tV .mk .blank T₆ (cellsOf (digs c')) :=
      hV₅.congr rfl (Tapes.setHead_hd_ne _ _ (by decide) _)
    obtain ⟨T₇, s7, hV₇, hSC₇, ag7, ih7, hW₇⟩ := Spec.pushBlk (x := x) (R := tV) (t := tSC)
      (by decide) hV₆ (digs_length _) hSC₆ hW₆ (by rw [hlenC]; omega)
    have ag57 : T₅.Agree (fun i => i = tSC) T₇ := by
      intro i hi
      exact ⟨(ag7 i hi).1, by rw [(ag7 i hi).2, Tapes.setHead_hd_ne _ _ hi]⟩
    have hSP₇ := (phLay_cons hSfull.2.2.2).congr (ag57 tSP (by decide)).1 (ag57 tSP (by decide)).2
    obtain ⟨T₈, s8, hSP₈, ag8, ih8, hW₈⟩ := Spec.setPh (x := x) false hSP₇ hW₇ (by simp; omega)
    have ag58 : T₅.Agree (fun i => i = tSC ∨ i = tSP) T₈ :=
      (ag57.mono (fun _ h => Or.inl h)).trans (ag8.mono (fun _ h => Or.inr h))
    have hSA₈ := (stack_cons hSfull.1).agree ag58 (by decide)
    have hU₈ := agree_lay ag58 (by decide) hU₅
    have hlenA : ((st.map fun f => digs f.a).reverse).length = st.length := by simp
    obtain ⟨T₉, s9, hU₉, hSA₉, ag9, ih9, hW₉⟩ := Spec.readTop (x := x) (t := tSA) (R := tU)
      (by decide) hU₈ (cellsOf_rec _) (by rw [cellsOf_length, digs_length]) hSA₈ hW₈
      (by rw [hlenA]; omega)
    have s10 := Spec.write (x := x) (t := tMd) (g := (Sym.md .call : Sym Λ Γ)) hW₉
    set T₁₀ := T₉.write tMd (.md .call)
    have ag10 : T₉.Agree (fun i => i = tMd) T₁₀ := fun i hi => ⟨by simp [T₁₀, Tapes.write, hi], rfl⟩
    have ag510 : T₅.Agree (fun i => i = tSC ∨ i = tSP ∨ i = tU ∨ i = tMd) T₁₀ :=
      ((ag58.mono (fun i h => by rcases h with h | h <;> simp [h])).trans
        (ag9.mono (fun i h => by simp [h]))).trans (ag10.mono (fun i h => by simp [h]))
    have ag010 : T.Agree (fun i => i = tV ∨ i = tF₄ ∨ i = tSC ∨ i = tSP ∨ i = tU ∨ i = tMd) T₁₀ :=
      (ag15.mono (fun i h => by rcases h with h | h <;> simp [h])).trans
        (ag510.mono (fun i h => by rcases h with h | h | h | h <;> simp [h]))
    have hcond : Cond.eval x T₅ (.tape tF₄ (fun g => decide (g = (Sym.yes : Sym Λ Γ)))) = false := by
      simp [Cond.eval, hread, hne]
    refine ⟨T₁₀, ((((s1.seq s2).seq s3).seq hh1).seq hh2).seq
      (Spec.ifElse_false hcond hW₅ ((((s6.seq s7).seq s8).seq s9).seq s10)), ?_,
      ag010.mono (by decide), Tapes.within_write hW₉⟩
    rw [show Gen.advance k a b c st = .call k a c' (⟨k, a, b, c', .left⟩ :: st) by
      simp only [Gen.advance, hlt, ↓reduceDIte]; rfl]
    have g9 := (ag8.mono (fun _ h => (Or.inl h : _ ∨ _))).trans
      ((ag9.mono (fun _ h => (Or.inr (Or.inl h) : _ ∨ _ ∨ _))).trans
        (ag10.mono (fun _ h => (Or.inr (Or.inr h) : _ ∨ _ ∨ _))))
    refine ⟨by simp [T₁₀, Tapes.read, Tapes.write_tp_self], agree_lay ag10 (by decide) hU₉,
      ?_, ⟨lk, hK.congr (ag010 tKc (by decide)).1 (ag010 tKc (by decide)).2, hlk, hvk⟩,
      ⟨?_, ?_, ?_, ?_⟩,
      hC.agree ag010 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by rw [show T₁₀.ih = T₉.ih from rfl, ih9, ih8, ih7]; exact hih₅)⟩
    · exact hV₇.congr ((g9 tV (by decide)).1) ((g9 tV (by decide)).2)
    · simpa using hSA₉.agree ag10 (by decide)
    · simpa using hSB.agree ag010 (by decide)
    · simpa using hSC₇.agree g9 (by decide)
    · have g10 : T₈.Agree (fun i => i = tU ∨ i = tMd) T₁₀ :=
        (ag9.mono (fun _ h => Or.inl h)).trans (ag10.mono (fun _ h => Or.inr h))
      have := hSP₈.congr (g10 tSP (by decide)).1 (g10 tSP (by decide)).2
      simpa [phBit] using this
  · -- wrapped around: pop and return `false`
    have heq : dinc (digs c) = digs (Gen.zero : Fin (nV Λ Γ L)) := (wrap_iff c).2 hlt
    have hcond : Cond.eval x T₅ (.tape tF₄ (fun g => decide (g = (Sym.yes : Sym Λ Γ)))) = true := by
      simp [Cond.eval, hread, heq]
    obtain ⟨T₆, s6, hS₆, ag6, ih6, hW₆⟩ := Spec.popAll (x := x) hU₅ (digs_length a₀) hSfull hW₅
      hLB
    have hK₆ := (hK.congr (ag15 tKc (by decide)).1 (ag15 tKc (by decide)).2).congr
      (ag6 tKc (by decide)).1 (ag6 tKc (by decide)).2
    have hk : k + 1 ≤ K := by
      have h1 : k + (st.length + 1) = K := hD.1
      omega
    obtain ⟨T₇, s7, hK₇, hfr₇, hW₇⟩ := Spec.incrH (x := x) hzo hmz hmo hK₆ hW₆ (by rw [hlk]; omega)
    have s8 := Spec.write (x := x) (t := tMd) (g := (Sym.md (.ret false) : Sym Λ Γ)) hW₇
    set T₈ := T₇.write tMd (.md (.ret false))
    have ag8 : T₇.Agree (fun i => i = tMd) T₈ := fun i hi => ⟨by simp [T₈, Tapes.write, hi], rfl⟩
    have ag58 : T₅.Agree (fun i => i = tSA ∨ i = tSB ∨ i = tSC ∨ i = tSP ∨ i = tKc ∨ i = tMd) T₈ :=
      ((ag6.mono (fun i h => by rcases h with h | h | h | h <;> simp [h])).trans
        ((hfr₇.toAgree (S := fun i => i = tKc) rfl).mono (fun i h => by simp [h]))).trans
        (ag8.mono (fun i h => by simp [h]))
    have ag08 : T.Agree (fun i => i = tV ∨ i = tF₄ ∨ i = tSA ∨ i = tSB ∨ i = tSC ∨ i = tSP ∨
        i = tKc ∨ i = tMd) T₈ :=
      (ag15.mono (fun i h => by rcases h with h | h <;> simp [h])).trans
        (ag58.mono (fun i h => by rcases h with h | h | h | h | h | h <;> simp [h]))
    refine ⟨T₈, ((((s1.seq s2).seq s3).seq hh1).seq hh2).seq
      (Spec.ifElse_true hcond hW₅ ((s6.seq s7).seq s8)), ?_, ag08.mono (by decide),
      Tapes.within_write hW₇⟩
    rw [show Gen.advance k a b c st = .ret false st by simp only [Gen.advance, hlt, ↓reduceDIte]]
    refine ⟨by simp [T₈, Tapes.read, Tapes.write_tp_self], ⟨a₀, agree_lay ag08 (by decide) hU⟩,
      ⟨Gen.zero, agree_lay ag58 (by decide) (heq ▸ hV₅)⟩,
      ⟨binc lk, hK₇.congr (ag8 tKc (by decide)).1 (ag8 tKc (by decide)).2,
        by rw [binc_length, hlk], by
          rw [bval_binc lk (by rw [hvk, hlk]; simp only [topK]; omega), hvk, topK_succ hD]⟩,
      hS₆.agree (((hfr₇.toAgree (S := fun i => i = tKc) rfl).mono (fun _ h => Or.inl h)).trans
        (ag8.mono (fun _ h => Or.inr h)) : T₆.Agree (fun i => i = tKc ∨ i = tMd) T₈)
        (by decide) (by decide) (by decide) (by decide),
      hC.agree ag08 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by rw [show T₈.ih = T₇.ih from rfl, hfr₇.1, ih6]; exact hih₅)⟩

end Savitch.Edge
