import Savitch.Outer.Build

/-!
# Per-width setup routines: input-fit test, depth counter, and initial block layout

Phase 4b-6 of the Savitch formalization (see `PLAN.md`).

From the ruler tape `tRu` holding `L` copies of a record:
* `resetIn`: rewind the input head to position `0` without touching any work tape.
* `fitTest`: test whether `x.length + 1 < 2 ^ L`, writing `yes` or `no` on `tF₂`
  and leaving `ih = 0` (`Spec.fitTest`).
* `loadK c`: add `c · L` to counter `tKK` by scanning `tRu` `c` times (`Spec.loadK`).
-/

set_option linter.unusedSectionVars false

namespace Savitch.Edge

open TM Machine Machine.NTM

variable {Λ Γ : Type} [Fintype Λ] [Fintype Γ] [DecidableEq Λ] [DecidableEq Γ]
variable {x : List Bool} {B : ℕ}

/-! ### All-ones binary value -/

theorem bval_replicate_true : ∀ L, bval (List.replicate L true) + 1 = 2 ^ L
  | 0 => rfl
  | L + 1 => by
    have ih := bval_replicate_true L
    simp only [List.replicate_succ, bval, Bool.toNat_true, Nat.pow_succ]
    omega

theorem map_bit_replicate (L : ℕ) (b : Bool) :
    (List.replicate L b).map (bsym (Sym.z : Sym Λ Γ) .o) = List.replicate L (bit b) := by
  induction L with
  | zero => rfl
  | succ L ih => simp [List.replicate_succ, ih, bit]

theorem Lay.toHolds_replicate {t : Fin NT} {L : ℕ} (b : Bool) {T : Tapes NT (Sym Λ Γ)}
    (h : Lay t .mk .blank T (List.replicate L (bit b))) :
    Holds t .mk .z .o T (List.replicate L b) := by
  obtain ⟨h0, hseg, hend, hhd⟩ := h
  rw [List.length_replicate] at hseg hend
  refine ⟨h0, ?_, ?_, ?_, ?_, hhd⟩
  · rw [List.length_replicate, map_bit_replicate]; exact hseg
  · rw [List.length_replicate, hend]; exact fun e => by cases e
  · rw [List.length_replicate, hend]; exact fun e => by cases e
  · rw [List.length_replicate, hend]; exact fun e => by cases e

/-! ### Counter-free input-head rewind -/

def resetIn : Code NT (Sym Λ Γ) :=
  [Instr.moveIn .left] ++ whileDo (.input (fun i => i.isSome)) [Instr.moveIn .left]

theorem resetIn_aux : ∀ (m : ℕ) (T : Tapes NT (Sym Λ Γ)),
    T.ih = m → m ≤ x.length → T.Within B →
    Loop (.input (fun i => i.isSome)) [Instr.moveIn .left] x B T { T with ih := 0 }
  | 0, T, hih, _, hT => by
    have heq : { T with ih := 0 } = T := by ext <;> simp [hih]
    rw [heq]
    exact .stop (by simp [Cond.eval, hih, inputSym]) hT
  | m + 1, T, hih, hm, hT => by
    have hsome : (inputSym x T.ih).isSome = true := by
      rw [Option.isSome_iff_ne_none, Ne, inputSym_eq_none]
      omega
    have hbody : Spec [Instr.moveIn (Γ := Sym Λ Γ) .left] x B T (T.moveInput x.length .left) :=
      Spec.moveIn hT
    have hloop := resetIn_aux m (T.moveInput x.length .left)
      (by simp [Tapes.moveInput, Machine.moveIn, hih]) (by omega) hT
    exact .iter (by simp [Cond.eval, hsome]) hT hbody hloop

theorem Spec.resetIn {T : Tapes NT (Sym Λ Γ)} (hih : T.ih ≤ x.length + 1) (hT : T.Within B) :
    Spec (Edge.resetIn (Λ := Λ) (Γ := Γ)) x B T { T with ih := 0 } := by
  have s1 : Spec [Instr.moveIn (Γ := Sym Λ Γ) .left] x B T (T.moveInput x.length .left) :=
    Spec.moveIn hT
  have hl := resetIn_aux (x := x) (T.ih - 1) (T.moveInput x.length .left)
    (by simp [Tapes.moveInput, Machine.moveIn]) (by omega) hT
  exact s1.seq (Spec.whileDo hl)

/-! ### Stepping the input head `c` times -/

def stepInBody : Code NT (Sym Λ Γ) :=
  TM.decrH tCU .mk .z .o ++ [Instr.moveIn .right] ++ TM.isZeroH tCU tF .mk .z .o .yes .no

def stepIn : Code NT (Sym Λ Γ) :=
  TM.isZeroH tCU tF .mk .z .o .yes .no ++
    whileDo (.tape tF (fun g => decide (g = .no))) stepInBody

theorem stepIn_aux :
    ∀ (c : ℕ) (lc : List Bool) (T : Tapes NT (Sym Λ Γ)),
      bval lc = c → Holds tCU .mk .z .o T lc →
      T.read tF = (if c = 0 then .yes else .no) → T.ih ≤ x.length + 1 →
      T.Within B → lc.length + 2 ≤ B →
      ∃ T' lc', Loop (.tape tF (fun g => decide (g = (Sym.no : Sym Λ Γ)))) stepInBody x B T T' ∧
        Holds tCU .mk .z .o T' lc' ∧ lc'.length = lc.length ∧
        T'.ih = min (T.ih + c) (x.length + 1) ∧
        T.Agree (fun i => i = tCU ∨ i = tF) T' ∧ T'.Within B
  | 0, lc, T, hc, hC, hF, hih, hT, _ => by
    refine ⟨T, lc, .stop (by simp [Cond.eval, hF]) hT, hC, rfl, by omega,
      Tapes.Agree.refl _ T, hT⟩
  | c + 1, lc, T, hc, hC, hF, hih, hT, hBc => by
    have hzo : (Sym.z : Sym Λ Γ) ≠ .o := fun h => by cases h
    have hmz : (Sym.mk : Sym Λ Γ) ≠ .z := fun h => by cases h
    have hmo : (Sym.mk : Sym Λ Γ) ≠ .o := fun h => by cases h
    obtain ⟨T₁, s1, hC₁, hfr₁, hW₁⟩ := Spec.decrH (x := x) hzo hmz hmo hC hT hBc
    have hval₁ : bval (bdec lc) = c := by rw [bval_bdec lc (by omega), hc]; rfl
    have s2 : Spec [Instr.moveIn (Γ := Sym Λ Γ) .right] x B T₁ (T₁.moveInput x.length .right) :=
      Spec.moveIn hW₁
    set T₂ := T₁.moveInput x.length .right
    have hC₂ : Holds tCU .mk .z .o T₂ (bdec lc) := hC₁.congr rfl rfl
    obtain ⟨T₃, s3, ⟨q1, q2, q3, q4, q5, q6, q7⟩, hW₃⟩ :=
      Spec.isZeroH (x := x) (t := tCU) (f := tF) (yes := .yes) (no := .no) (by decide) hzo hmz hmo
        hC₂ hW₁ (by rw [bdec_length]; exact hBc)
    have hC₃ : Holds tCU .mk .z .o T₃ (bdec lc) := hC₂.congr q3 q4
    have hF₃ : T₃.read tF = (if c = 0 then .yes else .no) := by
      rw [Tapes.read, q5, q1, hval₁]
    have hih₃ : T₃.ih = min (T.ih + 1) (x.length + 1) := by
      rw [q7]; simp [T₂, Tapes.moveInput, Machine.moveIn, hfr₁.1]
    obtain ⟨T', lc', hloop, hC', hlenc', hih', hag', hW'⟩ :=
      stepIn_aux c (bdec lc) T₃ hval₁ hC₃ hF₃ (by omega) hW₃ (by rw [bdec_length]; exact hBc)
    have ag13 : T.Agree (fun i => i = tCU ∨ i = tF) T₃ := by
      intro i hi
      have h1 : i ≠ tCU := fun e => hi (Or.inl e)
      exact ⟨(q6 i hi).1.trans (hfr₁.2 i h1).1, (q6 i hi).2.trans (hfr₁.2 i h1).2⟩
    refine ⟨T', lc', .iter (by simp [Cond.eval, hF]) hT ((s1.seq s2).seq s3) hloop,
      hC', by rw [hlenc', bdec_length], by rw [hih', hih₃]; omega,
      ag13.trans hag', hW'⟩

theorem Spec.stepIn {lc : List Bool} {T : Tapes NT (Sym Λ Γ)}
    (hC : Holds tCU .mk .z .o T lc) (hih : T.ih ≤ x.length + 1)
    (hT : T.Within B) (hBc : lc.length + 2 ≤ B) :
    ∃ T' lc', Spec (Edge.stepIn (Λ := Λ) (Γ := Γ)) x B T T' ∧
      Holds tCU .mk .z .o T' lc' ∧ lc'.length = lc.length ∧
      T'.ih = min (T.ih + bval lc) (x.length + 1) ∧
      T.Agree (fun i => i = tCU ∨ i = tF) T' ∧ T'.Within B := by
  have hzo : (Sym.z : Sym Λ Γ) ≠ .o := fun h => by cases h
  have hmz : (Sym.mk : Sym Λ Γ) ≠ .z := fun h => by cases h
  have hmo : (Sym.mk : Sym Λ Γ) ≠ .o := fun h => by cases h
  obtain ⟨T₀, s0, ⟨q1, q2, q3, q4, q5, q6, q7⟩, hW₀⟩ :=
    Spec.isZeroH (x := x) (t := tCU) (f := tF) (yes := .yes) (no := .no) (by decide) hzo hmz hmo
      hC hT hBc
  have hC₀ : Holds tCU .mk .z .o T₀ lc := hC.congr q3 q4
  obtain ⟨T', lc', hloop, hC', hlenc', hih', hag', hW'⟩ :=
    stepIn_aux (bval lc) lc T₀ rfl hC₀ (by rw [Tapes.read, q5, q1]) (by rw [q7]; exact hih)
      hW₀ hBc
  refine ⟨T', lc', s0.seq (Spec.whileDo hloop), hC', hlenc', by rw [hih', q7],
    q6.trans hag', hW'⟩

/-! ### Testing whether `x.length + 1 < 2 ^ L` -/

noncomputable def fitTest : Code NT (Sym Λ Γ) :=
  makeBlock tCU .o ++ stepIn ++
    ifElse (.input (fun i => i.isNone)) [Instr.write tF₂ .yes] [Instr.write tF₂ .no] ++
    resetIn

theorem Spec.fitTest {lr : List (Sym Λ Γ)} (hrec : ∀ g ∈ lr, isRec g = true) (hL : 0 < lr.length)
    {T : Tapes NT (Sym Λ Γ)} (hRu : Lay tRu .mk .blank T lr)
    (hCU : T.tp tCU 0 = .mk ∧ T.hd tCU = 1) (hih : T.ih = 0)
    (hT : T.Within B) (hB : lr.length + 2 ≤ B) :
    ∃ T', Spec (Edge.fitTest (Λ := Λ) (Γ := Γ)) x B T T' ∧
      T'.read tF₂ = (if x.length + 1 < 2 ^ lr.length then .yes else .no) ∧
      Lay tRu .mk .blank T' lr ∧ T'.ih = 0 ∧
      T'.tp tCU 0 = .mk ∧ T'.hd tCU = 1 ∧
      T.Agree (fun i => i = tCU ∨ i = tF ∨ i = tF₂) T' ∧ T'.Within B := by
  set L := lr.length
  obtain ⟨T₁, s1, hL₁, hRu₁, ag1, ih1, hW₁⟩ :=
    Spec.makeBlock (x := x) (t := tCU) (g := .o) (by decide) (fun h => by cases h) hRu hrec
      hCU.1 hCU.2 hT hB
  have hC₁ : Holds tCU .mk .z .o T₁ (List.replicate L true) := Lay.toHolds_replicate true hL₁
  obtain ⟨T₂, lc', s2, hC₂, hlc', hih₂, ag2, hW₂⟩ :=
    Spec.stepIn (x := x) hC₁ (by rw [ih1, hih]; omega) hW₁
      (by rw [List.length_replicate]; exact hB)
  have hval : bval (List.replicate L true) = 2 ^ L - 1 := by
    have := bval_replicate_true L; omega
  have hpos : 0 < 2 ^ L - 1 := by
    have : 2 ^ 1 ≤ 2 ^ L := Nat.pow_le_pow_right (by decide) hL
    omega
  have hih₂' : T₂.ih = min (2 ^ L - 1) (x.length + 1) := by
    rw [hih₂, ih1, hih, Nat.zero_add, hval]
  have hnone_iff : (inputSym x T₂.ih).isNone = true ↔ x.length + 1 < 2 ^ L := by
    rw [Option.isNone_iff_eq_none, inputSym_eq_none, hih₂']
    have := bval_replicate_true L
    omega
  have ag12 : T.Agree (fun i => i = tCU ∨ i = tF) T₂ :=
    (ag1.mono (fun _ h => Or.inl h)).trans ag2
  set g_res : Sym Λ Γ := if x.length + 1 < 2 ^ L then .yes else .no
  have s3 : Spec (ifElse (.input (fun i => i.isNone))
      [Instr.write tF₂ (Sym.yes : Sym Λ Γ)] [Instr.write tF₂ .no]) x B T₂ (T₂.write tF₂ g_res) := by
    by_cases hfit : x.length + 1 < 2 ^ L
    · have hc : Cond.eval x T₂ (.input (fun i => i.isNone)) = true := by
        simp [Cond.eval, hnone_iff.2 hfit]
      simp only [g_res, hfit, ↓reduceIte]
      exact Spec.ifElse_true hc hW₂ (Spec.write hW₂)
    · have hc : Cond.eval x T₂ (.input (fun i => i.isNone)) = false := by
        simp only [Cond.eval, Bool.eq_false_iff]; exact fun h => hfit (hnone_iff.1 h)
      simp only [g_res, hfit, ↓reduceIte]
      exact Spec.ifElse_false hc hW₂ (Spec.write hW₂)
  set T₃ := T₂.write tF₂ g_res
  have hW₃ : T₃.Within B := Tapes.within_write hW₂
  have s4 := Spec.resetIn (x := x) (T := T₃) (by show T₂.ih ≤ x.length + 1; rw [hih₂']; omega) hW₃
  set T₄ : Tapes NT (Sym Λ Γ) := { T₃ with ih := 0 }
  have ag3 : T₂.Agree (fun i => i = tF₂) T₄ := fun i hi =>
    ⟨by simp [T₄, T₃, Tapes.write, hi], rfl⟩
  have agAll : T.Agree (fun i => i = tCU ∨ i = tF ∨ i = tF₂) T₄ :=
    (ag12.mono (fun i h => h.elim Or.inl (fun h => Or.inr (Or.inl h)))).trans
      (ag3.mono (fun _ h => Or.inr (Or.inr h)))
  refine ⟨T₄, ((s1.seq s2).seq s3).seq s4, ?_, ?_, rfl, ?_, ?_, agAll, hW₃⟩
  · simp [T₄, T₃, Tapes.read, Tapes.write_tp_self, g_res]
  · exact agree_lay agAll (by decide) hRu
  · rw [(ag3 tCU (by decide)).1]; exact hC₂.1
  · rw [(ag3 tCU (by decide)).2]; exact hC₂.2.2.2.2.2

/-! ### Loading `c · L` into counter `tKK` -/

noncomputable def addRuBody : Code NT (Sym Λ Γ) :=
  [Instr.move tRu .right] ++ TM.incrH tKK .mk .z .o

noncomputable def addRu : Code NT (Sym Λ Γ) :=
  whileDo (.tape tRu isRec) addRuBody ++ TM.home tRu .mk

theorem addRu_aux :
    ∀ (m : ℕ) (l : List Bool) (T : Tapes NT (Sym Λ Γ)),
      (∀ j < m, isRec (T.tp tRu (T.hd tRu + j)) = true) →
      isRec (T.tp tRu (T.hd tRu + m)) = false →
      Holds tKK .mk .z .o T l → bval l + m < 2 ^ l.length →
      T.Within B → T.hd tRu + m < B → l.length + 2 ≤ B →
      ∃ T' l', Loop (.tape tRu isRec) addRuBody x B T T' ∧
        Holds tKK .mk .z .o T' l' ∧ l'.length = l.length ∧ bval l' = bval l + m ∧
        T'.tp tRu = T.tp tRu ∧ T'.hd tRu = T.hd tRu + m ∧
        T.Agree (fun i => i = tRu ∨ i = tKK) T' ∧ T'.ih = T.ih ∧ T'.Within B
  | 0, l, T, _, hq, hK, _, hT, _, _ => by
    exact ⟨T, l, .stop (by simpa [Cond.eval, Tapes.read] using hq) hT, hK, rfl, by simp,
      rfl, by simp, Tapes.Agree.refl _ T, rfl, hT⟩
  | m + 1, l, T, hp, hq, hK, hfit, hT, hBr, hBk => by
    have hzo : (Sym.z : Sym Λ Γ) ≠ .o := fun h => by cases h
    have hmz : (Sym.mk : Sym Λ Γ) ≠ .z := fun h => by cases h
    have hmo : (Sym.mk : Sym Λ Γ) ≠ .o := fun h => by cases h
    have s1 : Spec [Instr.move tRu .right] x B T (T.setHead tRu (T.hd tRu + 1)) :=
      Spec.moveRight hT (by omega)
    set T₁ := T.setHead tRu (T.hd tRu + 1)
    have hW₁ : T₁.Within B := Tapes.within_setHead hT (by omega)
    have hK₁ : Holds tKK .mk .z .o T₁ l :=
      hK.congr rfl (Tapes.setHead_hd_ne _ _ (by decide) _)
    obtain ⟨T₂, s2, hK₂, hfr₂, hW₂⟩ := Spec.incrH (x := x) hzo hmz hmo hK₁ hW₁ hBk
    have hR₂tp : T₂.tp tRu = T.tp tRu := (hfr₂.2 tRu (by decide)).1
    have hR₂hd : T₂.hd tRu = T.hd tRu + 1 := (hfr₂.2 tRu (by decide)).2
    have hval₂ : bval (binc l) = bval l + 1 := bval_binc l (by omega)
    obtain ⟨T', l', hloop, hK', hlen', hval', hRtp', hRhd', hag', hih', hW'⟩ :=
      addRu_aux m (binc l) T₂
        (fun j hj => by
          rw [hR₂tp, hR₂hd, show T.hd tRu + 1 + j = T.hd tRu + (j + 1) by omega]
          exact hp (j + 1) (by omega))
        (by rw [hR₂tp, hR₂hd, show T.hd tRu + 1 + m = T.hd tRu + (m + 1) by omega]; exact hq)
        hK₂ (by rw [binc_length, hval₂]; omega) hW₂ (by rw [hR₂hd]; omega)
        (by rw [binc_length]; exact hBk)
    have ag12 : T.Agree (fun i => i = tRu ∨ i = tKK) T₂ := fun i hi => by
      have h1 : i ≠ tRu := fun e => hi (Or.inl e)
      have h2 : i ≠ tKK := fun e => hi (Or.inr e)
      exact ⟨(hfr₂.2 i h2).1, by rw [(hfr₂.2 i h2).2]; exact Tapes.setHead_hd_ne _ _ h1 _⟩
    refine ⟨T', l', .iter (by simpa [Cond.eval, Tapes.read] using hp 0 (by omega)) hT
        (s1.seq s2) hloop, hK', by rw [hlen', binc_length], by rw [hval', hval₂]; omega,
      by rw [hRtp', hR₂tp], by rw [hRhd', hR₂hd]; omega, ag12.trans hag',
      by rw [hih', hfr₂.1]; rfl, hW'⟩

theorem Spec.addRu {lr : List (Sym Λ Γ)} (hrec : ∀ g ∈ lr, isRec g = true)
    {l : List Bool} {T : Tapes NT (Sym Λ Γ)} (hRu : Lay tRu .mk .blank T lr)
    (hK : Holds tKK .mk .z .o T l) (hfit : bval l + lr.length < 2 ^ l.length)
    (hT : T.Within B) (hBr : lr.length + 2 ≤ B) (hBk : l.length + 2 ≤ B) :
    ∃ T' l', Spec (Edge.addRu (Λ := Λ) (Γ := Γ)) x B T T' ∧
      Holds tKK .mk .z .o T' l' ∧ l'.length = l.length ∧ bval l' = bval l + lr.length ∧
      Lay tRu .mk .blank T' lr ∧ T.Agree (fun i => i = tKK) T' ∧ T'.ih = T.ih ∧ T'.Within B := by
  have hmb : (Sym.mk : Sym Λ Γ) ≠ .blank := fun h => by cases h
  obtain ⟨T₁, l', hloop, hK₁, hlen', hval', hRtp₁, hRhd₁, hag₁, hih₁, hW₁⟩ :=
    addRu_aux (x := x) lr.length l T (fun j hj => hrec _ (hRu.cell hj))
      (by rw [hRu.endCell]; rfl) hK hfit hT (by rw [hRu.2.2.2]; omega) hBk
  have hh := Spec.home (x := x) tRu .mk (T := T₁) (by rw [hRtp₁]; exact hRu.1)
    (by rw [hRtp₁, hRhd₁, hRu.2.2.2]
        exact home_ok hmb (fun g hg => by
          have := hrec g hg; intro h; subst h; simp [isRec] at this) hRu.2.1 hRu.2.2.1 (by omega))
    hW₁ (by omega)
  set T₂ := T₁.setHead tRu 1
  refine ⟨T₂, l', (Spec.whileDo hloop).seq hh,
    hK₁.congr rfl (Tapes.setHead_hd_ne _ _ (by decide) _), hlen', hval',
    hRu.congr (by simp [T₂, hRtp₁]) (by simp [T₂, hRu.2.2.2]), ?_, hih₁,
    Tapes.within_setHead hW₁ (by omega)⟩
  intro i hi
  by_cases hiR : i = tRu
  · subst hiR; exact ⟨hRtp₁, by simp [T₂, hRu.2.2.2]⟩
  · have g := hag₁ i (fun h => h.elim hiR hi)
    exact ⟨g.1, by rw [Tapes.setHead_hd_ne _ _ hiR]; exact g.2⟩

noncomputable def loadK : ℕ → Code NT (Sym Λ Γ)
  | 0 => []
  | c + 1 => addRu ++ loadK c

theorem Spec.loadK {lr : List (Sym Λ Γ)} (hrec : ∀ g ∈ lr, isRec g = true) :
    ∀ (c : ℕ) {l : List Bool} {T : Tapes NT (Sym Λ Γ)},
      Lay tRu .mk .blank T lr → Holds tKK .mk .z .o T l →
      bval l + c * lr.length < 2 ^ l.length →
      T.Within B → lr.length + 2 ≤ B → l.length + 2 ≤ B →
      ∃ T' l', Spec (Edge.loadK (Λ := Λ) (Γ := Γ) c) x B T T' ∧
        Holds tKK .mk .z .o T' l' ∧ l'.length = l.length ∧
        bval l' = bval l + c * lr.length ∧
        Lay tRu .mk .blank T' lr ∧ T.Agree (fun i => i = tKK) T' ∧ T'.ih = T.ih ∧ T'.Within B
  | 0, l, T, hRu, hK, _, hT, _, _ =>
    ⟨T, l, Spec.nil hT, hK, rfl, by simp, hRu, Tapes.Agree.refl _ T, rfl, hT⟩
  | c + 1, l, T, hRu, hK, hfit, hT, hBr, hBk => by
    have hmul : (c + 1) * lr.length = lr.length + c * lr.length := by ring
    obtain ⟨T₁, l₁, s1, hK₁, hlen₁, hval₁, hRu₁, ag1, ih1, hW₁⟩ :=
      Spec.addRu (x := x) hrec hRu hK (by omega) hT hBr hBk
    obtain ⟨T₂, l₂, s2, hK₂, hlen₂, hval₂, hRu₂, ag2, ih2, hW₂⟩ :=
      Spec.loadK hrec c hRu₁ hK₁ (by rw [hlen₁, hval₁]; omega) hW₁ hBr (by rw [hlen₁]; exact hBk)
    refine ⟨T₂, l₂, s1.seq s2, hK₂, by rw [hlen₂, hlen₁], by rw [hval₂, hval₁, hmul]; omega,
      hRu₂, ag1.trans ag2, by rw [ih2, ih1], hW₂⟩

end Savitch.Edge
