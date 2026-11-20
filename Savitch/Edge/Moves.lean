import Savitch.Edge.Mark

/-!
# Per-move pieces of the edge test

Phase 4b-4 of the Savitch formalization (see `PLAN.md`).

* `movedPos i di P P₂ F`: with `P` holding the input-head position `ih` (and `i` the
  input symbol there, known from the case split), put `moveIn n ih di` into counter
  `P₂`, without moving the input head (`Spec.movedPos`).
* `markMove dw A₁ A₂ G`: with `A₁` marking the work head `w`, mark `moveWork w dw` on
  `A₂`, and write `yes` under head `G` iff it is still inside the block
  (`Spec.markMove`).
-/

set_option linter.unusedSectionVars false

namespace Savitch.Edge

open TM Machine Machine.NTM

variable {Λ Γ : Type} [Fintype Λ] [Fintype Γ] [DecidableEq Λ] [DecidableEq Γ]
variable {k : ℕ} {x : List Bool} {B : ℕ}

local notation "isB" => TM.isBit (Sym.z : Sym Λ Γ) Sym.o

theorem bit_ne_mk (b : Bool) : (bit b : Sym Λ Γ) ≠ .mk := by cases b <;> simp [bit, bsym]

theorem isBit_bit (b : Bool) : isB (bit b) = true := by cases b <;> simp [TM.isBit, bit, bsym]

/-- The tail of `movedPos` for a right move: `+1` unless at the right end marker. -/
noncomputable def adjRight (i : Option Bool) (P P₂ F : Fin k) : Code k (Sym Λ Γ) :=
  match i with
  | none => TM.isZeroH P F .mk .z .o .yes .no ++
      ifElse (.tape F (fun g => decide (g = .yes))) (TM.incrH P₂ .mk .z .o) []
  | some _ => TM.incrH P₂ .mk .z .o

noncomputable def adjust (i : Option Bool) (di : Dir) (P P₂ F : Fin k) : Code k (Sym Λ Γ) :=
  match di with
  | .stay => []
  | .right => adjRight i P P₂ F
  | .left => TM.isZeroH P F .mk .z .o .yes .no ++
      ifElse (.tape F (fun g => decide (g = .yes))) [] (TM.decrH P₂ .mk .z .o)

/-- Put the moved input position into counter `P₂`. -/
noncomputable def movedPos (i : Option Bool) (di : Dir) (P P₂ F : Fin k) : Code k (Sym Λ Γ) :=
  copyPass P P₂ .mk isB id ++ adjust i di P P₂ F

theorem Spec.movedPos {P P₂ F : Fin k} (hPP : P ≠ P₂) (hPF : P ≠ F) (hP₂F : P₂ ≠ F)
    (di : Dir) {lp l₂ : List Bool} {T : Tapes k (Sym Λ Γ)}
    (hP : InPos P .mk .z .o x T lp) (hP₂ : Holds P₂ .mk .z .o T l₂) (hl₂ : l₂.length = lp.length)
    (hT : T.Within B) (hB : lp.length + 2 ≤ B) :
    ∃ T' l₂', Spec (Edge.movedPos (inputSym x T.ih) di P P₂ F) x B T T' ∧
      Holds P₂ .mk .z .o T' l₂' ∧ l₂'.length = lp.length ∧
      bval l₂' = moveIn x.length T.ih di ∧ T.Agree (fun j => j = P₂ ∨ j = F) T' ∧
      T'.hd F = T.hd F ∧ T'.ih = T.ih ∧ T'.Within B := by
  have hzo : (Sym.z : Sym Λ Γ) ≠ .o := fun h => by cases h
  have hmz : (Sym.mk : Sym Λ Γ) ≠ .z := fun h => by cases h
  have hmo : (Sym.mk : Sym Λ Γ) ≠ .o := fun h => by cases h
  have hyn : (Sym.yes : Sym Λ Γ) ≠ .no := fun h => by cases h
  obtain ⟨hH, hval, hle, hfit⟩ := hP
  have hbl : (lp.map (bit (Λ := Λ) (Γ := Γ))).length = lp.length := List.length_map _
  -- copy `P` to `P₂`
  obtain ⟨T₁, s1, hPw₁, hP₂w₁, hPtp₁, hP₂end₁, ag1, ih1, hW₁⟩ :=
    Spec.copyPassW (x := x) (p := isB) (h := id) hPP hH.toW
      (by rw [hbl]; simp [TM.isBit, hH.2.2.1, hH.2.2.2.1]) hP₂.toW
      (by rw [List.length_map, hbl, hl₂]) (fun g hg => by
        obtain ⟨b, _, rfl⟩ := List.mem_map.1 hg; exact isBit_bit b)
      (fun g hg => by obtain ⟨b, _, rfl⟩ := List.mem_map.1 hg; exact bit_ne_mk b)
      (fun g hg => by obtain ⟨b, _, rfl⟩ := List.mem_map.1 hg; exact bit_ne_mk b) hT
      (by rw [hbl]; exact hB)
  rw [List.map_id] at hP₂w₁
  rw [hbl] at hP₂end₁
  have hH₂₁ : Holds P₂ .mk .z .o T₁ lp := Holds.ofW hP₂w₁
    (by rw [hP₂end₁, ← hl₂]; exact hP₂.2.2.1) (by rw [hP₂end₁, ← hl₂]; exact hP₂.2.2.2.1)
  have hH₁ : Holds P .mk .z .o T₁ lp := hH.congr hPtp₁ (ag1 P hPP).2
  have hF₁ : T₁.hd F = T.hd F := (ag1 F (Ne.symm hP₂F)).2
  -- the adjustment
  have hfit' : x.length + 1 < 2 ^ lp.length := hfit
  cases di with
  | stay =>
    exact ⟨T₁, lp, s1.seq (Spec.nil hW₁), hH₂₁, rfl, by rw [hval]; rfl,
      ag1.mono (fun _ h => Or.inl h), hF₁, ih1, hW₁⟩
  | left =>
    obtain ⟨T₂, s2, ⟨q1, q2, q3, q4, q5, q6, q7⟩, hW₂⟩ :=
      Spec.isZeroH (x := x) (yes := .yes) (no := .no) (f := F) hPF hzo hmz hmo hH₁ hW₁ hB
    have hH₂₂ : Holds P₂ .mk .z .o T₂ lp :=
      hH₂₁.congr (q6 P₂ (fun h => h.elim hPP.symm hP₂F)).1 (q6 P₂ (fun h => h.elim hPP.symm hP₂F)).2
    have ag2 : T.Agree (fun j => j = P₂ ∨ j = F) T₂ := fun j hj => by
      have g1 := ag1 j (fun h => hj (Or.inl h))
      by_cases hjP : j = P
      · subst hjP; exact ⟨q3.trans g1.1, q4.trans g1.2⟩
      · have g2 := q6 j (fun h => h.elim hjP (fun h' => hj (Or.inr h')))
        exact ⟨g2.1.trans g1.1, g2.2.trans g1.2⟩
    by_cases h0 : T.ih = 0
    · have hflag : T₂.read F = .yes := by
        rw [Tapes.read, q5, q1, ite_pos' (by rw [hval, h0])]
      refine ⟨T₂, lp, s1.seq (s2.seq (Spec.ifElse_true (by simp [Cond.eval, hflag]) hW₂
        (Spec.nil hW₂))), hH₂₂, rfl, by rw [hval, h0]; rfl, ag2, by rw [q5, hF₁],
        by rw [q7, ih1], hW₂⟩
    · have hflag : T₂.read F = .no := by
        rw [Tapes.read, q5, q1, ite_neg' (by rw [hval]; exact h0)]
      obtain ⟨T₃, s3, hH₂₃, hfr₃, hW₃⟩ := Spec.decrH (x := x) hzo hmz hmo hH₂₂ hW₂ hB
      refine ⟨T₃, bdec lp, s1.seq (s2.seq (Spec.ifElse_false (by simp [Cond.eval, hflag])
        hW₂ s3)), hH₂₃, bdec_length lp, ?_, ?_, ?_, by rw [hfr₃.1, q7, ih1], hW₃⟩
      · rw [bval_bdec lp (by rw [hval]; omega), hval]; rfl
      · exact ag2.trans (hfr₃.toAgree (Or.inl rfl))
      · rw [(hfr₃.2 F (Ne.symm hP₂F)).2, q5, hF₁]
  | right =>
    have hincr : ∀ T₀ : Tapes k (Sym Λ Γ), Holds P₂ .mk .z .o T₀ lp → T₀.Within B →
        bval lp + 1 < 2 ^ lp.length →
        ∃ T', Spec (TM.incrH P₂ .mk .z .o) x B T₀ T' ∧ Holds P₂ .mk .z .o T' (binc lp) ∧
          bval (binc lp) = bval lp + 1 ∧ T₀.Frame P₂ T' ∧ T'.Within B := by
      intro T₀ hH₀ hW₀ hroom
      obtain ⟨T', s, hH', hfr, hW'⟩ := Spec.incrH (x := x) hzo hmz hmo hH₀ hW₀ hB
      exact ⟨T', s, hH', bval_binc lp hroom, hfr, hW'⟩
    cases hi : inputSym x T.ih with
    | some b =>
      have hpos : T.ih ≤ x.length := by
        have : inputSym x T.ih ≠ none := by rw [hi]; simp
        rw [ne_eq, inputSym_eq_none] at this; omega
      obtain ⟨T₂, s2, hH₂₂, hv, hfr, hW₂⟩ := hincr T₁ hH₂₁ hW₁ (by rw [hval]; omega)
      refine ⟨T₂, binc lp, s1.seq s2, hH₂₂, binc_length lp, ?_, ?_, ?_, ?_, hW₂⟩
      · rw [hv, hval]; simp [moveIn]; omega
      · exact (ag1.mono (fun _ h => Or.inl h)).trans (hfr.toAgree (Or.inl rfl))
      · rw [(hfr.2 F (Ne.symm hP₂F)).2, hF₁]
      · rw [hfr.1, ih1]
    | none =>
      obtain ⟨T₂, s2, ⟨q1, q2, q3, q4, q5, q6, q7⟩, hW₂⟩ :=
        Spec.isZeroH (x := x) (yes := .yes) (no := .no) (f := F) hPF hzo hmz hmo hH₁ hW₁ hB
      have hH₂₂ : Holds P₂ .mk .z .o T₂ lp :=
        hH₂₁.congr (q6 P₂ (fun h => h.elim hPP.symm hP₂F)).1
          (q6 P₂ (fun h => h.elim hPP.symm hP₂F)).2
      have ag2 : T.Agree (fun j => j = P₂ ∨ j = F) T₂ := fun j hj => by
        have g1 := ag1 j (fun h => hj (Or.inl h))
        by_cases hjP : j = P
        · subst hjP; exact ⟨q3.trans g1.1, q4.trans g1.2⟩
        · have g2 := q6 j (fun h => h.elim hjP (fun h' => hj (Or.inr h')))
          exact ⟨g2.1.trans g1.1, g2.2.trans g1.2⟩
      rcases (inputSym_eq_none x T.ih).1 hi with h0 | hgt
      · have hflag : T₂.read F = .yes := by
          rw [Tapes.read, q5, q1, ite_pos' (by rw [hval, h0])]
        obtain ⟨T₃, s3, hH₂₃, hv, hfr, hW₃⟩ := hincr T₂ hH₂₂ hW₂ (by rw [hval]; omega)
        refine ⟨T₃, binc lp, s1.seq (s2.seq (Spec.ifElse_true (by simp [Cond.eval, hflag]) hW₂
          s3)), hH₂₃, binc_length lp, ?_, ag2.trans (hfr.toAgree (Or.inl rfl)), ?_,
          by rw [hfr.1, q7, ih1], hW₃⟩
        · rw [hv, hval, h0]; simp [moveIn]
        · rw [(hfr.2 F (Ne.symm hP₂F)).2, q5, hF₁]
      · have hih : T.ih = x.length + 1 := by omega
        have hflag : T₂.read F = .no := by
          rw [Tapes.read, q5, q1, ite_neg' (by rw [hval]; omega)]
        refine ⟨T₂, lp, s1.seq (s2.seq (Spec.ifElse_false (by simp [Cond.eval, hflag]) hW₂
          (Spec.nil hW₂))), hH₂₂, rfl, ?_, ag2, by rw [q5, hF₁], by rw [q7, ih1], hW₂⟩
        rw [hval, hih]; simp [moveIn]

/-! ### The moved work-head mark -/

def isZs : Sym Λ Γ → Bool
  | .z => true
  | _ => false

def isMk : Sym Λ Γ → Bool
  | .mk => true
  | _ => false

noncomputable def moveTail (dw : Dir) (A₂ G : Fin k) : Code k (Sym Λ Γ) :=
  match dw with
  | .stay => [Instr.write A₂ .o] ++ [Instr.write G .yes]
  | .right => [Instr.move A₂ .right] ++
      ifElse (.tape A₂ isB) ([Instr.write A₂ .o] ++ [Instr.write G .yes]) [Instr.write G .no]
  | .left => [Instr.move A₂ .left] ++ ifElse (.tape A₂ isMk) [Instr.move A₂ .right] [] ++
      ([Instr.write A₂ .o] ++ [Instr.write G .yes])

/-- Mark the moved work head on `A₂`, with an in-range flag under head `G`. -/
noncomputable def markMove (dw : Dir) (A₁ A₂ G : Fin k) : Code k (Sym Λ Γ) :=
  copyPass A₁ A₂ .mk isB (fun _ => .z) ++ zipWhile A₁ A₂ isZs (fun a _ => a) ++
    moveTail dw A₂ G ++ TM.home A₁ .mk ++ TM.home A₂ .mk

theorem Spec.markMove {A₁ A₂ G : Fin k} (h12 : A₁ ≠ A₂) (h1G : A₁ ≠ G) (h2G : A₂ ≠ G)
    (dw : Dir) {L : ℕ} (w : Fin L) {l₂ : List (Sym Λ Γ)} {T : Tapes k (Sym Λ Γ)}
    (hA₁ : Lay A₁ .mk .blank T ((List.ofFn fun j : Fin L => decide (j = w)).map bit))
    (hA₂ : LayW A₂ .mk T l₂) (hl₂ : l₂.length = L)
    (hA₂z : T.tp A₂ (L + 1) ≠ .z) (hA₂o : T.tp A₂ (L + 1) ≠ .o)
    (hT : T.Within B) (hB : L + 2 ≤ B) :
    ∃ T', Spec (Edge.markMove dw A₁ A₂ G) x B T T' ∧
      Lay A₁ .mk .blank T' ((List.ofFn fun j : Fin L => decide (j = w)).map bit) ∧
      T'.tp G (T.hd G) = (if moveWork w.val dw < L then .yes else .no) ∧
      (∀ hlt : moveWork w.val dw < L, LayW A₂ .mk T'
        ((List.ofFn fun j : Fin L => decide (j = ⟨moveWork w.val dw, hlt⟩)).map bit)) ∧
      (∃ l : List Bool, LayW A₂ .mk T' (l.map bit) ∧ l.length = L) ∧
      T'.tp A₂ (L + 1) = T.tp A₂ (L + 1) ∧ T'.hd A₂ = 1 ∧
      T.Agree (fun i => i = A₂ ∨ i = G) T' ∧ T'.hd G = T.hd G ∧ T'.ih = T.ih ∧
      T'.Within B := by
  have hmb : (Sym.mk : Sym Λ Γ) ≠ .blank := fun h => by cases h
  set la := (List.ofFn fun j : Fin L => decide (j = w)).map (bit (Λ := Λ) (Γ := Γ)) with hla
  have hlal : la.length = L := by simp [la]
  have hAcell : ∀ j : Fin L, T.tp A₁ (1 + j) = bit (decide (j = w)) := by
    have h := hA₁.2.1
    rw [hlal, seg_ofFn, hla, List.map_ofFn] at h
    intro j; exact congrFun (List.ofFn_injective h) j
  have hAend : T.tp A₁ (L + 1) = .blank := by have := hA₁.2.2.1; rwa [hlal] at this
  -- 1. clear `A₂`
  obtain ⟨T₁, s1, hA₁w₁, hA₂w₁, hA₁tp₁, hA₂end₁, ag1, ih1, hW₁⟩ :=
    Spec.copyPassW (x := x) (p := isB) (h := fun _ => (Sym.z : Sym Λ Γ)) h12 (hA₁.toW hmb)
      (by rw [hlal, hAend]; rfl) hA₂ (by rw [hl₂, hlal])
      (fun g hg => by obtain ⟨b, _, rfl⟩ := List.mem_map.1 hg; exact isBit_bit b)
      (fun g hg => by obtain ⟨b, _, rfl⟩ := List.mem_map.1 hg; exact bit_ne_mk b)
      (fun _ _ h => by cases h) hT (by rw [hlal]; exact hB)
  rw [hlal] at hA₂end₁
  have hZcell : ∀ j : Fin L, T₁.tp A₂ (1 + j) = .z := by
    have h := hA₂w₁.2.1
    rw [List.length_map, hlal, seg_ofFn, hla, List.map_map, List.map_ofFn] at h
    intro j; exact congrFun (List.ofFn_injective h) j
  have hA₂0 : T₁.tp A₂ 0 = .mk := hA₂w₁.1
  have hA₁hd₁ : T₁.hd A₁ = 1 := hA₁w₁.2.2.2
  have hA₂hd₁ : T₁.hd A₂ = 1 := hA₂w₁.2.2.2
  -- 2. advance both heads to the mark
  have s2 := Spec.zipWhile (x := x) h12 isZs (fun g _ => g) w.val T₁
    (fun j hj => by
      rw [hA₁hd₁, hA₁tp₁, hAcell ⟨j, by omega⟩]
      have : (⟨j, by omega⟩ : Fin L) ≠ w := fun e => by rw [← e] at hj; exact lt_irrefl _ hj
      simp [this, isZs, bit, bsym])
    (by rw [hA₁hd₁, hA₁tp₁, hAcell w]; simp [isZs, bit, bsym])
    hW₁ (by rw [hA₁hd₁]; omega) (by rw [hA₂hd₁]; omega)
  set T₂ := T₁.zipRes A₁ A₂ (fun g _ => g) w.val
  have hT₂A₁ : T₂.tp A₁ = T₁.tp A₁ := zipRes_fst T₁ _
  have hT₂A₂ : T₂.tp A₂ = T₁.tp A₂ := Tapes.zipRes_tp_ne (Ne.symm h12) T₁ _
  have hT₂h1 : T₂.hd A₁ = 1 + w.val := by rw [Tapes.zipRes_hd_a h12, hA₁hd₁]
  have hT₂h2 : T₂.hd A₂ = 1 + w.val := by rw [Tapes.zipRes_hd_b, hA₂hd₁]
  have hT₂G : T₂.hd G = T.hd G := by
    rw [Tapes.zipRes_hd_ne (Ne.symm h1G) (Ne.symm h2G), (ag1 G (Ne.symm h2G)).2]
  have hT₂Gtp : T₂.tp G = T.tp G := by
    rw [Tapes.zipRes_tp_ne (Ne.symm h1G), (ag1 G (Ne.symm h2G)).1]
  have hW₂ : T₂.Within B := s2.target_within
  have hw := w.isLt
  -- 3. move the `A₂` head and write the mark
  set w' := moveWork w.val dw with hw'
  have h3 : ∃ T₃, Spec (moveTail dw A₂ G) x B T₂ T₃ ∧
      T₃.tp A₂ = (if w' < L then Function.update (T₁.tp A₂) (1 + w') .o else T₁.tp A₂) ∧
      T₃.tp G (T.hd G) = (if w' < L then .yes else .no) ∧ T₃.tp A₁ = T₁.tp A₁ ∧
      T₃.hd A₁ = 1 + w.val ∧ T₃.hd A₂ ≤ L + 1 ∧ T₃.hd G = T.hd G ∧
      T₂.Agree (fun i => i = A₂ ∨ i = G) T₃ ∧ T₃.ih = T₂.ih ∧ T₃.Within B := by
    have wr : ∀ (T₀ : Tapes k (Sym Λ Γ)) (pos : ℕ), T₀.Within B → T₀.hd A₂ = pos →
        T₀.tp A₂ = T₁.tp A₂ → T₀.tp G = T.tp G → T₀.hd G = T.hd G →
        Spec ([Instr.write A₂ .o] ++ [Instr.write G .yes]) x B T₀
          ((T₀.write A₂ .o).write G .yes) ∧
        ((T₀.write A₂ .o).write G .yes).tp A₂ = Function.update (T₁.tp A₂) pos .o ∧
        ((T₀.write A₂ .o).write G .yes).tp G (T.hd G) = .yes := by
      intro T₀ pos hW₀ hp hA hG hGh
      refine ⟨(Spec.write hW₀).seq (Spec.write (Tapes.within_write hW₀)), ?_, ?_⟩
      · funext j
        simp [Tapes.write, h2G, Function.update_apply, hp, hA]
      · simp [Tapes.write, Function.update_apply, hGh]
    cases dw with
    | stay =>
      have hlt : w' < L := by simp [w', moveWork]
      obtain ⟨s, e1, e2⟩ := wr T₂ (1 + w') hW₂ (by simp [hT₂h2, w', moveWork]) hT₂A₂
        hT₂Gtp hT₂G
      refine ⟨_, s, by rw [ite_pos' hlt, e1], by rw [ite_pos' hlt, e2], ?_, ?_, ?_, ?_, ?_, rfl,
        Tapes.within_write (Tapes.within_write hW₂)⟩
      · simp [Tapes.write, h1G, h12, hT₂A₁]
      · simp [Tapes.write, hT₂h1]
      · simp [Tapes.write, hT₂h2]; omega
      · simp [Tapes.write, hT₂G]
      · intro i hi
        have hi2 : i ≠ A₂ := fun h => hi (Or.inl h)
        have hiG : i ≠ G := fun h => hi (Or.inr h)
        exact ⟨by simp [Tapes.write, hi2, hiG], rfl⟩
    | right =>
      have hW₂' : (T₂.setHead A₂ (T₂.hd A₂ + 1)).Within B :=
        Tapes.within_setHead hW₂ (by rw [hT₂h2]; omega)
      have sm := Spec.moveRight (x := x) (t := A₂) hW₂ (by rw [hT₂h2]; omega)
      set T₂' := T₂.setHead A₂ (T₂.hd A₂ + 1)
      have hT₂'h2 : T₂'.hd A₂ = 2 + w.val := by simp [T₂', hT₂h2]; omega
      by_cases hlt : w' < L
      · have hlt' : w.val + 1 < L := by simpa [w', moveWork] using hlt
        have hc : Cond.eval x T₂' (.tape A₂ isB) = true := by
          simp only [Cond.eval, Tapes.read, T₂', Tapes.setHead_tp, hT₂A₂, Tapes.setHead_hd_self,
            hT₂h2]
          rw [show 1 + w.val + 1 = 1 + (w.val + 1) by omega, hZcell ⟨w.val + 1, hlt'⟩]; rfl
        obtain ⟨s, e1, e2⟩ := wr T₂' (1 + w') hW₂'
          (by rw [hT₂'h2]; simp [w', moveWork]; omega) (by simp [T₂', hT₂A₂])
          (by simp [T₂', hT₂Gtp]) (by simp [T₂', Tapes.setHead_hd_ne _ _ (Ne.symm h2G), hT₂G])
        refine ⟨_, sm.seq (Spec.ifElse_true hc hW₂' s), by rw [ite_pos' hlt, e1],
          by rw [ite_pos' hlt, e2], ?_, ?_, ?_, ?_, ?_, rfl,
          Tapes.within_write (Tapes.within_write hW₂')⟩
        · simp [Tapes.write, h1G, h12, T₂', hT₂A₁]
        · simp [Tapes.write, T₂', Tapes.setHead_hd_ne _ _ h12, hT₂h1]
        · simp [Tapes.write, hT₂'h2]; omega
        · simp [Tapes.write, T₂', Tapes.setHead_hd_ne _ _ (Ne.symm h2G), hT₂G]
        · intro i hi
          have hi2 : i ≠ A₂ := fun h => hi (Or.inl h)
          have hiG : i ≠ G := fun h => hi (Or.inr h)
          exact ⟨by simp [Tapes.write, T₂', hi2, hiG],
            by simp [Tapes.write, T₂', Tapes.setHead_hd_ne _ _ hi2]⟩
      · have hwL : w.val + 1 = L := by simp [w', moveWork] at hlt; omega
        have hc : Cond.eval x T₂' (.tape A₂ isB) = false := by
          simp only [Cond.eval, Tapes.read, T₂', Tapes.setHead_tp, hT₂A₂, Tapes.setHead_hd_self,
            hT₂h2]
          rw [show 1 + w.val + 1 = L + 1 by omega, hA₂end₁]
          simp [TM.isBit, hA₂z, hA₂o]
        have hW₃ : (T₂'.write G .no).Within B := Tapes.within_write hW₂'
        refine ⟨T₂'.write G .no, sm.seq (Spec.ifElse_false hc hW₂' (Spec.write hW₂')), ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, rfl, hW₃⟩
        · rw [ite_neg' hlt]; simp [Tapes.write, h2G, T₂', hT₂A₂]
        · rw [ite_neg' hlt]
          simp [Tapes.write, T₂', Tapes.setHead_hd_ne _ _ (Ne.symm h2G),
            hT₂G]
        · simp [Tapes.write, h1G, T₂', hT₂A₁]
        · simp [Tapes.write, T₂', Tapes.setHead_hd_ne _ _ h12, hT₂h1]
        · simp [Tapes.write, hT₂'h2]; omega
        · simp [Tapes.write, T₂', Tapes.setHead_hd_ne _ _ (Ne.symm h2G), hT₂G]
        · intro i hi
          have hi2 : i ≠ A₂ := fun h => hi (Or.inl h)
          have hiG : i ≠ G := fun h => hi (Or.inr h)
          exact ⟨by simp [Tapes.write, T₂', hiG],
            by simp [Tapes.write, T₂', Tapes.setHead_hd_ne _ _ hi2]⟩
    | left =>
      have hlt : w' < L := by simp [w', moveWork]; omega
      have sm := Spec.moveLeft (x := x) (t := A₂) hW₂
      set T₂' := T₂.setHead A₂ (T₂.hd A₂ - 1)
      have hW₂' : T₂'.Within B := Tapes.within_setHead hW₂ (by rw [hT₂h2]; omega)
      have hT₂'h2 : T₂'.hd A₂ = w.val := by simp [T₂', hT₂h2]
      -- back to cell 1 if we stepped onto the marker
      have hfix : ∃ T₂'', Spec (ifElse (.tape A₂ isMk) [Instr.move A₂ .right] []) x B T₂' T₂'' ∧
          T₂''.hd A₂ = 1 + w' ∧ T₂''.tp = T₂'.tp ∧ T₂''.ih = T₂'.ih ∧
          (∀ i, i ≠ A₂ → T₂''.hd i = T₂'.hd i) ∧ T₂''.Within B := by
        by_cases hw0 : w.val = 0
        · have hc : Cond.eval x T₂' (.tape A₂ isMk) = true := by
            simp only [Cond.eval, Tapes.read, T₂', Tapes.setHead_tp, hT₂A₂, Tapes.setHead_hd_self,
              hT₂h2, hw0]
            rw [hA₂0]; rfl
          refine ⟨T₂'.setHead A₂ (T₂'.hd A₂ + 1),
            Spec.ifElse_true hc hW₂' (Spec.moveRight hW₂' (by rw [hT₂'h2]; omega)),
            by simp [hT₂'h2, w', moveWork, hw0], rfl, rfl,
            fun i hi => Tapes.setHead_hd_ne _ _ hi _,
            Tapes.within_setHead hW₂' (by rw [hT₂'h2]; omega)⟩
        · have hc : Cond.eval x T₂' (.tape A₂ isMk) = false := by
            simp only [Cond.eval, Tapes.read, T₂', Tapes.setHead_tp, hT₂A₂, Tapes.setHead_hd_self,
              hT₂h2]
            rw [show 1 + w.val - 1 = 1 + (w.val - 1) by omega, hZcell ⟨w.val - 1, by omega⟩]; rfl
          exact ⟨T₂', Spec.ifElse_false hc hW₂' (Spec.nil hW₂'),
            by rw [hT₂'h2]; simp [w', moveWork]; omega, rfl, rfl, fun _ _ => rfl, hW₂'⟩
      obtain ⟨T₂'', sf, hh2, htp, hih, hhd, hW₂''⟩ := hfix
      obtain ⟨s, e1, e2⟩ := wr T₂'' (1 + w') hW₂'' hh2 (by rw [htp]; simp [T₂', hT₂A₂])
        (by rw [htp]; simp [T₂', hT₂Gtp])
        (by rw [hhd G (Ne.symm h2G)]; simp [T₂', Tapes.setHead_hd_ne _ _ (Ne.symm h2G), hT₂G])
      refine ⟨_, (sm.seq sf).seq s, by rw [ite_pos' hlt, e1], by rw [ite_pos' hlt, e2], ?_, ?_, ?_,
        ?_, ?_, ?_, Tapes.within_write (Tapes.within_write hW₂'')⟩
      · simp [Tapes.write, h1G, h12, htp, T₂', hT₂A₁]
      · simp [Tapes.write, hhd A₁ h12, T₂', Tapes.setHead_hd_ne _ _ h12, hT₂h1]
      · simp [Tapes.write, hh2]; simp [w', moveWork]; omega
      · simp [Tapes.write, hhd G (Ne.symm h2G), T₂', Tapes.setHead_hd_ne _ _ (Ne.symm h2G), hT₂G]
      · intro i hi
        have hi2 : i ≠ A₂ := fun h => hi (Or.inl h)
        have hiG : i ≠ G := fun h => hi (Or.inr h)
        exact ⟨by simp [Tapes.write, htp, T₂', hi2, hiG],
          by simp [Tapes.write, hhd i hi2, T₂', Tapes.setHead_hd_ne _ _ hi2]⟩
      · simp [Tapes.write, hih, T₂']
  obtain ⟨T₃, s3, hT₃A₂, hT₃G, hT₃A₁, hT₃h1, hT₃h2, hT₃hG, ag3, ih3, hW₃⟩ := h3
  -- 4. send both heads home
  have hh1 := Spec.home (x := x) A₁ .mk (T := T₃) (by rw [hT₃A₁, hA₁tp₁]; exact hA₁.1)
    (by rw [hT₃A₁, hA₁tp₁]
        exact home_ok hmb (fun g hg => by
          obtain ⟨b, _, rfl⟩ := List.mem_map.1 hg; exact bit_ne_mk b) hA₁.2.1 hA₁.2.2.1
          (by rw [hT₃h1, hlal]; omega))
    hW₃ (by omega)
  set T₄ := T₃.setHead A₁ 1
  have hW₄ : T₄.Within B := Tapes.within_setHead hW₃ (by omega)
  have hA₂cells : ∀ j, 0 < j → j ≤ L + 1 → T₃.tp A₂ j ≠ .mk := by
    intro j h1 h2
    rw [hT₃A₂]
    have base : T₁.tp A₂ j ≠ .mk := by
      by_cases hj : j ≤ L
      · rw [show j = 1 + (j - 1) by omega, hZcell ⟨j - 1, by omega⟩]; exact fun h => by cases h
      · rw [show j = L + 1 by omega, hA₂end₁]; have := hA₂.2.2.1; rwa [hl₂] at this
    split_ifs
    · simp only [Function.update_apply]; split_ifs
      · exact fun h => by cases h
      · exact base
    · exact base
  have hh2 := Spec.home (x := x) A₂ .mk (T := T₄)
    (by simp only [T₄, Tapes.setHead_tp]; rw [hT₃A₂]; split_ifs
        · rw [Function.update_of_ne (by omega)]; exact hA₂0
        · exact hA₂0)
    (fun j h1 h2 => by
      simp only [T₄, Tapes.setHead_tp]
      rw [Tapes.setHead_hd_ne _ _ (Ne.symm h12)] at h2
      exact hA₂cells j h1 (by omega))
    hW₄ (by omega)
  have hbits : ∀ j : Fin L, T₃.tp A₂ (1 + j) = .z ∨ T₃.tp A₂ (1 + j) = .o := by
    intro j
    rw [hT₃A₂]
    split_ifs
    · simp only [Function.update_apply]; split_ifs
      · exact Or.inr rfl
      · exact Or.inl (hZcell j)
    · exact Or.inl (hZcell j)
  have hA₂0' : T₃.tp A₂ 0 = .mk := by
    rw [hT₃A₂]; split_ifs
    · rw [Function.update_of_ne (by omega)]; exact hA₂0
    · exact hA₂0
  have hA₂end' : T₃.tp A₂ (L + 1) = T₁.tp A₂ (L + 1) := by
    rw [hT₃A₂]; split_ifs
    · rw [Function.update_of_ne (by omega)]
    · rfl
  refine ⟨T₄.setHead A₂ 1, (((s1.seq s2).seq s3).seq hh1).seq hh2, ?_, ?_, ?_, ?_, ?_, by simp,
    ?_, ?_, ?_, Tapes.within_setHead hW₄ (by omega)⟩
  · refine hA₁.congr ?_ ?_
    · simp only [T₄, Tapes.setHead_tp]; rw [hT₃A₁, hA₁tp₁]
    · rw [Tapes.setHead_hd_ne _ _ h12]; simp [T₄, hA₁.2.2.2]
  · simp only [T₄, Tapes.setHead_tp]; exact hT₃G
  · intro hlt
    refine ⟨?_, ?_, ?_, by simp⟩
    · simp only [T₄, Tapes.setHead_tp]; rw [hT₃A₂, ite_pos' hlt, Function.update_of_ne (by omega)]
      exact hA₂0
    · simp only [T₄, Tapes.setHead_tp, List.length_map, List.length_ofFn]
      rw [hT₃A₂, ite_pos' hlt, seg_ofFn, List.map_ofFn]
      congr 1
      funext j
      simp only [Function.comp_apply, Function.update_apply, hZcell j]
      by_cases hj : j.val = w'
      · have : j = ⟨w', hlt⟩ := Fin.ext hj
        simp [this, bit, bsym]
      · have : j ≠ ⟨w', hlt⟩ := fun e => hj (by rw [e])
        have h' : 1 + j.val ≠ 1 + w' := fun e => hj (by omega)
        simp [this, hj, bit, bsym]
    · simp only [T₄, Tapes.setHead_tp, List.length_map, List.length_ofFn]
      rw [hT₃A₂, ite_pos' hlt, Function.update_of_ne (by omega), hA₂end₁]
      have := hA₂.2.2.1; rwa [hl₂] at this
  · refine ⟨List.ofFn (fun j : Fin L => decide (T₃.tp A₂ (1 + j) = .o)), ⟨?_, ?_, ?_, by simp⟩,
      by simp⟩
    · simp only [T₄, Tapes.setHead_tp]; exact hA₂0'
    · simp only [T₄, Tapes.setHead_tp, List.length_map, List.length_ofFn]
      rw [seg_ofFn, List.map_ofFn]
      congr 1; funext j
      rcases hbits j with h | h <;> simp [h, bit, bsym]
    · simp only [T₄, Tapes.setHead_tp, List.length_map, List.length_ofFn]
      rw [hA₂end', hA₂end₁]; have := hA₂.2.2.1; rwa [hl₂] at this
  · simp only [T₄, Tapes.setHead_tp]; rw [hA₂end', hA₂end₁]
  · intro i hi
    have hi2 : i ≠ A₂ := fun h => hi (Or.inl h)
    have hiG : i ≠ G := fun h => hi (Or.inr h)
    have g1 := ag1 i hi2
    have g3 := ag3 i hi
    refine ⟨?_, ?_⟩
    · simp only [T₄, Tapes.setHead_tp]
      by_cases hi1 : i = A₁
      · subst hi1; rw [hT₃A₁, hA₁tp₁]
      · rw [g3.1, Tapes.zipRes_tp_ne hi1]; exact g1.1
    · rw [Tapes.setHead_hd_ne _ _ hi2]
      by_cases hi1 : i = A₁
      · subst hi1; simp [T₄, hA₁.2.2.2]
      · simp only [T₄]; rw [Tapes.setHead_hd_ne _ _ hi1, g3.2, Tapes.zipRes_hd_ne hi1 hi2]
        exact g1.2
  · simp only [T₄, Tapes.setHead_hd_ne _ _ (Ne.symm h2G), Tapes.setHead_hd_ne _ _ (Ne.symm h1G)]
    exact hT₃hG
  · show T₃.ih = T.ih
    rw [ih3]; simp [T₂, Tapes.zipRes, ih1]

end Savitch.Edge
