import Savitch.Edge.Key

/-!
# Checking one move of `M` against the target vertex

Phase 4b-4 of the Savitch formalization (see `PLAN.md`).

The Savitch TM has `NT = 24` work tapes with fixed roles (`tU`, `tV`, …). For one
move `t` of `M` (and the input symbol `i` under the input head), `check i t`
1. computes the moved input position into `tP₂` (`movedPos`);
2. marks the moved work head on `tA₂`, with an in-range flag on `tG` (`markMove`);
3. if in range, builds the successor block on `tS` (`buildS`), compares it with
   the target block on `tV` (`cmpD`), and on a match writes `yes` on `tR`.

`Spec.check`: afterwards `tR` reads `yes` iff it did before or the successor of
`dec u` under `t` exists and is encoded by `v`.
-/

set_option linter.unusedSectionVars false

namespace Savitch.Edge

open TM Machine Machine.NTM

variable {Λ Γ : Type} [Fintype Λ] [Fintype Γ] [DecidableEq Λ] [DecidableEq Γ]
variable {x : List Bool} {B : ℕ}

/-! ### Tapes -/

abbrev NT : ℕ := 32
def tU : Fin NT := 0
def tV : Fin NT := 1
def tS : Fin NT := 2
def tA₁ : Fin NT := 3
def tA₂ : Fin NT := 4
def tP : Fin NT := 5
def tP₂ : Fin NT := 6
def tCU : Fin NT := 7
def tK : Fin NT := 8
def tF : Fin NT := 9
def tF₂ : Fin NT := 10
def tG : Fin NT := 11
def tR : Fin NT := 12

/-! ### Records as digits -/

abbrev nR (Λ Γ : Type) [Fintype Λ] [Fintype Γ] : ℕ := Fintype.card (Rec Λ Γ)

/-- The tape symbol of a digit (a record, numbered by `equivFin`). -/
noncomputable def symR (d : Fin (nR Λ Γ)) : Sym Λ Γ := .rc ((Fintype.equivFin _).symm d)

theorem symR_inj : Function.Injective (symR (Λ := Λ) (Γ := Γ)) := by
  intro a b h
  simp only [symR, Sym.rc.injEq] at h
  exact (Fintype.equivFin _).symm.injective h

theorem rc_digits {L : ℕ} (f : Fin L → Rec Λ Γ) :
    (List.ofFn f).map Sym.rc = ((List.ofFn f).map (Fintype.equivFin _)).map symR := by
  rw [List.map_map]; congr 1; funext r; simp [symR]

theorem digits_inj {L : ℕ} {f g : Fin L → Rec Λ Γ} :
    (List.ofFn f).map (Fintype.equivFin (Rec Λ Γ)) = (List.ofFn g).map (Fintype.equivFin _) ↔
      f = g := by
  constructor
  · intro h
    rw [List.map_ofFn, List.map_ofFn] at h
    have := List.ofFn_injective h
    funext j
    exact (Fintype.equivFin _).injective (congrFun this j)
  · rintro rfl; rfl

theorem eq_encV_iff {n L : ℕ} (v : Fin (nV Λ Γ L)) (b : BCfg Λ Γ n L) :
    v = encV b ↔ recs v = encR b := by
  constructor
  · rintro rfl; exact recs_unrecs _
  · intro h
    have : unrecs (recs v) = v := by
      apply finFunctionFinEquiv.symm.injective
      funext j
      simp [unrecs, recs]
    rw [← this, h]; rfl

theorem moveIn_lt {n L ih : ℕ} (d : Dir) (hih : ih ≤ n + 1) (hfit : n + 1 < 2 ^ L) :
    moveIn n ih d < 2 ^ L := by
  have := moveIn_le n ih d hih; omega

/-! ### The check -/

/-- Check move `t` (for input symbol `i`) against the target block on `tV`. -/
noncomputable def check (i : Option Bool) (t : Λ × Γ × Dir × Dir) : Code NT (Sym Λ Γ) :=
  movedPos i t.2.2.1 tP tP₂ tF ++ markMove t.2.2.2 tA₁ tA₂ tG ++
    ifElse (.tape tG (fun g => decide (g = .yes)))
      (buildS t.1 t.2.1 tU tS tA₁ tA₂ tP₂ ++ cmpD tS tV tF₂ symR .yes .no ++
        TM.home tS .mk ++ TM.home tV .mk ++
        ifElse (.tape tF₂ (fun g => decide (g = .yes))) [Instr.write tR .yes] [])
      []

/-- The scratch tapes of the edge test, in the standard layouts. -/
def Scratch (L : ℕ) (T : Tapes NT (Sym Λ Γ)) : Prop :=
  (∃ ls : List (Sym Λ Γ), Lay tS .mk .blank T ls ∧ ls.length = L ∧ ∀ g ∈ ls, g ≠ .mk) ∧
  (∃ l : List Bool, LayW tA₂ .mk T (l.map bit) ∧ l.length = L ∧
    T.tp tA₂ (L + 1) ≠ .z ∧ T.tp tA₂ (L + 1) ≠ .o) ∧
  (∃ l : List Bool, Holds tP₂ .mk .z .o T l ∧ l.length = L)

theorem Spec.check {L : ℕ} (hL : 0 < L) (hfit : x.length + 1 < 2 ^ L)
    (u v : Fin (nV Λ Γ L)) (t : Λ × Γ × Dir × Dir) {lp : List Bool} {T : Tapes NT (Sym Λ Γ)}
    (hU : Lay tU .mk .blank T ((List.ofFn (recs u)).map .rc))
    (hV : LayW tV .mk T ((List.ofFn (recs v)).map .rc))
    (hA₁ : Lay tA₁ .mk .blank T
      ((List.ofFn fun j : Fin L => decide (j = firstFlag hL (recs u))).map bit))
    (hP : InPos tP .mk .z .o x T lp) (hlp : lp.length = L)
    (hih : T.ih = (decV (n := x.length) hL u).2.1.val)
    (hSc : Scratch L T) (hT : T.Within B) (hB : L + 2 ≤ B) :
    ∃ T', Spec (check (inputSym x T.ih) t) x B T T' ∧
      T'.tp tR (T.hd tR) = (if (∃ b', nextB (decV (n := x.length) hL u) t = some b' ∧
          v = encV b') then .yes else T.tp tR (T.hd tR)) ∧
      Lay tU .mk .blank T' ((List.ofFn (recs u)).map .rc) ∧
      LayW tV .mk T' ((List.ofFn (recs v)).map .rc) ∧
      Lay tA₁ .mk .blank T'
        ((List.ofFn fun j : Fin L => decide (j = firstFlag hL (recs u))).map bit) ∧
      InPos tP .mk .z .o x T' lp ∧ Scratch L T' ∧
      T.Agree (fun i => i = tS ∨ i = tA₂ ∨ i = tP₂ ∨ i = tF ∨ i = tF₂ ∨ i = tG ∨ i = tR) T' ∧
      T'.hd tR = T.hd tR ∧ T'.ih = T.ih ∧ T'.Within B := by
  obtain ⟨⟨ls, hS, hls, hlsm⟩, ⟨l₂, hA₂, hl₂, hA₂z, hA₂o⟩, ⟨l₃, hP₂, hl₃⟩⟩ := hSc
  have hmb : (Sym.mk : Sym Λ Γ) ≠ .blank := fun h => by cases h
  obtain ⟨q₂, g₂, di, dw⟩ := t
  set w := firstFlag hL (recs u) with hw
  -- 1. the moved input position
  obtain ⟨T₁, l₃', s1, hP₂₁, hl₃', hv, ag1, hF₁, ih1, hW₁⟩ :=
    Spec.movedPos (x := x) (P := tP) (P₂ := tP₂) (F := tF) (by decide) (by decide) (by decide)
      di hP hP₂ (by rw [hl₃, hlp]) hT (by rw [hlp]; exact hB)
  have hU₁ := agree_lay ag1 (by decide) hU
  have hV₁ := agree_layW ag1 (by decide) hV
  have hA₁₁ := agree_lay ag1 (by decide) hA₁
  have hS₁ := agree_lay ag1 (by decide) hS
  have hA₂₁ := agree_layW ag1 (by decide) hA₂
  have gA₂₁ := ag1 tA₂ (by decide)
  have hP₁ : InPos tP .mk .z .o x T₁ lp :=
    ⟨hP.1.congr (ag1 tP (by decide)).1 (ag1 tP (by decide)).2, by rw [ih1]; exact hP.2.1,
      by rw [ih1]; exact hP.2.2.1, hP.2.2.2⟩
  -- 2. the moved work-head mark
  obtain ⟨T₂, s2, hA₁₂, hG₂, hA₂in, ⟨l₄, hA₂₂, hl₄⟩, hA₂end₂, _, ag2, hGhd₂, ih2, hW₂⟩ :=
    Spec.markMove (x := x) (A₁ := tA₁) (A₂ := tA₂) (G := tG) (by decide) (by decide) (by decide)
      dw w hA₁₁ hA₂₁ (by simp [hl₂]) (by rw [gA₂₁.1]; exact hA₂z) (by rw [gA₂₁.1]; exact hA₂o)
      hW₁ hB
  have hU₂ := agree_lay ag2 (by decide) hU₁
  have hV₂ := agree_layW ag2 (by decide) hV₁
  have hS₂ := agree_lay ag2 (by decide) hS₁
  have hP₂₂ : Holds tP₂ .mk .z .o T₂ l₃' :=
    hP₂₁.congr (ag2 tP₂ (by decide)).1 (ag2 tP₂ (by decide)).2
  have hP₂' : InPos tP .mk .z .o x T₂ lp :=
    ⟨hP₁.1.congr (ag2 tP (by decide)).1 (ag2 tP (by decide)).2, by rw [ih2]; exact hP₁.2.1,
      by rw [ih2]; exact hP₁.2.2.1, hP₁.2.2.2⟩
  have hA₂endT : T₂.tp tA₂ (L + 1) = T.tp tA₂ (L + 1) := by rw [hA₂end₂, gA₂₁.1]
  have hR₂ : T₂.tp tR = T.tp tR ∧ T₂.hd tR = T.hd tR :=
    ⟨((ag2 tR (by decide)).1).trans (ag1 tR (by decide)).1,
     ((ag2 tR (by decide)).2).trans (ag1 tR (by decide)).2⟩
  have ag12 : T.Agree (fun i => i = tS ∨ i = tA₂ ∨ i = tP₂ ∨ i = tF ∨ i = tF₂ ∨ i = tG ∨ i = tR)
      T₂ := (ag1.mono (fun i h => by rcases h with h | h <;> simp [h])).trans
        (ag2.mono (fun i h => by rcases h with h | h <;> simp [h]))
  have hTG : T₂.read tG = (if moveWork w.val dw < L then .yes else .no) := by
    rw [Tapes.read, hGhd₂]; exact hG₂
  by_cases hr : moveWork w.val dw < L
  · -- in range: build, compare, record
    have hc : Cond.eval x T₂ (.tape tG (fun g => decide (g = .yes))) = true := by
      simp [Cond.eval, hTG, hr]
    have hihlt : moveIn x.length (decV (n := x.length) hL u).2.1.val di < x.length + 2 := by
      have := moveIn_le x.length (decV (n := x.length) hL u).2.1.val di
        (by have := (decV (n := x.length) hL u).2.1.isLt; omega); omega
    set b' : BCfg Λ Γ x.length L :=
      (q₂, ⟨moveIn x.length (decV (n := x.length) hL u).2.1.val di, hihlt⟩,
        ⟨moveWork w.val dw, hr⟩, Function.update (decV (n := x.length) hL u).2.2.2 w g₂)
    have hb' : nextB (decV (n := x.length) hL u) (q₂, g₂, di, dw) = some b' := by
      have hr' : moveWork (decV (n := x.length) hL u).2.2.1.val dw < L := hr
      simp only [nextB, hr', ↓reduceDIte]; rfl
    have hl₃eq : l₃' = toBits b'.2.1.val L := by
      apply bval_inj (by rw [toBits_length, hl₃', hlp])
      rw [hv, bval_toBits L _ (moveIn_lt di (by have := (decV (n := x.length) hL u).2.1.isLt; omega)
        hfit), hih]
    -- build the successor block
    obtain ⟨T₃, s3, hS₃, ag3, ih3, hW₃⟩ := Spec.buildS (x := x) (U := tU) (S := tS)
      (A₁ := tA₁) (A₂ := tA₂) (P₂ := tP₂) (by decide) (by decide) (by decide) (by decide) q₂ g₂
      (ru := List.ofFn (recs u)) (ls := ls)
      (m₁ := List.ofFn fun j : Fin L => decide (j = w))
      (m₂ := List.ofFn fun j : Fin L => decide (j = ⟨moveWork w.val dw, hr⟩)) (m₃ := l₃')
      hU₂ hS₂ (hA₁₂.toW hmb) (hA₂in hr) hP₂₂.toW (by simp [hls]) (by simp) (by simp)
      (by simp [hl₃', hlp]) hW₂ (by simpa using hB)
    have hbuild : build q₂ g₂ (List.ofFn (recs u)) (List.ofFn fun j : Fin L => decide (j = w))
        (List.ofFn fun j : Fin L => decide (j = ⟨moveWork w.val dw, hr⟩)) l₃' =
        List.ofFn (encR b') := by
      rw [hl₃eq]; exact build_eq_encR hL u (q₂, g₂, di, dw) b' hb'
    rw [hbuild, rc_digits] at hS₃
    set ds := (List.ofFn (encR b')).map (Fintype.equivFin (Rec Λ Γ))
    set dv := (List.ofFn (recs v)).map (Fintype.equivFin (Rec Λ Γ))
    have hV₃ : LayW tV .mk T₃ (dv.map symR) := by
      have := agree_layW ag3 (by decide) hV₂; rwa [rc_digits] at this
    have hdsl : ds.length = L := by simp [ds]
    have hdvl : dv.length = L := by simp [dv]
    have hS₃hd : T₃.hd tS = 1 := hS₃.2.2.2
    have hV₃hd : T₃.hd tV = 1 := hV₃.2.2.2
    -- compare with the target
    obtain ⟨T₄, s4, c1, c2, c3, c4, c5, c6, c7⟩ := Spec.cmpD (x := x) (a := tS) (b := tV)
      (f := tF₂) (by decide) (by decide) (by decide) symR_inj (yes := .yes) (no := .no) ds dv T₃
      (by rw [hdsl, hdvl])
      (by rw [hS₃hd]; have := hS₃.2.1; rwa [List.length_map] at this)
      (by rw [hV₃hd]; have := hV₃.2.1; rwa [List.length_map] at this)
      (fun d => by
        have he : T₃.tp tS (ds.length + 1) = .blank := by
          have := hS₃.2.2.1; rwa [List.length_map] at this
        rw [hS₃hd, Nat.add_comm, he]; exact fun h => by simp [symR] at h)
      hW₃ (by rw [hS₃hd, hdsl]; omega) (by rw [hV₃hd, hdsl]; omega)
    simp only [Tapes.write_hd] at c1 c2 c4 c5 c6
    have hW₄ : T₄.Within B := s4.target_within
    have hflag : T₄.tp tF₂ (T₃.hd tF₂) = if ds = dv then .yes else .no := by
      rw [c1]; simp [Tapes.read, Tapes.write_tp_self]
    have hT₄tp : ∀ i, i ≠ tF₂ → T₄.tp i = T₃.tp i := fun i hi => by
      rw [c3 i hi]; simp [Tapes.write, hi]
    -- heads home
    have hh1 := Spec.home (x := x) tS .mk (T := T₄)
      (by rw [hT₄tp tS (by decide)]; exact hS₃.1)
      (by rw [hT₄tp tS (by decide)]
          exact home_ok hmb (fun g hg => by
            obtain ⟨d, _, rfl⟩ := List.mem_map.1 hg; exact fun h => by simp [symR] at h)
            hS₃.2.1 hS₃.2.2.1 (by rw [c4, hS₃hd]; simp [ds, Nat.add_comm]))
      hW₄ (by omega)
    set T₅ := T₄.setHead tS 1
    have hW₅ : T₅.Within B := Tapes.within_setHead hW₄ (by omega)
    have hh2 := Spec.home (x := x) tV .mk (T := T₅)
      (by simp only [T₅, Tapes.setHead_tp]; rw [hT₄tp tV (by decide)]; exact hV₃.1)
      (by simp only [T₅, Tapes.setHead_tp]; rw [hT₄tp tV (by decide)]
          refine home_okW (fun g hg => by
            obtain ⟨d, _, rfl⟩ := List.mem_map.1 hg; exact fun h => by simp [symR] at h)
            hV₃.2.1 hV₃.2.2.1 ?_
          rw [Tapes.setHead_hd_ne _ _ (by decide), c5, hV₃hd]; simp [ds, dv, Nat.add_comm])
      hW₅ (by omega)
    set T₆ := T₅.setHead tV 1
    have hW₆ : T₆.Within B := Tapes.within_setHead hW₅ (by omega)
    have hT₆tp : T₆.tp = T₄.tp := rfl
    have hT₆F₂ : T₆.hd tF₂ = T₃.hd tF₂ := by
      simp only [T₆, T₅, Tapes.setHead_hd_ne _ _ (show tF₂ ≠ tV by decide),
        Tapes.setHead_hd_ne _ _ (show tF₂ ≠ tS by decide)]
      exact c6 tF₂ (by decide) (by decide)
    have hT₆R : T₆.hd tR = T.hd tR := by
      simp only [T₆, T₅, Tapes.setHead_hd_ne _ _ (show tR ≠ tV by decide),
        Tapes.setHead_hd_ne _ _ (show tR ≠ tS by decide)]
      rw [c6 tR (by decide) (by decide), (ag3 tR (by decide)).2, hR₂.2]
    have hT₆Rtp : T₆.tp tR = T.tp tR := by
      rw [hT₆tp, hT₄tp tR (by decide), (ag3 tR (by decide)).1, hR₂.1]
    have hread : T₆.read tF₂ = if ds = dv then .yes else .no := by
      rw [Tapes.read, hT₆tp, hT₆F₂, hflag]
    -- record a match
    obtain ⟨T₇, s5, hR₇, h7tp, h7hd, h7ih, hW₇⟩ : ∃ T₇,
        Spec (ifElse (.tape tF₂ (fun g => decide (g = (Sym.yes : Sym Λ Γ))))
          [Instr.write tR (Sym.yes : Sym Λ Γ)] []) x B T₆ T₇ ∧
        T₇.tp tR (T.hd tR) = (if ds = dv then .yes else T.tp tR (T.hd tR)) ∧
        (∀ i, i ≠ tR → T₇.tp i = T₆.tp i) ∧ T₇.hd = T₆.hd ∧ T₇.ih = T₆.ih ∧ T₇.Within B := by
      by_cases heq : ds = dv
      · refine ⟨T₆.write tR .yes, Spec.ifElse_true (by simp [Cond.eval, hread, heq]) hW₆
          (Spec.write hW₆), ?_, fun i hi => by simp [Tapes.write, hi], rfl, rfl,
          Tapes.within_write hW₆⟩
        rw [ite_pos' heq, Tapes.write_tp_self, hT₆R, ite_pos' rfl]
      · refine ⟨T₆, Spec.ifElse_false (by simp [Cond.eval, hread, heq]) hW₆ (Spec.nil hW₆), ?_,
          fun _ _ => rfl, rfl, rfl, hW₆⟩
        rw [ite_neg' heq, hT₆Rtp]
    have hiff : (∃ b'', nextB (decV (n := x.length) hL u) (q₂, g₂, di, dw) = some b'' ∧
        v = encV b'') ↔ ds = dv := by
      constructor
      · rintro ⟨b'', hb'', hv''⟩
        have : b'' = b' := Option.some.inj (hb''.symm.trans hb')
        rw [this] at hv''
        exact (digits_inj.2 ((eq_encV_iff v b').1 hv'')).symm
      · intro h
        exact ⟨b', hb', (eq_encV_iff v b').2 (digits_inj.1 h).symm⟩
    -- the chain from `T₃` to `T₇` on untouched tapes
    have chain : ∀ i, i ≠ tS → i ≠ tV → i ≠ tF₂ → i ≠ tR →
        T₇.tp i = T₃.tp i ∧ T₇.hd i = T₃.hd i := by
      intro i h1 h2 h3 h4
      refine ⟨by rw [h7tp i h4, hT₆tp, hT₄tp i h3], ?_⟩
      rw [h7hd]
      simp only [T₆, T₅, Tapes.setHead_hd_ne _ _ h2, Tapes.setHead_hd_ne _ _ h1]
      exact c6 i h1 h2
    have back : ∀ i, i ≠ tS → i ≠ tV → i ≠ tF₂ → i ≠ tR →
        T₇.tp i = T₂.tp i ∧ T₇.hd i = T₂.hd i := fun i h1 h2 h3 h4 =>
      ⟨(chain i h1 h2 h3 h4).1.trans (ag3 i h1).1, (chain i h1 h2 h3 h4).2.trans (ag3 i h1).2⟩
    have hV₇tp : T₇.tp tV = T₂.tp tV := by
      rw [h7tp tV (by decide), hT₆tp, hT₄tp tV (by decide), (ag3 tV (by decide)).1]
    have hV₇hd : T₇.hd tV = 1 := by rw [h7hd]; simp [T₆]
    have hS₇tp : T₇.tp tS = T₃.tp tS := by rw [h7tp tS (by decide), hT₆tp, hT₄tp tS (by decide)]
    have hS₇hd : T₇.hd tS = 1 := by
      rw [h7hd]; simp [T₆, T₅, Tapes.setHead_hd_ne _ _ (show tS ≠ tV by decide)]
    have hih₇ : T₇.ih = T.ih := by
      rw [h7ih]; show T₄.ih = T.ih
      rw [c7]; simp [Tapes.write, ih3, ih2, ih1]
    refine ⟨T₇, (s1.seq s2).seq (Spec.ifElse_true hc hW₂ ((((s3.seq s4).seq hh1).seq hh2).seq s5)),
      hR₇.trans (if_congr hiff.symm rfl rfl), ?_, ?_, ?_, ?_, ?_, ?_, by rw [h7hd, hT₆R], hih₇,
      hW₇⟩
    · exact hU₂.congr (back tU (by decide) (by decide) (by decide) (by decide)).1
        (back tU (by decide) (by decide) (by decide) (by decide)).2
    · exact hV₂.congr hV₇tp (by rw [hV₇hd, hV₂.2.2.2])
    · exact hA₁₂.congr (back tA₁ (by decide) (by decide) (by decide) (by decide)).1
        (back tA₁ (by decide) (by decide) (by decide) (by decide)).2
    · have g := back tP (by decide) (by decide) (by decide) (by decide)
      exact ⟨hP₂'.1.congr g.1 g.2, by rw [hih₇]; exact hP.2.1, by rw [hih₇]; exact hP.2.2.1,
        hP.2.2.2⟩
    · refine ⟨⟨ds.map symR, hS₃.congr hS₇tp (by rw [hS₇hd, hS₃hd]), by simp [hdsl], fun g hg => by
          obtain ⟨d, _, rfl⟩ := List.mem_map.1 hg; exact fun h => by simp [symR] at h⟩, ?_, ?_⟩
      · have g := back tA₂ (by decide) (by decide) (by decide) (by decide)
        exact ⟨_, (hA₂in hr).congr g.1 g.2, by simp,
          by rw [g.1, hA₂endT]; exact hA₂z, by rw [g.1, hA₂endT]; exact hA₂o⟩
      · have g := back tP₂ (by decide) (by decide) (by decide) (by decide)
        exact ⟨l₃', hP₂₂.congr g.1 g.2, by rw [hl₃', hlp]⟩
    · intro i hi
      have h12 := ag12 i hi
      have hiS : i ≠ tS := fun e => hi (Or.inl e)
      have hiF₂ : i ≠ tF₂ := fun e => hi (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))
      have hiR : i ≠ tR := fun e => hi (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e))))))
      by_cases hiV : i = tV
      · subst hiV
        exact ⟨hV₇tp.trans h12.1, by rw [hV₇hd, hV.2.2.2]⟩
      · have g := back i hiS hiV hiF₂ hiR
        exact ⟨g.1.trans h12.1, g.2.trans h12.2⟩
  · -- out of range: nothing to do
    have hc : Cond.eval x T₂ (.tape tG (fun g => decide (g = .yes))) = false := by
      simp [Cond.eval, hTG, hr]
    have hnone : nextB (decV (n := x.length) hL u) (q₂, g₂, di, dw) = none := by
      have hr' : ¬ moveWork (decV (n := x.length) hL u).2.2.1.val dw < L := hr
      simp only [nextB, hr', ↓reduceDIte]
    refine ⟨T₂, (s1.seq s2).seq (Spec.ifElse_false hc hW₂ (Spec.nil hW₂)), ?_, hU₂, hV₂, hA₁₂,
      hP₂', ⟨⟨ls, hS₂, hls, hlsm⟩, ⟨l₄, hA₂₂, hl₄, by rw [hA₂endT]; exact hA₂z,
        by rw [hA₂endT]; exact hA₂o⟩, ⟨l₃', hP₂₂, by rw [hl₃', hlp]⟩⟩, ag12, hR₂.2,
      by rw [ih2, ih1], hW₂⟩
    rw [ite_neg' (by rintro ⟨b'', hb'', _⟩; rw [hnone] at hb''; cases hb''),
      hR₂.1]

end Savitch.Edge
