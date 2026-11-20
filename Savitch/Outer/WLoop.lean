import Savitch.Outer.Setup

/-!
# The outer width-search loop and full Savitch program

Phase 4b-6 / 4b-7 of the Savitch formalization (see `PLAN.md`).

* `WInv M L T`: the ruler tape `tRu` holds `L` copies of `rInit₀ M`, all
  block/counter/stack tapes are at home (`AllHome`), and `T.ih = 0`.
* `wBody M`: at width `L`, test whether `x.length + 1 < 2 ^ L` (`fitTest`). If so,
  initialize the width-`L` layout (`setupWidth`), run the vertex loop (`vLoop`),
  reset the input head, and if some reachable vertex escaped (`tEsc = .yes`), grow
  `tRu` to `L + 1` (`growRu`). If `x.length + 1 ≥ 2 ^ L`, set `tEsc := .yes` and
  grow `tRu` to `L + 1`.
* `savitchCode M`: initialize all work tapes from blank, run `whileDo (tEsc = .yes)
  (wBody M)` starting at `L = 1`, and halt with `true` iff `tAcc = .yes`.
-/

set_option linter.unusedSectionVars false

namespace Savitch.Edge

open TM Machine Machine.NTM

variable {Λ Γ : Type} [Fintype Λ] [Fintype Γ] [DecidableEq Λ] [DecidableEq Γ]
variable {x : List Bool} {B : ℕ} {L : ℕ}

/-! ### The outer-loop invariant and growing the ruler -/

def WInv (M : NTM Λ Γ) (L : ℕ) (T : Tapes NT (Sym Λ Γ)) : Prop :=
  Lay tRu .mk .blank T (List.replicate L (rInit₀ M)) ∧ AllHome T ∧ T.ih = 0

theorem replicate_append_one {α : Type} (a : α) : ∀ L,
    List.replicate L a ++ [a] = List.replicate (L + 1) a
  | 0 => rfl
  | L + 1 => by simp [List.replicate_succ, replicate_append_one a L]

noncomputable def growRu (M : NTM Λ Γ) : Code NT (Sym Λ Γ) :=
  appendCell tRu isRec (rInit₀ M)

theorem Spec.growRu (M : NTM Λ Γ) {T : Tapes NT (Sym Λ Γ)}
    (hW : WInv M L T) (hT : T.Within B) (hB : L + 3 ≤ B) :
    ∃ T', Spec (growRu M) x B T T' ∧ WInv M (L + 1) T' ∧
      T.Agree (fun i => i = tRu) T' ∧ T'.Within B := by
  obtain ⟨hRu, hH, hih⟩ := hW
  have hrl : (List.replicate L (rInit₀ M)).length = L := List.length_replicate
  obtain ⟨T', s, h0, hseg, hend, h1, ag, ih, hW'⟩ :=
    Spec.appendCell (x := x) (t := tRu) (p := isRec) (g := rInit₀ M) (fun h => by cases h)
      hRu.1 hRu.2.1
      (fun g hg => by rw [List.eq_of_mem_replicate hg]; rfl)
      (fun g hg => by rw [List.eq_of_mem_replicate hg]; exact fun h => by cases h)
      (by rw [hRu.2.2.1]; rfl) hRu.2.2.2 hT (by rw [hrl]; exact hB)
  rw [hrl, replicate_append_one] at hseg
  rw [hrl] at hend
  refine ⟨T', s, ⟨⟨h0, by rw [List.length_replicate]; exact hseg,
    by rw [List.length_replicate]; exact hend, h1⟩, ?_, by rw [ih, hih]⟩, ag, hW'⟩
  intro i hi
  have hiR : i ≠ tRu := by revert i hi; decide
  exact ⟨by rw [(ag i hiR).1]; exact (hH i hi).1, by rw [(ag i hiR).2]; exact (hH i hi).2⟩

/-! ### Whether width `L` must grow -/

open Classical in
def NeedsGrow (M : NTM Λ Γ) (x : List Bool) (L : ℕ) (hL : 0 < L) : Prop :=
  ¬ (x.length + 1 < 2 ^ L) ∨
    ∃ u : Fin (nV Λ Γ L), EscV (x := x) M hL (encV (n := x.length) (M.initB hL)) u

theorem accV_iff_accepts (M : NTM Λ Γ) (hL : 0 < L)
    (hng : ¬ NeedsGrow M x L hL) :
    (∃ u : Fin (nV Λ Γ L), AccV (x := x) M hL (encV (n := x.length) (M.initB hL)) u) ↔
      M.Accepts x := by
  have hfit : x.length + 1 < 2 ^ L := Classical.not_not.1 (fun h => hng (Or.inl h))
  have hne_esc : ¬ ∃ u, EscV (x := x) M hL (encV (n := x.length) (M.initB hL)) u :=
    fun h => hng (Or.inr h)
  have hne : ∀ b, Relation.ReflTransGen (M.BStep x) (M.initB (n := x.length) hL) b →
      ¬ M.Escapes x b := by
    intro b hb hesc
    apply hne_esc
    refine ⟨encV b, ?_, by rw [decV_encV hL hfit]; exact hesc⟩
    exact hb.lift encV (fun a b' h => ⟨b', by rw [decV_encV hL hfit]; exact h, rfl⟩)
  rw [M.accepts_iff_gen_closed x hL hfit hne]
  exact exists_congr fun u => and_comm

theorem not_needsGrow_of_bounded {s : ℕ → ℕ} (M : NTM Λ Γ) (hM : M.SpaceBounded s)
    (hL : 0 < L) (hsL : s x.length ≤ L) (hfit : x.length + 1 < 2 ^ L) :
    ¬ NeedsGrow M x L hL := by
  rintro (hnot | ⟨u, hreach, hesc⟩)
  · exact hnot hfit
  · have key : ∀ w, Relation.ReflTransGen (M.GEdge x hL) (encV (n := x.length) (M.initB hL)) w →
        ∃ b : BCfg Λ Γ x.length L, w = encV b ∧
          Relation.ReflTransGen (M.BStep x) (M.initB hL) b := by
      intro w hw
      induction hw with
      | refl => exact ⟨_, rfl, .refl⟩
      | tail _ hstep ih =>
        obtain ⟨b, rfl, hpath⟩ := ih
        obtain ⟨b', hb', rfl⟩ := hstep
        rw [decV_encV hL hfit] at hb'
        exact ⟨b', rfl, hpath.tail hb'⟩
    obtain ⟨b, rfl, hpath⟩ := key u hreach
    rw [decV_encV hL hfit] at hesc
    exact M.no_escape_of_bounded hM x hL hsL b hpath hesc

/-! ### One width-search iteration -/

noncomputable def wBody [NeZero (nR Λ Γ)] (M : NTM Λ Γ) : Code NT (Sym Λ Γ) :=
  fitTest ++
    ifElse (.tape tF₂ (fun g => decide (g = .yes)))
      (setupWidth M ++ vLoop M ++ resetIn ++
        ifElse (.tape tEsc (fun g => decide (g = .yes))) (growRu M) [])
      ([Instr.write tEsc .yes] ++ growRu M)

theorem rep_ih_le [NeZero (nV Λ Γ L)] {K WK : ℕ} {r : Bool} {T : Tapes NT (Sym Λ Γ)}
    (hR : Rep L x K WK T (.done r)) : T.ih ≤ x.length + 1 := by
  obtain ⟨_, _, _, _, _, _, _, ⟨_, hP, _⟩, _⟩ := hR
  exact hP.2.2.1

open Classical in
theorem Spec.wBody_grow [NeZero (nV Λ Γ L)] [NeZero (nR Λ Γ)] (M : NTM Λ Γ) (hL : 0 < L)
    (hng : NeedsGrow M x L hL) {T : Tapes NT (Sym Λ Γ)} (hW : WInv M L T)
    (hT : T.Within B) (hB : (nR Λ Γ * L + 1) * (L + 1) + nR Λ Γ * L + 8 ≤ B) :
    ∃ T', Spec (wBody M) x B T T' ∧ WInv M (L + 1) T' ∧
      T'.read tEsc = .yes ∧ T'.Within B := by
  obtain ⟨hRu, hH, hih⟩ := hW
  set lr := List.replicate L (rInit₀ M)
  have hlr : lr.length = L := List.length_replicate
  have hrec : ∀ g ∈ lr, isRec g = true := fun g hg => by
    rw [List.eq_of_mem_replicate hg]; rfl
  have hLB : L + 3 ≤ B := by
    have := Nat.le_mul_of_pos_left (L + 1) (show 0 < nR Λ Γ * L + 1 by omega); omega
  obtain ⟨T₁, s1, hF₂₁, hRu₁, hih₁, hCU0₁, hCU1₁, ag1, hW₁⟩ :=
    Spec.fitTest (x := x) hrec (by rw [hlr]; exact hL) hRu (hH tCU (by decide)) hih hT
      (by rw [hlr]; omega)
  have hH₁ : AllHome T₁ := by
    intro i hi
    by_cases h : i = tCU
    · subst h; exact ⟨hCU0₁, hCU1₁⟩
    · have hnot : ¬ (i = tCU ∨ i = tF ∨ i = tF₂) := by
        rintro (rfl | rfl | rfl)
        · exact h rfl
        · revert hi; decide
        · revert hi; decide
      exact ⟨by rw [(ag1 i hnot).1]; exact (hH i hi).1,
        by rw [(ag1 i hnot).2]; exact (hH i hi).2⟩
  by_cases hfit : x.length + 1 < 2 ^ L
  · have hesc : ∃ u, EscV (x := x) M hL (encV (n := x.length) (M.initB hL)) u :=
      hng.resolve_left (not_not.2 hfit)
    have hcF₂ : Cond.eval x T₁ (.tape tF₂ (fun g => decide (g = (Sym.yes : Sym Λ Γ)))) = true := by
      rw [hlr] at hF₂₁; simp [Cond.eval, hF₂₁, hfit]
    obtain ⟨T₂, s2, hRep₂, hRegs₂, hRu₂, hih₂, hW₂⟩ :=
      Spec.setupWidth (x := x) M hL hfit hRu₁ hH₁ hih₁ hW₁
        (by have := Nat.le_mul_of_pos_left (L + 1) (show 0 < nR Λ Γ * L + 1 by omega); omega)
    obtain ⟨T₃, r₃, s3, hRep₃, ⟨v', hRegs₃⟩, hEsc₃, _, hEhd₃, _, ag3, hW₃⟩ :=
      Spec.vLoop (x := x) M hL hfit Nat.lt_two_pow_self (nV_le_two_pow L)
        (encV (n := x.length) (M.initB hL)) hB hRep₂ hRegs₂ hW₂
    have hRu₃ := agree_lay ag3 (by decide) hRu₂
    have hH₃ : AllHome T₃ := allHome_of_rep_regs hRep₃ hRegs₃
    have hreadEsc₃ : T₃.read tEsc = .yes := by
      rw [Tapes.read, hEhd₃, hEsc₃, ite_pos' hesc]
    have s4 := Spec.resetIn (x := x) (T := T₃) (rep_ih_le hRep₃) hW₃
    set T₄ : Tapes NT (Sym Λ Γ) := { T₃ with ih := 0 }
    have hWInv₄ : WInv M L T₄ := ⟨hRu₃, hH₃, rfl⟩
    have hcEsc : Cond.eval x T₄ (.tape tEsc (fun g => decide (g = (Sym.yes : Sym Λ Γ)))) = true := by
      show decide (T₃.read tEsc = .yes) = true
      simp [hreadEsc₃]
    obtain ⟨T₅, s5, hWInv₅, ag5, hW₅⟩ := Spec.growRu (x := x) M hWInv₄ hW₃ hLB
    have hreadEsc₅ : T₅.read tEsc = .yes := by
      rw [Tapes.read, (ag5 tEsc (by decide)).1, (ag5 tEsc (by decide)).2]
      exact hreadEsc₃
    exact ⟨T₅, s1.seq (Spec.ifElse_true hcF₂ hW₁ (((s2.seq s3).seq s4).seq
      (Spec.ifElse_true hcEsc hW₃ s5))), hWInv₅, hreadEsc₅, hW₅⟩
  · have hcF₂ : Cond.eval x T₁ (.tape tF₂ (fun g => decide (g = (Sym.yes : Sym Λ Γ)))) = false := by
      rw [hlr] at hF₂₁; simp [Cond.eval, hF₂₁, hfit]
    have s2 := Spec.write (x := x) (t := tEsc) (g := (Sym.yes : Sym Λ Γ)) hW₁
    set T₂ := T₁.write tEsc .yes
    have hW₂ : T₂.Within B := Tapes.within_write hW₁
    have ag2 : T₁.Agree (fun i => i = tEsc) T₂ := fun i hi =>
      ⟨by simp [T₂, Tapes.write, hi], rfl⟩
    have hWInv₂ : WInv M L T₂ := by
      refine ⟨agree_lay ag2 (by decide) hRu₁, ?_, hih₁⟩
      intro i hi
      have hne : i ≠ tEsc := by revert i hi; decide
      exact ⟨by rw [(ag2 i hne).1]; exact (hH₁ i hi).1,
        by rw [(ag2 i hne).2]; exact (hH₁ i hi).2⟩
    obtain ⟨T₃, s3, hWInv₃, ag3, hW₃⟩ := Spec.growRu (x := x) M hWInv₂ hW₂ hLB
    have hreadEsc₃ : T₃.read tEsc = .yes := by
      rw [Tapes.read, (ag3 tEsc (by decide)).1, (ag3 tEsc (by decide)).2]
      simp [T₂, Tapes.write_tp_self]
    exact ⟨T₃, s1.seq (Spec.ifElse_false hcF₂ hW₁ (s2.seq s3)), hWInv₃, hreadEsc₃, hW₃⟩

open Classical in
theorem Spec.wBody_stop [NeZero (nV Λ Γ L)] [NeZero (nR Λ Γ)] (M : NTM Λ Γ) (hL : 0 < L)
    (hng : ¬ NeedsGrow M x L hL) {T : Tapes NT (Sym Λ Γ)} (hW : WInv M L T)
    (hT : T.Within B) (hB : (nR Λ Γ * L + 1) * (L + 1) + nR Λ Γ * L + 8 ≤ B) :
    ∃ T', Spec (wBody M) x B T T' ∧ WInv M L T' ∧
      T'.read tEsc = .no ∧ T'.read tAcc = (if M.Accepts x then .yes else .no) ∧
      T'.Within B := by
  have hfit : x.length + 1 < 2 ^ L := Classical.not_not.1 (fun h => hng (Or.inl h))
  have hne_esc : ¬ ∃ u, EscV (x := x) M hL (encV (n := x.length) (M.initB hL)) u :=
    fun h => hng (Or.inr h)
  obtain ⟨hRu, hH, hih⟩ := hW
  set lr := List.replicate L (rInit₀ M)
  have hlr : lr.length = L := List.length_replicate
  have hrec : ∀ g ∈ lr, isRec g = true := fun g hg => by
    rw [List.eq_of_mem_replicate hg]; rfl
  obtain ⟨T₁, s1, hF₂₁, hRu₁, hih₁, hCU0₁, hCU1₁, ag1, hW₁⟩ :=
    Spec.fitTest (x := x) hrec (by rw [hlr]; exact hL) hRu (hH tCU (by decide)) hih hT
      (by have := Nat.le_mul_of_pos_left (L + 1) (show 0 < nR Λ Γ * L + 1 by omega); omega)
  have hH₁ : AllHome T₁ := by
    intro i hi
    by_cases h : i = tCU
    · subst h; exact ⟨hCU0₁, hCU1₁⟩
    · have hnot : ¬ (i = tCU ∨ i = tF ∨ i = tF₂) := by
        rintro (rfl | rfl | rfl)
        · exact h rfl
        · revert hi; decide
        · revert hi; decide
      exact ⟨by rw [(ag1 i hnot).1]; exact (hH i hi).1,
        by rw [(ag1 i hnot).2]; exact (hH i hi).2⟩
  have hcF₂ : Cond.eval x T₁ (.tape tF₂ (fun g => decide (g = (Sym.yes : Sym Λ Γ)))) = true := by
    rw [hlr] at hF₂₁; simp [Cond.eval, hF₂₁, hfit]
  obtain ⟨T₂, s2, hRep₂, hRegs₂, hRu₂, hih₂, hW₂⟩ :=
    Spec.setupWidth (x := x) M hL hfit hRu₁ hH₁ hih₁ hW₁
      (by have := Nat.le_mul_of_pos_left (L + 1) (show 0 < nR Λ Γ * L + 1 by omega); omega)
  obtain ⟨T₃, r₃, s3, hRep₃, ⟨v', hRegs₃⟩, hEsc₃, hAcc₃, hEhd₃, hAhd₃, ag3, hW₃⟩ :=
    Spec.vLoop (x := x) M hL hfit Nat.lt_two_pow_self (nV_le_two_pow L)
      (encV (n := x.length) (M.initB hL)) hB hRep₂ hRegs₂ hW₂
  have hRu₃ := agree_lay ag3 (by decide) hRu₂
  have hH₃ : AllHome T₃ := allHome_of_rep_regs hRep₃ hRegs₃
  have hreadEsc₃ : T₃.read tEsc = .no := by
    rw [Tapes.read, hEhd₃, hEsc₃, ite_neg' hne_esc]
  have hreadAcc₃ : T₃.read tAcc = (if M.Accepts x then .yes else .no) := by
    rw [Tapes.read, hAhd₃, hAcc₃]
    exact if_congr (accV_iff_accepts M hL hng) rfl rfl
  have s4 := Spec.resetIn (x := x) (T := T₃) (rep_ih_le hRep₃) hW₃
  set T₄ : Tapes NT (Sym Λ Γ) := { T₃ with ih := 0 }
  have hcEsc : Cond.eval x T₄ (.tape tEsc (fun g => decide (g = (Sym.yes : Sym Λ Γ)))) = false := by
    show decide (T₃.read tEsc = .yes) = false
    simp [hreadEsc₃]
  refine ⟨T₄, s1.seq (Spec.ifElse_true hcF₂ hW₁ (((s2.seq s3).seq s4).seq
    (Spec.ifElse_false hcEsc hW₃ (Spec.nil hW₃)))), ⟨hRu₃, hH₃, rfl⟩,
    hreadEsc₃, hreadAcc₃, hW₃⟩

/-! ### The outer width-search loop -/

noncomputable def wLoop [NeZero (nR Λ Γ)] (M : NTM Λ Γ) : Code NT (Sym Λ Γ) :=
  whileDo (.tape tEsc (fun g => decide (g = .yes))) (wBody M)

open Classical in
theorem wloop_aux [NeZero (nR Λ Γ)] (M : NTM Λ Γ) {L_max : ℕ} (hLm : 0 < L_max)
    (hstop : ¬ NeedsGrow M x L_max hLm)
    (hB : (nR Λ Γ * L_max + 1) * (L_max + 1) + nR Λ Γ * L_max + 8 ≤ B) :
    ∀ (m L : ℕ), 0 < L → L ≤ L_max → L_max - L = m →
      ∀ (T : Tapes NT (Sym Λ Γ)), WInv M L T → T.read tEsc = .yes → T.Within B →
      ∃ T', Loop (.tape tEsc (fun g => decide (g = (Sym.yes : Sym Λ Γ)))) (wBody M) x B T T' ∧
        T'.read tAcc = (if M.Accepts x then .yes else .no) ∧ T'.Within B
  | m, L, hL, hle, hm, T, hW, hEsc, hT => by
    have : NeZero (nV Λ Γ L) := ⟨Nat.ne_of_gt (nV_pos M L)⟩
    have hBL : (nR Λ Γ * L + 1) * (L + 1) + nR Λ Γ * L + 8 ≤ B := by
      have h1 : nR Λ Γ * L + 1 ≤ nR Λ Γ * L_max + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hle) 1
      have h2 : (nR Λ Γ * L + 1) * (L + 1) ≤ (nR Λ Γ * L_max + 1) * (L_max + 1) :=
        Nat.mul_le_mul h1 (Nat.add_le_add_right hle 1)
      have h3 : nR Λ Γ * L ≤ nR Λ Γ * L_max := Nat.mul_le_mul_left _ hle
      omega
    have hc : Cond.eval x T (.tape tEsc (fun g => decide (g = (Sym.yes : Sym Λ Γ)))) = true := by
      simp [Cond.eval, hEsc]
    by_cases hng : NeedsGrow M x L hL
    · cases m with
      | zero =>
        have hEq : L = L_max := by omega
        subst hEq
        exact absurd hng hstop
      | succ m' =>
        obtain ⟨T₁, s1, hW₁, hEsc₁, hW₁'⟩ :=
          Spec.wBody_grow (x := x) M hL hng hW hT hBL
        obtain ⟨T', hl, hAcc', hW'⟩ :=
          wloop_aux M hLm hstop hB m' (L + 1) (by omega) (by omega) (by omega) T₁ hW₁ hEsc₁ hW₁'
        exact ⟨T', .iter hc hT s1 hl, hAcc', hW'⟩
    · obtain ⟨T₁, s1, _, hEsc₁, hAcc₁, hW₁'⟩ :=
        Spec.wBody_stop (x := x) M hL hng hW hT hBL
      refine ⟨T₁, .iter hc hT s1 (.stop ?_ hW₁'), hAcc₁, hW₁'⟩
      simp [Cond.eval, hEsc₁]

/-! ### Initializing from blank tapes -/

def initTape (t : Fin NT) : Code NT (Sym Λ Γ) :=
  [Instr.write t .mk] ++ [Instr.move t .right]

def initTapes : List (Fin NT) → Code NT (Sym Λ Γ)
  | [] => []
  | t :: ts => initTape t ++ initTapes ts

theorem Spec.initTapes (hB : 2 ≤ B) :
    ∀ (ts : List (Fin NT)) {T : Tapes NT (Sym Λ Γ)},
      ts.Nodup → (∀ t ∈ ts, T.hd t = 0) → T.Within B →
      ∃ T', Spec (Edge.initTapes (Λ := Λ) (Γ := Γ) ts) x B T T' ∧
        (∀ t ∈ ts, T'.tp t 0 = .mk ∧ T'.hd t = 1 ∧ ∀ j, 0 < j → T'.tp t j = T.tp t j) ∧
        T.Agree (fun i => i ∈ ts) T' ∧ T'.ih = T.ih ∧ T'.Within B
  | [], T, _, _, hT =>
    ⟨T, Spec.nil hT, fun _ h => absurd h List.not_mem_nil, Tapes.Agree.refl _ T, rfl, hT⟩
  | t :: ts, T, hnd, hhd, hT => by
    have ht0 : T.hd t = 0 := hhd t List.mem_cons_self
    have s1 := Spec.write (x := x) (t := t) (g := (Sym.mk : Sym Λ Γ)) hT
    have hW₁ := Tapes.within_write (t := t) (g := (Sym.mk : Sym Λ Γ)) hT
    have s2 := Spec.moveRight (x := x) (t := t) hW₁ (by simp [ht0]; omega)
    set T₁ := (T.write t .mk).setHead t ((T.write t .mk).hd t + 1)
    have hW₂ : T₁.Within B := Tapes.within_setHead hW₁ (by simp [ht0]; omega)
    have hnotin : ∀ q ∈ ts, q ≠ t := fun q hq e =>
      (List.nodup_cons.1 hnd).1 (e ▸ hq)
    obtain ⟨T₂, s3, hpost, ag2, ih2, hW₃⟩ :=
      Spec.initTapes hB ts (List.nodup_cons.1 hnd).2
        (fun q hq => by
          simp only [T₁, Tapes.setHead_hd_ne _ _ (hnotin q hq), Tapes.write_hd]
          exact hhd q (List.mem_cons_of_mem _ hq))
        hW₂
    refine ⟨T₂, (s1.seq s2).seq s3, ?_, ?_, ih2, hW₃⟩
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · have g := ag2 q (List.nodup_cons.1 hnd).1
        refine ⟨?_, ?_, ?_⟩
        · rw [g.1]; simp [T₁, Tapes.write_tp_self, ht0]
        · rw [g.2]; simp [T₁, ht0]
        · intro j hj
          rw [g.1]; simp only [T₁, Tapes.setHead_tp, Tapes.write_tp_self, ht0]
          rw [ite_neg' (by omega)]
      · obtain ⟨p1, p2, p3⟩ := hpost q hq
        refine ⟨p1, p2, fun j hj => ?_⟩
        rw [p3 j hj]
        simp [T₁, Tapes.write, hnotin q hq]
    · intro i hi
      have hit : i ≠ t := fun e => hi (e ▸ List.mem_cons_self)
      have hits : i ∉ ts := fun h => hi (List.mem_cons_of_mem _ h)
      exact ⟨(ag2 i hits).1.trans (by simp [T₁, Tapes.write, hit]),
        (ag2 i hits).2.trans (by simp [T₁, Tapes.setHead_hd_ne _ _ hit])⟩

noncomputable def savitchBody [NeZero (nR Λ Γ)] (M : NTM Λ Γ) : Code NT (Sym Λ Γ) :=
  initTapes (List.finRange NT) ++ [Instr.write tRu (rInit₀ M)] ++
    [Instr.write tEsc .yes] ++ wLoop M

open Classical in
theorem Spec.savitchBody [NeZero (nR Λ Γ)] (M : NTM Λ Γ) {L_max : ℕ} (hLm : 0 < L_max)
    (hstop : ¬ NeedsGrow M x L_max hLm)
    (hB : (nR Λ Γ * L_max + 1) * (L_max + 1) + nR Λ Γ * L_max + 8 ≤ B) :
    ∃ T', Spec (savitchBody M) x B (Tapes.blank .blank) T' ∧
      T'.read tAcc = (if M.Accepts x then .yes else .no) ∧ T'.Within B := by
  have hB2 : 2 ≤ B := by omega
  have hW₀ : (Tapes.blank (Sym.blank : Sym Λ Γ) : Tapes NT (Sym Λ Γ)).Within B :=
    fun _ => by show 0 < B; omega
  obtain ⟨T₁, s1, hpost, _, ih1, hW₁⟩ :=
    Spec.initTapes (Λ := Λ) (Γ := Γ) (x := x) hB2 (List.finRange NT)
      (List.nodup_finRange NT) (fun _ _ => rfl) hW₀
  have hall₁ : ∀ i : Fin NT, T₁.tp i 0 = .mk ∧ T₁.hd i = 1 ∧ ∀ j, 0 < j → T₁.tp i j = .blank :=
    fun i => hpost i (List.mem_finRange i)
  have s2 := Spec.write (x := x) (t := tRu) (g := rInit₀ M) hW₁
  set T₂ := T₁.write tRu (rInit₀ M)
  have hW₂ : T₂.Within B := Tapes.within_write hW₁
  have s3 := Spec.write (x := x) (t := tEsc) (g := (Sym.yes : Sym Λ Γ)) hW₂
  set T₃ := T₂.write tEsc .yes
  have hW₃ : T₃.Within B := Tapes.within_write hW₂
  have hRu₃ : Lay tRu .mk .blank T₃ (List.replicate 1 (rInit₀ M)) := by
    have hRu₁ := hall₁ tRu
    have htp : T₃.tp tRu = T₂.tp tRu := by simp [T₃, Tapes.write, show tRu ≠ tEsc by decide]
    refine ⟨?_, ?_, ?_, by simp [T₃, T₂, hRu₁.2.1]⟩
    · rw [htp]; simp [T₂, Tapes.write_tp_self, hRu₁.2.1, hRu₁.1]
    · rw [htp]; simp [List.replicate, seg, T₂, Tapes.write_tp_self, hRu₁.2.1]
    · rw [htp]; simp only [List.length_replicate, T₂, Tapes.write_tp_self, hRu₁.2.1]
      rw [ite_neg' (by decide), hRu₁.2.2 2 (by decide)]
  have hH₃ : AllHome T₃ := by
    intro i hi
    have hiR : i ≠ tRu := by revert i hi; decide
    have hiE : i ≠ tEsc := by revert i hi; decide
    exact ⟨by simp [T₃, T₂, Tapes.write, hiR, hiE, (hall₁ i).1],
      by simp [T₃, T₂, (hall₁ i).2.1]⟩
  have hWInv₃ : WInv M 1 T₃ := ⟨hRu₃, hH₃, ih1⟩
  have hEsc₃ : T₃.read tEsc = .yes := by simp [T₃, Tapes.read, Tapes.write_tp_self]
  obtain ⟨T', hl, hAcc', hW'⟩ :=
    wloop_aux M hLm hstop hB (L_max - 1) 1 (by decide) (by omega) rfl T₃ hWInv₃ hEsc₃ hW₃
  exact ⟨T', (((s1.seq s2).seq s3).seq (Spec.whileDo hl)), hAcc', hW'⟩

end Savitch.Edge
