import Savitch.Machine.Next

/-!
# Choosing the width: closure under steps

Phase 4b-6 of the Savitch formalization (see `PLAN.md`).

The deterministic machine does not know `s |x|`. It tries widths `L = 1, 2, …` and
stops at the first width at which no reachable bounded configuration has a move
that leaves the block (`Escapes`). This file proves that this is sound and that
it terminates:

* `accepts_iff_gen_closed`: if no configuration reachable within width `L`
  escapes, acceptance is reachability of an accepting vertex along `GEdge`
  (no space bound on `M` needed).
* `no_escape_of_bounded`: if `M` is `s`-space-bounded and `s |x| ≤ L`, nothing
  escapes, so the search stops by width `max (s |x|) _`.
-/

set_option linter.unusedSectionVars false

namespace Savitch.Machine

namespace NTM

open Machine (Dir inputSym moveIn moveWork)

variable {Λ Γ : Type} [Fintype Λ] [Fintype Γ] [DecidableEq Λ] [DecidableEq Γ]
variable (M : NTM Λ Γ) {n L : ℕ}

/-- Some move of `M` from `b` leaves the block. -/
def Escapes (x : List Bool) (b : BCfg Λ Γ x.length L) : Prop :=
  ∃ t ∈ M.δ b.1 (inputSym x b.2.1) (b.2.2.2 b.2.2.1), nextB b t = none

theorem nextB_toCfg (x : List Bool) {b b' : BCfg Λ Γ x.length L} {t : Λ × Γ × Dir × Dir}
    (h : nextB b t = some b') : M.toCfg b' = (M.toCfg b).next x t := by
  obtain ⟨q, ih, wh, tape⟩ := b
  obtain ⟨q₂, g₂, di, dw⟩ := t
  simp only [nextB] at h
  split_ifs at h with hlt
  simp only [Option.some.injEq] at h
  subst h
  apply Cfg.ext
  · rfl
  · rfl
  · rfl
  · funext j
    simp only [toCfg, Cfg.next, Function.update_apply]
    by_cases hjL : j < L
    · simp only [hjL, ↓reduceDIte]
      by_cases hj : j = wh.val
      · have : (⟨j, hjL⟩ : Fin L) = wh := Fin.ext hj
        simp [hj]
      · have : (⟨j, hjL⟩ : Fin L) ≠ wh := fun e => hj (by rw [← e])
        simp [this, hj]
    · have : j ≠ wh.val := fun e => hjL (e ▸ wh.isLt)
      simp [hjL, this]

/-- If no reachable configuration escapes, every reachable configuration of `M`
is represented in width `L`. -/
theorem reach_closed (x : List Bool) (hL : 0 < L)
    (hne : ∀ b, Relation.ReflTransGen (M.BStep x) (M.initB (n := x.length) hL) b →
      ¬ M.Escapes x b) :
    ∀ d, Relation.ReflTransGen (M.Step x) M.init d →
      ∃ b : BCfg Λ Γ x.length L, M.toCfg b = d ∧
        Relation.ReflTransGen (M.BStep x) (M.initB hL) b := by
  intro d hd
  induction hd with
  | refl => exact ⟨_, M.toCfg_initB hL, .refl⟩
  | @tail c d _ hstep ih =>
    obtain ⟨b, rfl, hpath⟩ := ih
    obtain ⟨t, ht, rfl⟩ := hstep
    have hread : (M.toCfg b).tape (M.toCfg b).wh = b.2.2.2 b.2.2.1 := M.toCfg_tape_lt _ _
    cases hn : nextB b t with
    | none =>
      exact absurd ⟨t, by rw [← hread]; exact ht, hn⟩ (hne b hpath)
    | some b' =>
      refine ⟨b', M.nextB_toCfg x hn, hpath.tail ?_⟩
      exact (M.bstep_iff_nextB x b b').2 ⟨t, by rw [← hread]; exact ht, hn⟩

/-- **Acceptance at a closed width.** -/
theorem accepts_iff_gen_closed (x : List Bool) (hL : 0 < L) (hih : x.length + 1 < 2 ^ L)
    (hne : ∀ b, Relation.ReflTransGen (M.BStep x) (M.initB (n := x.length) hL) b →
      ¬ M.Escapes x b) :
    M.Accepts x ↔ ∃ v : Fin (nV Λ Γ L), (decV (n := x.length) hL v).1 = M.accept ∧
      Relation.ReflTransGen (M.GEdge x hL) (encV (n := x.length) (M.initB hL)) v := by
  have hbnd : M.Accepts x ↔ ∃ b : BCfg Λ Γ x.length L,
      b.1 = M.accept ∧ Relation.ReflTransGen (M.BStep x) (M.initB hL) b := by
    constructor
    · rintro ⟨d, hd, hacc⟩
      obtain ⟨b, rfl, hp⟩ := M.reach_closed x hL hne d hd
      exact ⟨b, hacc, hp⟩
    · rintro ⟨b, hacc, hp⟩
      have : Relation.ReflTransGen (M.Step x) (M.toCfg (M.initB hL)) (M.toCfg b) :=
        hp.lift M.toCfg (fun _ _ h => h)
      rw [M.toCfg_initB] at this
      exact ⟨_, this, hacc⟩
  rw [hbnd]
  constructor
  · rintro ⟨b, hacc, hp⟩
    refine ⟨encV b, by rw [decV_encV hL hih]; exact hacc, ?_⟩
    have : Relation.ReflTransGen (M.GEdge x hL) (encV (M.initB hL)) (encV b) :=
      hp.lift encV (fun a b h => ⟨b, by rw [decV_encV hL hih]; exact h, rfl⟩)
    exact this
  · rintro ⟨v, hacc, hp⟩
    have key : ∀ w, Relation.ReflTransGen (M.GEdge x hL) (encV (n := x.length) (M.initB hL)) w →
        ∃ b : BCfg Λ Γ x.length L, w = encV b ∧ Relation.ReflTransGen (M.BStep x) (M.initB hL) b := by
      intro w hw
      induction hw with
      | refl => exact ⟨_, rfl, .refl⟩
      | tail _ hstep ih =>
        obtain ⟨b, rfl, hpath⟩ := ih
        obtain ⟨b', hb', rfl⟩ := hstep
        rw [decV_encV hL hih] at hb'
        exact ⟨b', rfl, hpath.tail hb'⟩
    obtain ⟨b, rfl, hpath⟩ := key v hp
    rw [decV_encV hL hih] at hacc
    exact ⟨b, hacc, hpath⟩

/-- **Termination of the width search.** A space-bounded machine never escapes a
block at least as wide as its space bound. -/
theorem no_escape_of_bounded {s : ℕ → ℕ} (hM : M.SpaceBounded s) (x : List Bool) (hL : 0 < L)
    (hsL : s x.length ≤ L) :
    ∀ b, Relation.ReflTransGen (M.BStep x) (M.initB (n := x.length) hL) b → ¬ M.Escapes x b := by
  intro b hb ⟨t, ht, hn⟩
  have hreach : Relation.ReflTransGen (M.Step x) M.init (M.toCfg b) := by
    have : Relation.ReflTransGen (M.Step x) (M.toCfg (M.initB hL)) (M.toCfg b) :=
      hb.lift M.toCfg (fun _ _ h => h)
    rwa [M.toCfg_initB] at this
  have hread : (M.toCfg b).tape (M.toCfg b).wh = b.2.2.2 b.2.2.1 := M.toCfg_tape_lt _ _
  have hstep : M.Step x (M.toCfg b) ((M.toCfg b).next x t) := ⟨t, by rw [hread]; exact ht, rfl⟩
  have := hM x _ (hreach.tail hstep)
  obtain ⟨q₂, g₂, di, dw⟩ := t
  simp only [nextB] at hn
  split_ifs at hn with hlt
  simp only [Cfg.next, toCfg] at this
  omega

end NTM

end Savitch.Machine
