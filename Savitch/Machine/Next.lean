import Savitch.Machine.Encode

/-!
# Successors of bounded configurations, and the generated-edge graph

Phase 4b-4 of the Savitch formalization (see `PLAN.md`).

Instead of *checking* `BStep (dec u) (dec v)`, the Savitch TM will *generate*
each successor of `dec u`, write its canonical encoding on a scratch tape and
compare it with `v`. This file is the pure side of that design.

* `nextB b t`: the bounded configuration after move `t`, or `none` if the work
  head would leave the `L` cells.
* `bstep_iff_nextB`: `BStep b b' ↔ ∃ t ∈ δ …, nextB b t = some b'`.
* `GEdge u v`: `v` is the canonical encoding of some `BStep`-successor of `dec u`.
* `accepts_iff_gen`: acceptance is reachability along `GEdge` from `encV initB`.
-/

set_option linter.unusedSectionVars false

namespace Savitch.Machine

namespace NTM

open Machine (Dir inputSym moveIn moveWork)

variable {Λ Γ : Type} [Fintype Λ] [Fintype Γ] [DecidableEq Λ] [DecidableEq Γ]

theorem moveIn_le (n i : ℕ) (d : Dir) (h : i ≤ n + 1) : moveIn n i d ≤ n + 1 := by
  cases d <;> simp [moveIn] <;> omega

variable {n L : ℕ}

/-- The bounded configuration after move `t`, if the work head stays in range. -/
def nextB (b : BCfg Λ Γ n L) (t : Λ × Γ × Dir × Dir) : Option (BCfg Λ Γ n L) :=
  if h : moveWork b.2.2.1.val t.2.2.2 < L then
    some (t.1,
      ⟨moveIn n b.2.1.val t.2.2.1, by have := moveIn_le n b.2.1.val t.2.2.1 (by omega); omega⟩,
      ⟨moveWork b.2.2.1.val t.2.2.2, h⟩,
      Function.update b.2.2.2 b.2.2.1 t.2.1)
  else none

variable (M : NTM Λ Γ)

theorem toCfg_tape_lt (b : BCfg Λ Γ n L) (j : Fin L) : (M.toCfg b).tape j = b.2.2.2 j := by
  simp [toCfg, j.isLt]

/-- **One step, functionally.** -/
theorem bstep_iff_nextB (x : List Bool) (b b' : BCfg Λ Γ x.length L) :
    M.BStep x b b' ↔ ∃ t ∈ M.δ b.1 (inputSym x b.2.1) (b.2.2.2 b.2.2.1),
      nextB (n := x.length) b t = some b' := by
  obtain ⟨q, ih, wh, tape⟩ := b
  obtain ⟨q', ih', wh', tape'⟩ := b'
  have hread : (M.toCfg (q, ih, wh, tape)).tape (M.toCfg (q, ih, wh, tape)).wh = tape wh :=
    M.toCfg_tape_lt _ wh
  unfold BStep Step
  rw [hread]
  apply exists_congr
  intro t
  apply and_congr_right
  intro _
  obtain ⟨q₂, g₂, di, dw⟩ := t
  simp only [nextB]
  constructor
  · intro h
    have hq := congrArg Cfg.q h
    have hih := congrArg Cfg.ih h
    have hwh := congrArg Cfg.wh h
    have htp := congrArg Cfg.tape h
    simp only [toCfg, Cfg.next] at hq hih hwh htp
    have hlt : moveWork wh.val dw < L := by rw [← hwh]; exact wh'.isLt
    simp only [hlt, ↓reduceDIte]
    congr 1
    refine Prod.ext hq.symm (Prod.ext (Fin.ext hih.symm) (Prod.ext (Fin.ext hwh.symm) ?_))
    funext j
    have := congrFun htp j.val
    simp only [j.isLt, ↓reduceDIte, Function.update_apply] at this
    simp only [Function.update_apply]
    rw [this]
    by_cases hj : j = wh
    · subst hj; simp
    · have : j.val ≠ wh.val := fun e => hj (Fin.ext e)
      simp [hj, this]
  · intro h
    split_ifs at h with hlt
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, hih, hwh, rfl⟩ := h
    apply Cfg.ext
    · rfl
    · simp [toCfg, Cfg.next, ← hih]
    · simp [toCfg, Cfg.next, ← hwh]
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

/-! ### The generated-edge graph -/

/-- `v` is the canonical encoding of a `BStep`-successor of `dec u`. -/
def GEdge (x : List Bool) (hL : 0 < L) (u v : Fin (nV Λ Γ L)) : Prop :=
  ∃ b', M.BStep x (decV (n := x.length) hL u) b' ∧ v = encV b'

/-- **Acceptance as reachability along generated edges.** -/
theorem accepts_iff_gen {s : ℕ → ℕ} (hM : M.SpaceBounded s) (x : List Bool) {L : ℕ}
    (hsL : s x.length ≤ L) (hL : 0 < L) (hih : x.length + 1 < 2 ^ L) :
    M.Accepts x ↔ ∃ v : Fin (nV Λ Γ L), (decV (n := x.length) hL v).1 = M.accept ∧
      Relation.ReflTransGen (M.GEdge x hL) (encV (n := x.length) (M.initB hL)) v := by
  rw [M.accepts_iff_boundedL hM x hsL hL]
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

/-- What the edge-test program must decide, in terms of the decoded source alone. -/
theorem gEdge_iff (x : List Bool) {L : ℕ} (hL : 0 < L) (u v : Fin (nV Λ Γ L)) :
    M.GEdge x hL u v ↔
      ∃ t ∈ M.δ (decV (n := x.length) hL u).1 (inputSym x (decV (n := x.length) hL u).2.1)
          ((decV (n := x.length) hL u).2.2.2 (decV (n := x.length) hL u).2.2.1),
        ∃ b', nextB (decV (n := x.length) hL u) t = some b' ∧ v = encV b' := by
  unfold GEdge
  constructor
  · rintro ⟨b', hb', rfl⟩
    obtain ⟨t, ht, hn⟩ := (M.bstep_iff_nextB x _ _).1 hb'
    exact ⟨t, ht, b', hn, rfl⟩
  · rintro ⟨t, ht, b', hn, rfl⟩
    exact ⟨b', (M.bstep_iff_nextB x _ _).2 ⟨t, ht, hn⟩, rfl⟩

end NTM

end Savitch.Machine
