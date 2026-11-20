import Savitch.Outer.WLoop

/-!
# Savitch's Theorem: `NSPACE(s) ⊆ DSPACE(s²)`

Phase 4b-7 of the Savitch formalization (see `PLAN.md`).

We attach a halting branch (`withHalt`) to `savitchBody M`, obtaining the complete
tape program `savitchCode M`. For any `s`-space-bounded NTM `M` with `s n ≥ log₂ n`,
`savitchCode M` decides `M`'s language on `NT = 32` work tapes while keeping every
work head below `O(s(|x|)² + 1)` on every reachable configuration. By
`Code.mem_DSPACE`, this compiles to a deterministic multi-tape Turing machine and
proves `NSPACE s ⊆ DSPACE (fun n => s n ^ 2)`.
-/

set_option linter.unusedSectionVars false

namespace Savitch.Edge

open TM Machine Machine.NTM

variable {Λ Γ : Type} [Fintype Λ] [Fintype Γ] [DecidableEq Λ] [DecidableEq Γ]

/-! ### Halting with the answer in a flag cell -/

def withHalt {k : ℕ} {Γ' : Type} [DecidableEq Γ'] (c : Code k Γ') (t : Fin k) (yes : Γ') :
    Code k Γ' :=
  c ++ [Cond.jmp 2 (.tape t (fun g => decide (g = yes)))] ++ [Instr.halt false] ++
    [Instr.halt true]

theorem Spec.withHalt {k : ℕ} {Γ' : Type} [DecidableEq Γ'] {c : Code k Γ'} {t : Fin k}
    {yes no : Γ'} (hyn : yes ≠ no) {x : List Bool} {B : ℕ} {T₀ T' : Tapes k Γ'} {b : Bool}
    (h : Spec c x B T₀ T') (hread : T'.read t = if b then yes else no) :
    Seg (Edge.withHalt c t yes) x B 0 (Edge.withHalt c t yes).length
      (.run 0 T₀) (.halted b T') := by
  have hs := SubAt.self (Edge.withHalt c t yes)
  unfold Edge.withHalt at hs
  have hj := hs.left.left.right.single
  have hf := hs.left.right.single
  have ht := hs.right.single
  have h0 := Spec.embed hs.left.left.left h
  have hW' : T'.Within B := h.target_within
  unfold Edge.withHalt
  simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one,
    zero_add] at hj hf ht h0 ⊢
  refine (h0.mono le_rfl (by omega)).trans ?_
  cases b with
  | false =>
    have hc : Cond.eval x T' (.tape t (fun g => decide (g = yes))) = false := by
      simp [Cond.eval, hread, Ne.symm hyn]
    refine .step (by omega) (by omega) hW' ?_
    simp only [Code.step, hj, Cond.exec_jmp, hc, Bool.false_eq_true, ↓reduceIte]
    refine .step (by omega) (by omega) hW' ?_
    simp only [Code.step, hf, Instr.exec]
    exact .refl hW'
  | true =>
    have hc : Cond.eval x T' (.tape t (fun g => decide (g = yes))) = true := by
      simp [Cond.eval, hread]
    refine .step (by omega) (by omega) hW' ?_
    simp only [Code.step, hj, Cond.exec_jmp, hc, ↓reduceIte]
    rw [show (c.length : ℤ) + 2 = (c.length : ℤ) + 1 + 1 by omega]
    refine .step (by omega) (by omega) hW' ?_
    simp only [Code.step, ht, Instr.exec]
    exact .refl hW'

/-! ### The complete Savitch program and its space bound -/

noncomputable def savitchCode [NeZero (nR Λ Γ)] (M : NTM Λ Γ) : Code NT (Sym Λ Γ) :=
  withHalt (savitchBody M) tAcc .yes

theorem space_poly_bound (r c S : ℕ) :
    (r * ((c + 2) * (S + 1)) + 1) * ((c + 2) * (S + 1) + 1) + r * ((c + 2) * (S + 1)) + 8 ≤
      3 * ((r * (c + 2) + 1) * (c + 3) + (r * (c + 2) + 8)) * (S ^ 2 + 1) := by
  set D := c + 2
  set T := S + 1
  set L_max := D * T
  have hT : 1 ≤ T := by omega
  have h1 : r * L_max + 1 ≤ (r * D + 1) * T := by
    have : (r * D + 1) * T = r * L_max + T := by simp only [L_max]; ring
    omega
  have h2 : L_max + 1 ≤ (D + 1) * T := by
    have : (D + 1) * T = L_max + T := by simp only [L_max]; ring
    omega
  have h3 : r * L_max + 8 ≤ (r * D + 8) * T ^ 2 := by
    have hT2 : T ≤ T ^ 2 := Nat.le_self_pow (by decide) T
    have hmul : (r * D + 8) * T ≤ (r * D + 8) * T ^ 2 := Nat.mul_le_mul_left _ hT2
    have : (r * D + 8) * T = r * L_max + 8 * T := by simp only [L_max]; ring
    omega
  have h4 : (r * L_max + 1) * (L_max + 1) ≤ (r * D + 1) * (D + 1) * T ^ 2 := by
    calc (r * L_max + 1) * (L_max + 1)
        ≤ ((r * D + 1) * T) * ((D + 1) * T) := Nat.mul_le_mul h1 h2
      _ = (r * D + 1) * (D + 1) * T ^ 2 := by ring
  have h5 : (r * L_max + 1) * (L_max + 1) + r * L_max + 8 ≤
      ((r * D + 1) * (D + 1) + (r * D + 8)) * T ^ 2 := by
    have : ((r * D + 1) * (D + 1) + (r * D + 8)) * T ^ 2 =
        (r * D + 1) * (D + 1) * T ^ 2 + (r * D + 8) * T ^ 2 := by ring
    omega
  have hS : S ≤ S ^ 2 := Nat.le_self_pow (by decide) S
  have hT2_le : T ^ 2 ≤ 3 * (S ^ 2 + 1) := by
    have : T ^ 2 = S ^ 2 + 2 * S + 1 := by simp only [T]; ring
    omega
  calc (r * L_max + 1) * (L_max + 1) + r * L_max + 8
      ≤ ((r * D + 1) * (D + 1) + (r * D + 8)) * T ^ 2 := h5
    _ ≤ ((r * D + 1) * (D + 1) + (r * D + 8)) * (3 * (S ^ 2 + 1)) :=
        Nat.mul_le_mul_left _ hT2_le
    _ = 3 * ((r * D + 1) * (c + 3) + (r * D + 8)) * (S ^ 2 + 1) := by
        simp only [D]; ring

theorem fit_of_log {s : ℕ → ℕ} (hlog : ∀ n, Nat.log 2 n ≤ s n) (c n : ℕ) :
    n + 1 < 2 ^ ((c + 2) * (s n + 1)) := by
  have h1 := Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  have h2 : 2 ^ (Nat.log 2 n).succ ≤ 2 ^ (s n + 1) :=
    Nat.pow_le_pow_right (by decide) (by have := hlog n; omega)
  have h3 : 2 ^ (s n + 2) = 2 * 2 ^ (s n + 1) := by ring
  have h4 := Nat.two_pow_pos (s n + 1)
  have h5 : n + 1 < 2 ^ (s n + 2) := by omega
  have h6 : 2 ^ (s n + 2) ≤ 2 ^ ((c + 2) * (s n + 1)) := by
    apply Nat.pow_le_pow_right (by decide)
    have : (c + 2) * (s n + 1) = c * (s n + 1) + 2 * s n + 2 := by ring
    omega
  exact lt_of_lt_of_le h5 h6

end Savitch.Edge

namespace Savitch

open TM Machine Machine.NTM Edge

/-- **Savitch's Theorem.**

For any space function `s(n) ≥ log₂ n`, every language in `NSPACE(s(n))` is in
`DSPACE(s(n)²)`. No space-constructibility assumption on `s` is required. -/
theorem savitch_theorem {s : ℕ → ℕ} (hlog : ∀ n, Nat.log 2 n ≤ s n) :
    NSPACE s ⊆ DSPACE (fun n => s n ^ 2) := by
  intro L ⟨Λ, Γ, iΛ, iΓ, M, c, hM, hLM⟩
  classical
  have : NeZero (nR Λ Γ) := ⟨Nat.ne_of_gt (nR_pos M)⟩
  set K_c := 3 * ((nR Λ Γ * (c + 2) + 1) * (c + 3) + (nR Λ Γ * (c + 2) + 8))
  have run_x : ∀ x : List Bool,
      ∃ T', Seg (savitchCode M) x (K_c * (s x.length ^ 2 + 1)) 0 (savitchCode M).length
        (.run 0 (Tapes.blank .blank)) (.halted (decide (M.Accepts x)) T') := by
    intro x
    set L_max := (c + 2) * (s x.length + 1)
    have hLm : 0 < L_max := Nat.mul_pos (by omega) (by omega)
    have hsL : c * (s x.length + 1) ≤ L_max := by
      have : L_max = c * (s x.length + 1) + 2 * (s x.length + 1) := by simp only [L_max]; ring
      omega
    have hfit : x.length + 1 < 2 ^ L_max := fit_of_log hlog c x.length
    have hstop : ¬ NeedsGrow M x L_max hLm :=
      not_needsGrow_of_bounded M hM hLm hsL hfit
    have hB : (nR Λ Γ * L_max + 1) * (L_max + 1) + nR Λ Γ * L_max + 8 ≤
        K_c * (s x.length ^ 2 + 1) :=
      space_poly_bound (nR Λ Γ) c (s x.length)
    obtain ⟨T', hbody, hAcc, _⟩ := Spec.savitchBody (x := x) M hLm hstop hB
    have hread : T'.read tAcc = (if decide (M.Accepts x) then .yes else .no) := by
      rw [hAcc]; by_cases h : M.Accepts x <;> simp [h]
    exact ⟨T', Spec.withHalt (fun h => by cases h) hbody hread⟩
  refine Code.mem_DSPACE (savitchCode M) .blank K_c ?_ ?_
  · intro x st hst
    obtain ⟨T', hseg⟩ := run_x x
    exact hseg.reachable rfl st hst
  · intro x
    obtain ⟨T', hseg⟩ := run_x x
    exact ⟨decide (M.Accepts x), T', hseg.toReflTransGen, by simp [hLM x]⟩

end Savitch
