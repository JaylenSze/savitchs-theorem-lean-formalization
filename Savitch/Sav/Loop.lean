import Savitch.Sav.Body

/-!
# The Savitch main loop

Phase 4b-5 of the Savitch formalization (see `PLAN.md`).

* `body M`: dispatch on the mode cell; `Spec.body_step` shows one iteration
  performs one step of the generic Phase 2 machine.
* `mainLoop M`: iterate `body M` until the mode is `done`; `loop_done` shows that,
  from a state whose Phase 2 run halts with answer `r`, the loop exits with the
  mode cell reading `done r`.
-/

set_option linter.unusedSectionVars false

namespace Savitch.Edge

open TM Machine Machine.NTM

variable {Λ Γ : Type} [Fintype Λ] [Fintype Γ] [DecidableEq Λ] [DecidableEq Γ]
variable {x : List Bool} {B : ℕ} {L : ℕ}

/-- One iteration: dispatch on the mode cell. -/
noncomputable def body [NeZero (nR Λ Γ)] (M : NTM Λ Γ) : Code NT (Sym Λ Γ) :=
  TM.cases tMd (fun g => match g with
    | .md .call => callCode M
    | .md (.ret r) => retCode r
    | _ => []) Finset.univ.toList

def notDone : Sym Λ Γ → Bool
  | .md (.done _) => false
  | _ => true

/-- The main loop. -/
noncomputable def mainLoop [NeZero (nR Λ Γ)] (M : NTM Λ Γ) : Code NT (Sym Λ Γ) :=
  whileDo (.tape tMd notDone) (body M)

theorem stack_len_le {K : ℕ} {s : Gen.State (nV Λ Γ L)} (hD : Gen.DepthInv K s) :
    s.stack.length ≤ K := by
  cases s with
  | call _ _ _ st => exact Gen.stackOK_length hD.1
  | ret _ st => exact Gen.stackOK_length hD
  | done _ => exact Nat.zero_le _

theorem Spec.body_step [NeZero (nV Λ Γ L)] [NeZero (nR Λ Γ)] (M : NTM Λ Γ) (hL : 0 < L)
    (hfit : x.length + 1 < 2 ^ L) {K WK : ℕ} (hWK : K < 2 ^ WK) {s : Gen.State (nV Λ Γ L)}
    (hs : ∀ r, s ≠ .done r) {T : Tapes NT (Sym Λ Γ)} (hR : Rep L x K WK T s)
    (hD : Gen.DepthInv K s) (hT : T.Within B) (hB : (K + 1) * (L + 1) + WK + 8 ≤ B) :
    ∃ T', Spec (body M) x B T T' ∧ Rep L x K WK T' (Gen.step (EO M x hL) s) ∧ T.Agree Lo T' ∧
      T'.Within B := by
  have hlen := stack_len_le hD
  have hKL : (s.stack.length + 1) * L ≤ (K + 1) * L := Nat.mul_le_mul_right _ (by omega)
  have hKL' : (K + 1) * L + K + 1 ≤ (K + 1) * (L + 1) := by rw [Nat.mul_succ]; omega
  cases s with
  | done r => exact absurd rfl (hs r)
  | call k a b st =>
    have hmd : T.read tMd = .md .call := hR.1
    have key : ∀ T', Spec (callCode M) x B T T' → Spec (body M) x B T T' := fun T' h =>
      Spec.cases tMd _ Finset.univ.toList (by simp) hT (by rw [hmd]; exact h)
    cases k with
    | zero =>
      obtain ⟨T', h, hR', ag, _, hW⟩ := Spec.call_zero (B := B) M hL hfit hR hD hT
        (by have := Nat.le_mul_of_pos_left (L + 1) (show 0 < K + 1 by omega); omega)
      exact ⟨T', key T' h, hR', ag.mono (by decide), hW⟩
    | succ k =>
      obtain ⟨T', h, hR', ag, hW⟩ := Spec.call_succ (B := B) M hL hR hT
        (by simp only [Gen.State.stack] at hKL hlen; omega)
      exact ⟨T', key T' h, hR', ag, hW⟩
  | ret r st =>
    have hmd : T.read tMd = .md (.ret r) := hR.1
    have key : ∀ T', Spec (retCode r) x B T T' → Spec (body M) x B T T' := fun T' h =>
      Spec.cases tMd _ Finset.univ.toList (by simp) hT (by rw [hmd]; exact h)
    cases st with
    | nil =>
      obtain ⟨T', h, hR', ag, hW⟩ := Spec.ret_nil (B := B) M hL hR hT
      exact ⟨T', key T' h, hR', ag, hW⟩
    | cons f st =>
      obtain ⟨k, a, b, c, ph⟩ := f
      simp only [Gen.State.stack, List.length_cons] at hKL hlen
      have h3 : (st.length + 1) * L ≤ (K + 1) * L := Nat.mul_le_mul_right _ (by omega)
      cases r with
      | true =>
        cases ph with
        | left =>
          obtain ⟨T', h, hR', ag, hW⟩ := Spec.ret_true_left (B := B) M hL hR hT (by omega)
          exact ⟨T', key T' h, hR', ag, hW⟩
        | right =>
          obtain ⟨T', h, hR', ag, hW⟩ := Spec.ret_true_right (B := B) M hL hR hD hWK hT
            (by have := Nat.le_mul_of_pos_left (L + 1) (show 0 < K + 1 by omega); omega)
          exact ⟨T', key T' h, hR', ag, hW⟩
      | false =>
        obtain ⟨T', h, hR', ag, hW⟩ := Spec.advCode (B := B) hR hD hWK hT (by omega)
        have hNe : ((⟨k, a, b, c, ph⟩ :: st : List (GF Λ Γ L)).map phBit).reverse ≠ [] := by simp
        have hSP' := phLay_cons hR.2.2.2.2.1.2.2.2
        refine ⟨T', key T' (Spec.emptyBranch hR.2.2.2.2.1.2.2.2 hT (by
          rw [ite_neg' hNe]
          exact Spec.phBranch hSP' hT (by cases ph <;> exact h))), ?_, ag, hW⟩
        cases ph <;> exact hR'

/-- **The main loop.** From a represented state whose Phase 2 run halts with
answer `r`, the loop terminates with the mode cell reading `done r`. -/
theorem loop_done [NeZero (nV Λ Γ L)] [NeZero (nR Λ Γ)] (M : NTM Λ Γ) (hL : 0 < L)
    (hfit : x.length + 1 < 2 ^ L) {K WK : ℕ} (hWK : K < 2 ^ WK)
    (hB : (K + 1) * (L + 1) + WK + 8 ≤ B) (r : Bool) :
    ∀ s : Gen.State (nV Λ Γ L),
      Relation.ReflTransGen (Gen.StepRel (EO M x hL)) s (.done r) →
      ∀ T : Tapes NT (Sym Λ Γ), Rep L x K WK T s → Gen.DepthInv K s → T.Within B →
      ∃ T', Loop (.tape tMd notDone) (body M) x B T T' ∧ Rep L x K WK T' (.done r) ∧
        T.Agree Lo T' := by
  intro s hs
  induction hs using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro T hR _ hT
    have h : T.read tMd = .md (.done r) := hR.1
    exact ⟨T, .stop (by simp [Cond.eval, h, notDone]) hT, hR, Tapes.Agree.refl _ T⟩
  | @head s s' hstep _ ih =>
    intro T hR hD hT
    by_cases hdone : ∃ r', s = .done r'
    · obtain ⟨r', rfl⟩ := hdone
      have : s' = .done r' := hstep.symm
      subst this
      exact ih T hR hD hT
    · push Not at hdone
      obtain ⟨T', h, hR', ag, hW⟩ := Spec.body_step (B := B) M hL hfit hWK hdone hR hD hT hB
      have hc : Cond.eval x T (.tape tMd notDone) = true := by
        cases s with
        | done r' => exact absurd rfl (hdone r')
        | call _ _ _ _ => simp [Cond.eval, hR.1, notDone]
        | ret _ _ => simp [Cond.eval, hR.1, notDone]
      rw [← hstep] at ih
      obtain ⟨T'', hl, hr, ag'⟩ := ih T' hR' (Gen.depthInv_step _ hD) hW
      exact ⟨T'', .iter hc hT h hl, hr, ag.trans ag'⟩

end Savitch.Edge
