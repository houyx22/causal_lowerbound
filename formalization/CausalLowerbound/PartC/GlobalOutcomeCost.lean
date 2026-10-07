import CausalLowerbound.PartC.IncidentOutcomeFineHellinger
import CausalLowerbound.PartC.ObservationCountCosts
import CausalLowerbound.PartC.CollisionObservationCost
import CausalLowerbound.PartC.GhostCostUnderCarrier

/-! The measurable global cost for the actual degree-three experiment.
All three small-component contributions are integrable under the true
mixed design, with explicit finite-scale expectation bounds. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d K J Ω : Type*} [Fintype d] [DecidableEq d]
  [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J] [Fintype Ω] {θ : ℝ}

def outcomeGlobalCost (H₀ : DiscreteLaw ℕ) (Q : ℕ) (x₀ : d → ℝ)
    (ℓ r h c N₀ M θ κ a₀ jb t τ w : ℝ) {n : ℕ} (x : Fin n → d → ℝ) : ℝ :=
  outcomeLocalFineConstant Q (Fintype.card d) c N₀ M θ κ * (a₀ * t * jb) ^ 2 *
    ((5 : ℝ) ^ Fintype.card d * ((ℓ / (2 * r)) ^ Fintype.card d) ^ 2 *
      observationSetCount (coordinateBox x₀ (5 * h)) x + globalGhostCost H₀ Q 0 τ x₀ r h x) +
  outcomeLocalCrudeConstant Q (Fintype.card d) c N₀ θ κ * (a₀ * t * jb) ^ 2 *
    (collisionObservationCost x₀ ℓ h x +
      observationSetCount (assignmentTransitionUnion (activeBlocks r h) w x₀ r) x)

theorem outcomeGlobalCost_nonneg (H₀ : DiscreteLaw ℕ) (Q : ℕ) (x₀ : d → ℝ)
    (ℓ r h c N₀ M θ κ a₀ jb t τ w : ℝ) (hr : 0 < r) {n : ℕ} (x : Fin n → d → ℝ) :
    0 ≤ outcomeGlobalCost H₀ Q x₀ ℓ r h c N₀ M θ κ a₀ jb t τ w x := by
  have hf := outcomeLocalFineConstant_nonneg Q (Fintype.card d) c N₀ M θ κ
  have hc := outcomeLocalCrudeConstant_nonneg Q (Fintype.card d) c N₀ θ κ
  have hco := observationSetCount_nonneg (coordinateBox x₀ (5 * h)) x
  have hg := globalGhostCost_nonneg H₀ Q 0 τ (by norm_num) (by norm_num) x₀ r h hr x
  have hp := collisionObservationCost_nonneg x₀ ℓ h x
  have ht := observationSetCount_nonneg (assignmentTransitionUnion (activeBlocks r h) w x₀ r) x
  unfold outcomeGlobalCost
  positivity

theorem outcomeGlobalCost_measurable (H₀ : DiscreteLaw ℕ) (Q : ℕ) (x₀ : d → ℝ)
    (ℓ r h c N₀ M θ κ a₀ jb t τ w : ℝ) (hr : 0 < r) (n : ℕ) :
    Measurable (fun x : Fin n → d → ℝ => outcomeGlobalCost H₀ Q x₀ ℓ r h c N₀ M θ κ a₀ jb t τ w x) := by
  exact (((observationSetCount_measurable (coordinateBox x₀ (5 * h)) measurableSet_Icc).const_mul _).add
    (globalGhostCost_measurable H₀ Q 0 τ (by norm_num) (by norm_num) x₀ r h hr n)).const_mul _ |>.add
      (((collisionObservationCost_measurable x₀ ℓ h n).add
        (observationSetCount_measurable _ (assignmentTransitionUnion_measurable _ w x₀ r))).const_mul _)

theorem outcomeGlobalCost_integrable
    (H₀ : DiscreteLaw ℕ) (Q : ℕ) (x₀ : d → ℝ) (ℓ r h c N₀ M κ a₀ jb t τ w : ℝ)
    (hr : 0 < r) (hrh : r ≤ h) (hw : 0 < w) (hw1 : w ≤ 1)
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (H : K → DiscreteLaw ℕ) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ) :
    Integrable (fun x : Fin n → d → ℝ => outcomeGlobalCost H₀ Q x₀ ℓ r h c N₀ M θ κ a₀ jb t τ w x)
      (mixedCarrierDesign F hθ hθ1 (activeBlocks r h) x₀ r H kernel n) := by
  have hv : volume (coordinateBox x₀ (5 * h)) < ⊤ := by
    rw [coordinateBox_volume]
    exact lt_top_iff_ne_top.mpr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have htvol : volume (assignmentTransitionUnion (activeBlocks r h) w x₀ r) < ⊤ :=
    (active_assignmentTransition_volume w x₀ r h hw hw1 hr hrh).trans_lt
      (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
  have hci := mixedCarrierDesign_observationSetCount_integrable F hθ hθ1 (activeBlocks r h)
    x₀ r H kernel n (coordinateBox x₀ (5 * h)) measurableSet_Icc hv
  have hgi := mixedCarrierDesign_globalGhostCost_integrable H₀ Q τ F hθ hθ1 x₀ r h hr H kernel n
  have hpi := mixedCarrierDesign_collisionObservationCost_integrable F hθ hθ1 (activeBlocks r h)
    x₀ ℓ r h H kernel n
  have hti := mixedCarrierDesign_observationSetCount_integrable F hθ hθ1 (activeBlocks r h)
    x₀ r H kernel n _ (assignmentTransitionUnion_measurable _ w x₀ r) htvol
  exact (((hci.const_mul _).add hgi).const_mul _).add ((hpi.add hti).const_mul _)

theorem outcomeGlobalCost_integral_le [Nonempty d]
    (H₀ : DiscreteLaw ℕ) (q : ℕ) (x₀ : d → ℝ) (ℓ r h c N₀ M κ a₀ jb t τ w : ℝ)
    (hℓ : 0 ≤ ℓ) (hr : 0 < r) (hrh : r ≤ h) (hw : 0 < w) (hw1 : w ≤ 1)
    (s : ℝ) (hs : 0 < s) (hsd : s < (Fintype.card d : ℝ)) (hτ : 0 < τ)
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (H : K → DiscreteLaw ℕ) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω)
    (n : ℕ) (hnr : (n : ℝ) * r ^ Fintype.card d ≤ 1) :
    let D := Fintype.card d
    let F₀ := outcomeLocalFineConstant (q + 1) D c N₀ M θ κ * (a₀ * t * jb) ^ 2
    let C₀ := outcomeLocalCrudeConstant (q + 1) D c N₀ θ κ * (a₀ * t * jb) ^ 2
    let B := (designDensityCeiling d θ : ℝ)
    (∫ x, outcomeGlobalCost H₀ (q + 1) x₀ ℓ r h c N₀ M θ κ a₀ jb t τ w x
      ∂mixedCarrierDesign F hθ hθ1 (activeBlocks r h) x₀ r H kernel n) ≤
      F₀ * ((5 : ℝ) ^ D * ((ℓ / (2 * r)) ^ D) ^ 2 *
        (B * 10 ^ D * ((n : ℝ) * h ^ D)) + globalGhostConstant d q θ s * ((n : ℝ) * h ^ D * τ ^ s)) +
      C₀ * ((n : ℝ) ^ 2 * B ^ 2 * ((10 * h) ^ D * (4 * ℓ) ^ D) +
        (B * (2 * D * (2 : ℝ) ^ (D - 1) * 7 ^ D)) * ((n : ℝ) * h ^ D * w)) := by
  let μ := mixedCarrierDesign F hθ hθ1 (activeBlocks r h) x₀ r H kernel n
  have hh : 0 ≤ h := (hr.trans_le hrh).le
  have hv : volume (coordinateBox x₀ (5 * h)) < ⊤ := by
    rw [coordinateBox_volume]
    exact lt_top_iff_ne_top.mpr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have htvol : volume (assignmentTransitionUnion (activeBlocks r h) w x₀ r) < ⊤ :=
    (active_assignmentTransition_volume w x₀ r h hw hw1 hr hrh).trans_lt
      (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
  have hci := mixedCarrierDesign_observationSetCount_integrable F hθ hθ1 (activeBlocks r h)
    x₀ r H kernel n (coordinateBox x₀ (5 * h)) measurableSet_Icc hv
  have hgi := mixedCarrierDesign_globalGhostCost_integrable H₀ (q + 1) τ F hθ hθ1 x₀ r h hr H kernel n
  have hpi := mixedCarrierDesign_collisionObservationCost_integrable F hθ hθ1 (activeBlocks r h)
    x₀ ℓ r h H kernel n
  have hti := mixedCarrierDesign_observationSetCount_integrable F hθ hθ1 (activeBlocks r h)
    x₀ r H kernel n _ (assignmentTransitionUnion_measurable _ w x₀ r) htvol
  have hF0 := mul_nonneg (outcomeLocalFineConstant_nonneg (q + 1) (Fintype.card d) c N₀ M θ κ) (sq_nonneg (a₀ * t * jb))
  have hC0 := mul_nonneg (outcomeLocalCrudeConstant_nonneg (q + 1) (Fintype.card d) c N₀ θ κ) (sq_nonneg (a₀ * t * jb))
  dsimp only
  unfold outcomeGlobalCost
  have hsplit := integral_add (((hci.const_mul ((5 : ℝ) ^ Fintype.card d * ((ℓ / (2 * r)) ^ Fintype.card d) ^ 2)).add hgi).const_mul
      (outcomeLocalFineConstant (q + 1) (Fintype.card d) c N₀ M θ κ * (a₀ * t * jb) ^ 2))
      ((hpi.add hti).const_mul (outcomeLocalCrudeConstant (q + 1) (Fintype.card d) c N₀ θ κ * (a₀ * t * jb) ^ 2))
  have hsplitFine := integral_add (hci.const_mul ((5 : ℝ) ^ Fintype.card d * ((ℓ / (2 * r)) ^ Fintype.card d) ^ 2)) hgi
  have hsplitCrude := integral_add hpi hti
  simp only [Pi.add_apply] at hsplit hsplitFine hsplitCrude
  rw [hsplit,
    integral_const_mul, integral_const_mul,
    hsplitFine, hsplitCrude,
    integral_const_mul]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left (mixedCarrierDesign_coarse_count_integral_le F hθ hθ1 (activeBlocks r h)
        x₀ r h hh H kernel n) (by positivity))
      (mixedCarrierDesign_globalGhostCost_integral_le H₀ q F hθ hθ1 s hs hsd τ hτ x₀ r h hr hrh H kernel n hnr)) hF0)
    (mul_le_mul_of_nonneg_left (add_le_add
      (mixedCarrierDesign_collisionObservationCost_integral_le F hθ hθ1 (activeBlocks r h) x₀ ℓ r h hℓ hh H kernel n)
      (mixedCarrierDesign_transition_count_integral_le F hθ hθ1 x₀ r h w hr hrh hw hw1 H kernel n)) hC0)

end CausalLowerbound.PartC

