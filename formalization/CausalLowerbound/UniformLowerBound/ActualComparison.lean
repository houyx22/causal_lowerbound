import CausalLowerbound.UniformLowerBound.ActualLocal
import CausalLowerbound.UniformLowerBound.GlobalHellinger

/-! The component argument for the constructed binary families. The full
conditional mixtures factor according to the carrier incidence graph; their
actual joint distributions have a common iid uniform covariate marginal. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.UniformLowerBound
open PartB PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt incidenceComponentFintype physicalComponentFintype
variable {d : Type*} [Fintype d] [DecidableEq d]
variable {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}

def actualComparisonConstant (d : Type*) [Fintype d] (κ : ℝ) (Q : ℕ) : ℝ :=
  componentHellingerConstant ((2 : ℝ) ^ Fintype.card d) (4 * κ ^ 2) Q *
    (10 : ℝ) ^ Fintype.card d * (8 : ℝ) ^ Fintype.card d

theorem actualComparisonConstant_nonneg (κ : ℝ) (hκ : 0 < κ) (Q : ℕ) :
    0 ≤ actualComparisonConstant d κ Q := by
  unfold actualComparisonConstant
  exact mul_nonneg (mul_nonneg
    (componentHellingerConstant_nonneg _ _ (by positivity) _) (by positivity)) (by positivity)

theorem actual_global_hellinger_bound
    (regime : Bool) (Q : ℕ) (hQ : 1 ≤ Q) (x₀ : d → ℝ) (ℓ h a b : ℝ)
    (hℓ : 0 < ℓ) (hℓh : ℓ ≤ h)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) (hκ : 0 < κ)
    (hlegal : ∀ (side : Bool) (ζ : activeBlocks (d := d) ℓ h → Bool),
      (fields regime side (activeBlocks ℓ h) (extendBlockSample (activeBlocks ℓ h) ζ)
        x₀ ℓ h a b).Legal α β γ Lπ L₀ Lτ κ)
    {n : ℕ} (x : Fin n → d → ℝ) (hx : x ∉ largeClusterEvent n Q x₀ ℓ h) :
    (actualSampleConditional regime true (activeBlocks ℓ h) x₀ ℓ h a b hlegal hκ.le x).hellingerSq
      (actualSampleConditional regime false (activeBlocks ℓ h) x₀ ℓ h a b hlegal hκ.le x) ≤
        (componentHellingerConstant ((2 : ℝ)^Fintype.card d) (4*κ^2) Q *
          (a^2*b^2 + (if regime then b^4 else a^4))) * collisionCount x₀ ℓ h x := by
  let S := activeBlocks (d := d) ℓ h
  let inc := fun i (k : S) => x i ∈ carrierBox x₀ ℓ k.val
  let P := fun i ζ => actualKernel regime true S x₀ ℓ h a b (hlegal true) hκ.le (x i) ζ
  let R := fun i ζ => actualKernel regime false S x₀ ℓ h a b (hlegal false) hκ.le (x i) ζ
  let m := fun c : Option (incidenceGraph inc).ConnectedComponent =>
    Fintype.card {i // siteComponent inc i = c}
  let e := fun c : Option (incidenceGraph inc).ConnectedComponent =>
    (Fintype.equivFin {i // siteComponent inc i = c}).symm
  let D := componentHellingerConstant ((2 : ℝ)^Fintype.card d) (4*κ^2) Q *
    (a^2*b^2 + (if regime then b^4 else a^4))
  have hD : 0 ≤ D := by
    apply mul_nonneg (componentHellingerConstant_nonneg _ _ (by positivity) _)
    cases regime <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> positivity
  have hm (c) : m c ≤ Q :=
    component_fiber_small_off_largeCluster n Q hQ x₀ ℓ h hℓ hℓh x hx c
  have hP : ∀ i ζ ζ', (∀ k, inc i k → ζ k = ζ' k) → P i ζ = P i ζ' :=
    fun i ζ ζ' he => actual_kernel_incident_local regime true S x₀ ℓ h a b
      (hlegal true) hκ.le (x i) ζ ζ' he
  have hR : ∀ i ζ ζ', (∀ k, inc i k → ζ k = ζ' k) → R i ζ = R i ζ' :=
    fun i ζ ζ' he => actual_kernel_incident_local regime false S x₀ ℓ h a b
      (hlegal false) hκ.le (x i) ζ ζ' he
  have hsingle (c) (hc : m c ≤ 1) :
      FiniteLaw.restrictedExperiment (fun _ : S => rademacher) P (fun j => (e c j).val) =
        FiniteLaw.restrictedExperiment (fun _ : S => rademacher) R (fun j => (e c j).val) := by
    exact actual_sample_eq_of_card_le_one regime x₀ ℓ h a b hlegal hκ.le hℓ
      (hℓ.trans_le hℓh) hc (fun j => x (e c j).val)
  have hcost (c) :
      (FiniteLaw.restrictedExperiment (fun _ : S => rademacher) P (fun j => (e c j).val)).hellingerSq
        (FiniteLaw.restrictedExperiment (fun _ : S => rademacher) R (fun j => (e c j).val)) ≤ D := by
    exact actual_sample_hellinger_le_cutoff regime x₀ ℓ h a b hlegal hκ hℓ
      (hℓ.trans_le hℓh) ha ha1 hb hb1 Q (hm c) (fun j => x (e c j).val)
  have hh := reindexed_mixture_hellinger_le_orderedAdjCount
    (fun _ : S => rademacher) (fun _ : S => rademacher) inc P R hP hR m e D hD hsingle hcost
  exact hh.trans (mul_le_mul_of_nonneg_left
    (observationGraph_orderedAdjCount_le_collisionCount x₀ ℓ h hℓ hℓh x) hD)

theorem actual_totalVariation_bound
    (regime : Bool) (Q : ℕ) (hQ : 1 ≤ Q) (x₀ : d → ℝ) (ℓ h a b : ℝ)
    (hℓ : 0 < ℓ) (hℓh : ℓ ≤ h)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) (hκ : 0 < κ)
    (hlegal : ∀ (side : Bool) (ζ : activeBlocks (d := d) ℓ h → Bool),
      (fields regime side (activeBlocks ℓ h) (extendBlockSample (activeBlocks ℓ h) ζ)
        x₀ ℓ h a b).Legal α β γ Lπ L₀ Lτ κ) (n : ℕ) :
    (uniformMixtureDensity (signPrior (activeBlocks ℓ h))
      (actualFamily regime (activeBlocks ℓ h) x₀ ℓ h a b hlegal true) hκ.le n).totalVariation
      (uniformMixtureDensity (signPrior (activeBlocks ℓ h))
        (actualFamily regime (activeBlocks ℓ h) x₀ ℓ h a b hlegal false) hκ.le n) ≤
      clusterConstant d Q * ((n : ℝ) ^ (Q + 1) * h ^ Fintype.card d * ℓ ^ (Q * Fintype.card d)) +
        Real.sqrt (actualComparisonConstant d κ Q *
          (a^2*b^2 + (if regime then b^4 else a^4)) *
          (n : ℝ)^2 * h^Fintype.card d * ℓ^Fintype.card d) := by
  let D := componentHellingerConstant ((2 : ℝ)^Fintype.card d) (4*κ^2) Q *
    (a^2*b^2 + (if regime then b^4 else a^4))
  have hD : 0 ≤ D := by
    apply mul_nonneg (componentHellingerConstant_nonneg _ _ (by positivity) _)
    cases regime <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> positivity
  have hh := uniform_totalVariation_bound n Q x₀ ℓ h D hℓ.le (hℓ.le.trans hℓh) hD
    (actualSampleConditional regime true (activeBlocks ℓ h) x₀ ℓ h a b hlegal hκ.le)
    (actualSampleConditional regime false (activeBlocks ℓ h) x₀ ℓ h a b hlegal hκ.le)
    (uniformMixtureConditional_measurable _ _ hκ.le n)
    (uniformMixtureConditional_measurable _ _ hκ.le n)
    (fun x hx => actual_global_hellinger_bound regime Q hQ x₀ ℓ h a b hℓ hℓh
      ha ha1 hb hb1 hκ hlegal x hx)
  convert hh using 1
  congr 2
  dsimp only [D, actualComparisonConstant]
  simp only [mul_pow]
  ring

end CausalLowerbound.UniformLowerBound
