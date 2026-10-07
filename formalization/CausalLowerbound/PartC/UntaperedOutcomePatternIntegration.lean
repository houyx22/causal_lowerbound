import CausalLowerbound.PartC.OutcomePatternIntegration
import CausalLowerbound.PartC.CubicObservationRescaling

/-! The untapered cubic expansion has the same normalized physical
shift. Its zero weight is the partial carrier integral used in the
exact shared-sign likelihood matching theorem. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry MvPolynomial Representative
variable {d K P : Type*} [Fintype d] [DecidableEq d] [Fintype K] [DecidableEq K]
  [Fintype P] [DecidableEq P]

theorem ghostOutcomePatternIntegral_zero
    {I G : Type*} [Fintype I] [Fintype G]
    (Q : ℕ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N : ℝ)
    (B : Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ) (a : I → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) :
    ghostOutcomePatternIntegral x₀ ℓ r h k c w N B e u a ζ 0 (fun _ => 1) =
      ∫ g : G → d → ℝ, partialPhysicalCarrierValue x₀ ℓ r h k c w N B e u a ζ g
        ∂Measure.pi (fun _ : G => cubeMeasure d) := by
  unfold ghostOutcomePatternIntegral
  apply integral_congr_ae
  filter_upwards [] with g
  simp only [one_mul, partialPhysicalOutcomePatternWeight, weightedOutcomePatternWeight,
    degreeSize, Pi.zero_apply, Pi.zero_def, Fin.val_zero, Finset.sum_const_zero, pow_zero, one_mul,
    outcomePatternWeight_zero]
  rfl

theorem outcome_untapered_cube_integral
    (Q : ℕ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : K → d → ℤ) (c w N : ℝ) (hc : 0 < c)
    (I G : K → Type*) [∀ j, Fintype (I j)] [∀ j, Fintype (G j)]
    (B : K → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (e : ∀ j, I j ⊕ G j ≃ Fin Q) (u : ∀ j, I j → d → ℝ) (a : ∀ j, I j → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (p : MvPolynomial (K × Fin Q) ℝ) :
    (∫ ghost : ∀ j, G j → d → ℝ, blockPolynomialFunctional
      (fun j => cubicSiteFunctional (fun f =>
        partialPhysicalOutcomePatternWeight x₀ ℓ r h (k j) c w N (B j) (e j) (u j) (a j) ζ f (ghost j))) p
      ∂Measure.pi (fun j => Measure.pi (fun _ : G j => cubeMeasure d))) =
      blockPolynomialFunctional (fun j => cubicSiteFunctional (fun f =>
        ghostOutcomePatternIntegral x₀ ℓ r h (k j) c w N (B j) (e j) (u j) (a j) ζ f (fun _ => 1))) p := by
  let W := fun j (g : G j → d → ℝ) (f : Degree (Fin Q) 3) =>
    partialPhysicalOutcomePatternWeight x₀ ℓ r h (k j) c w N (B j) (e j) (u j) (a j) ζ f g
  have hW (j : K) (f : Degree (Fin Q) 3) : Continuous (fun g => W j g f) :=
    partialPhysicalOutcomePatternWeight_continuous x₀ ℓ r h (k j) c w N hc (B j) (e j) (u j) (a j) ζ f
  simp only [ghostOutcomePatternIntegral, one_mul]
  exact block_cubic_cube_integral G W hW p

theorem outcome_untapered_observation_integral
    (Q : ℕ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : K → d → ℤ) (c w N shift : ℝ) (hc : 0 < c)
    (I G : K → Type*) [∀ j, Fintype (I j)] [∀ j, Fintype (G j)]
    (B : K → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (e : ∀ j, I j ⊕ G j ≃ Fin Q) (u : ∀ j, I j → d → ℝ) (a : ∀ j, I j → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool)
    (b : P → Fin 4 → ℝ) (δ : P → K → ℝ) (slot : K → P → Fin Q) :
    (∫ ghost : ∀ j, G j → d → ℝ, blockPolynomialFunctional
      (fun j => partialPhysicalOutcomeFunctional x₀ ℓ r h (k j) c w N (B j) (e j) (u j) (a j) ζ (ghost j))
      (∏ i, ∑ n : Fin 4, C (b i n) * (∑ j, C ((shift * N) * δ i j) * X (j, slot j i)) ^ n.val)
      ∂Measure.pi (fun j => Measure.pi (fun _ : G j => cubeMeasure d))) =
      cubicObservationExpansion (fun j f =>
        ghostOutcomePatternIntegral x₀ ℓ r h (k j) c w N (B j) (e j) (u j) (a j) ζ f (fun _ => 1))
        b δ slot shift := by
  let p : MvPolynomial (K × Fin Q) ℝ :=
    ∏ i, ∑ n : Fin 4, C (b i n) * (∑ j, C (shift * δ i j) * X (j, slot j i)) ^ n.val
  let W := fun j (f : Degree (Fin Q) 3) =>
    ghostOutcomePatternIntegral x₀ ℓ r h (k j) c w N (B j) (e j) (u j) (a j) ζ f (fun _ => 1)
  have hpoint (ghost : ∀ j, G j → d → ℝ) := block_cubic_observation_rescale
    (fun j => outcomePatternWeight
      (fun v => normalizedRoughVariance x₀ r h (k j) c w N
        (configurationSite (completedConfiguration (e j) (u j) (ghost j)) v))
      (B j) (completedConfiguration (e j) (u j) (ghost j))
      (completedSites (e j) (a j) (fun g => normalizedRoughChart x₀ ℓ r h (k j) c w N ζ (ghost j g))) ζ)
    b δ slot shift N
  have hint := outcome_untapered_cube_integral Q x₀ ℓ r h k c w N hc I G B e u a ζ p
  have hexp : blockPolynomialFunctional (fun j => cubicSiteFunctional (W j)) p =
      cubicObservationExpansion W b δ slot shift :=
    block_cubic_observation_scaled_expansion W b δ slot shift
  refine Eq.trans ?_ (hint.trans hexp)
  apply integral_congr_ae
  filter_upwards [] with ghost
  exact hpoint ghost

end CausalLowerbound.PartC
