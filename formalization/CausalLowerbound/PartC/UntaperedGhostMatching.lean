import CausalLowerbound.PartC.UntaperedObservationMatching
import CausalLowerbound.PartC.PropensityPatternIntegration

/-! Integrate the completed physical matching identity over the actual
product of ghost cubes. All integrability is derived from the physical
pattern bound. One shared resampled sign field remains outside every
block integral; no independence of the block representatives is inserted. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener Representative MvPolynomial
variable {d I G V J : Type*} [Fintype d] [DecidableEq d]
  [Fintype I] [DecidableEq I] [Fintype G] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J]

theorem integrated_resampled_matching {X : Type*} [MeasurableSpace X]
    (T : Finset J) (μ : Measure X) (f g : (J → Bool) → (J → Bool) → X → ℝ)
    (hf : ∀ ζ η, Integrable (f ζ η) μ) (hg : ∀ ζ η, Integrable (g ζ η) μ)
    (he : ∀ x, independentSigns.expect (fun ζ => Walsh.resampleAverage T (fun η => f ζ η x) ζ) =
      independentSigns.expect (fun ζ => Walsh.resampleAverage T (fun η => g ζ η x) ζ)) :
    independentSigns.expect (fun ζ => Walsh.resampleAverage T (fun η => ∫ x, f ζ η x ∂μ) ζ) =
      independentSigns.expect (fun ζ => Walsh.resampleAverage T (fun η => ∫ x, g ζ η x ∂μ) ζ) := by
  have hint (F : (J → Bool) → (J → Bool) → X → ℝ) (hF : ∀ ζ η, Integrable (F ζ η) μ) :
      (∫ x, independentSigns.expect (fun ζ => Walsh.resampleAverage T (fun η => F ζ η x) ζ) ∂μ) =
      independentSigns.expect (fun ζ => Walsh.resampleAverage T (fun η => ∫ x, F ζ η x ∂μ) ζ) := by
    unfold Walsh.resampleAverage
    rw [FiniteLaw.integral_expect independentSigns μ _ (fun ζ =>
      FiniteLaw.expect_integrable independentSigns μ _ (fun fresh => hF ζ (Walsh.resample T ζ fresh)))]
    apply FiniteLaw.expect_congr
    intro ζ
    exact FiniteLaw.integral_expect independentSigns μ _ (fun fresh => hF ζ (Walsh.resample T ζ fresh))
  rw [← hint f hf, ← hint g hg]
  exact integral_congr_ae (Filter.Eventually.of_forall he)

theorem partialPhysicalPatternWeight_empty (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N ja : ℝ) (B : Array d V (activeBlocks (d := d) ℓ h) 1)
    (e : I ⊕ G ≃ V) (u : I → d → ℝ) (a : I → ℝ)
    (η : activeBlocks (d := d) ℓ h → Bool) (ghost : G → d → ℝ) :
    partialPhysicalPatternWeight x₀ ℓ r h k c w N ja B e u a η ∅ ghost =
      partialPhysicalCarrierValue x₀ ℓ r h k c w N B e u a η ghost := by
  simp only [partialPhysicalPatternWeight, weightedPropensityPatternWeight, Finset.card_empty,
    pow_zero, one_mul, propensityPatternWeight_empty, partialPhysicalCarrierValue]

theorem partialPhysicalPatternWeight_integrable
    (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N N₀ ja : ℝ)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀) (hja : ja ^ 2 ≤ 1)
    (B : Array d V (activeBlocks (d := d) ℓ h) 1)
    (e : I ⊕ G ≃ V) (u : I → d → ℝ) (a : I → ℝ) (ha : ∀ i, |a i| ≤ 1)
    (C : ℝ) (hC : 1 ≤ C) (hCz : N₀ / c ≤ C) (hCκ : 1 / (c * N₀) ≤ C)
    (hNa : ∀ i, |N * a i| ≤ C) (η : activeBlocks (d := d) ℓ h → Bool) (A : Finset V) :
    Integrable (partialPhysicalPatternWeight x₀ ℓ r h k c w N ja B e u a η A)
      (Measure.pi (fun _ : G => cubeMeasure d)) := by
  apply (integrable_const (C ^ Fintype.card V * ‖B‖)).mono'
  · exact (partialPhysicalPatternWeight_continuous x₀ ℓ r h k c w N ja hc B e u a η A).aestronglyMeasurable
  · filter_upwards [] with ghost
    exact partialPhysicalPatternWeight_bound x₀ ℓ r h k c w N N₀ ja hc hN₀ hN hm hrough hja
      B e u a ha C hC hCz hCκ hNa η A ghost

theorem physical_untapered_ghost_matching
    (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ r h c w N N₀ ja b t : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hh : 0 < h) (hw : 0 < w) (hw1 : w ≤ 1)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N) (hja : ja ^ 2 ≤ 1)
    (hm : ∀ y : d → ℝ, assignmentMultiplier c w y * linearPartition y = assignmentPartition w y)
    (hmb : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀)
    (x : I → d → ℝ) (y : I → Bool × Bool)
    (hsep : ∀ i j, i ≠ j → 2 * ℓ < ‖x i - x j‖)
    (hcover : ∀ i, coarseBump x₀ h (x i) ≠ 0 → ∀ k, assignmentWeight w x₀ r k (x i) ≠ 0 → k ∈ S)
    (htr : ∀ i, coarseBump x₀ h (x i) ≠ 0 → x i ∉ assignmentTransitionUnion S w x₀ r)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) :
    let u₀ := fun (k : S) (i : {i // x i ∈ carrierBox x₀ r k.val}) =>
      carrierCoordinate (localCoordinate x₀ r k.val (x i.val))
    let W := fun (ζ η : activeBlocks (d := d) ℓ h → Bool) (k : S) (A : Finset (Fin Q)) =>
      ghostPatternIntegral x₀ ℓ r h k.val c w N ja (B k) (e k) (u₀ k)
        (fun i => normalizedRoughChart x₀ ℓ r h k.val c w N ζ (u₀ k i)) η A (fun _ => 1)
    independentSigns.expect (fun ζ => Walsh.resampleAverage
      (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) (fun η =>
      ∑ s : I → Option S, propensityObservationCoefficient Q ρ false S x₀ ℓ r h ja b t ζ x y ξ s *
        ∏ k, W ζ η k ((observationChoiceSet s k).image (retainedObservationSlot Q hQ x₀ r k.val x (e k)))) ζ) =
    independentSigns.expect (fun ζ => Walsh.resampleAverage
      (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) (fun η =>
      (∏ k, W ζ η k ∅) * ∏ i, eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (mixedPropensityCellPolynomial Q true S x₀ ℓ r h ja b t ζ (x i) (y i))) ζ) := by
  let μ := fun k : S => Measure.pi (fun _ : G k => cubeMeasure d)
  letI : ∀ k : S, MeasureSpace (G k → d → ℝ) := fun k => ⟨μ k⟩
  letI : ∀ k : S, SigmaFinite (volume : Measure (G k → d → ℝ)) :=
    fun k => inferInstanceAs (SigmaFinite (μ k))
  let u₀ := fun (k : S) (i : {i // x i ∈ carrierBox x₀ r k.val}) =>
    carrierCoordinate (localCoordinate x₀ r k.val (x i.val))
  let F := fun (ζ η : activeBlocks (d := d) ℓ h → Bool) (k : S) (A : Finset (Fin Q)) =>
    partialPhysicalPatternWeight x₀ ℓ r h k.val c w N ja (B k) (e k) (u₀ k)
      (fun i => normalizedRoughChart x₀ ℓ r h k.val c w N ζ (u₀ k i)) η A
  let W := fun (ζ η : activeBlocks (d := d) ℓ h → Bool) (k : S) (A : Finset (Fin Q)) =>
    ghostPatternIntegral x₀ ℓ r h k.val c w N ja (B k) (e k) (u₀ k)
      (fun i => normalizedRoughChart x₀ ℓ r h k.val c w N ζ (u₀ k i)) η A (fun _ => 1)
  let A := fun (s : I → Option S) (k : S) =>
    (observationChoiceSet s k).image (retainedObservationSlot Q hQ x₀ r k.val x (e k))
  let coeff := fun ζ s => propensityObservationCoefficient Q ρ false S x₀ ℓ r h ja b t ζ x y ξ s
  let cells := fun ζ => ∏ i, eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
    (mixedPropensityCellPolynomial Q true S x₀ ℓ r h ja b t ζ (x i) (y i))
  let f := fun ζ η (ghost : ∀ k, G k → d → ℝ) => ∑ s : I → Option S, coeff ζ s * ∏ k, F ζ η k (A s k) (ghost k)
  let g := fun ζ η (ghost : ∀ k, G k → d → ℝ) => (∏ k, F ζ η k ∅ (ghost k)) * cells ζ
  let C := 1 + N₀ / c + 1 / (c * N₀)
  have hcz : 0 ≤ N₀ / c := by positivity
  have hcκ : 0 ≤ 1 / (c * N₀) := by positivity
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hCz : N₀ / c ≤ C := by dsimp [C]; linarith
  have hCκ : 1 / (c * N₀) ≤ C := by dsimp [C]; linarith
  have hF (ζ η : activeBlocks (d := d) ℓ h → Bool) (k : S) (A : Finset (Fin Q)) :
      Integrable (F ζ η k A) (μ k) :=
    partialPhysicalPatternWeight_integrable x₀ ℓ r h k.val c w N N₀ ja hc hN₀ hN hmb hrough hja
      (B k) (e k) (u₀ k) _
      (fun i => normalizedRoughChart_bound x₀ ℓ r h k.val c w N N₀ hc hN₀ hN hmb hrough ζ (u₀ k i))
      C hC hCz hCκ (fun i =>
        (normalizedRoughChart_scaled_bound x₀ ℓ r h k.val c w N N₀ hc hN₀ hN hmb hrough ζ (u₀ k i)).trans hCz)
      η A
  have hp (ζ η : activeBlocks (d := d) ℓ h → Bool) (A : S → Finset (Fin Q)) :
      Integrable (fun ghost : ∀ k, G k → d → ℝ => ∏ k, F ζ η k (A k) (ghost k)) (Measure.pi μ) :=
    Integrable.fintype_prod_dep (fun k => hF ζ η k (A k))
  have hi (ζ η : activeBlocks (d := d) ℓ h → Bool) (A : S → Finset (Fin Q)) :
      (∫ ghost : ∀ k, G k → d → ℝ, (∏ k, F ζ η k (A k) (ghost k)) ∂Measure.pi μ) =
      ∏ k, W ζ η k (A k) := by
    simp only [W, ghostPatternIntegral, one_mul]
    exact @integral_fintype_prod_eq_prod ℝ inferInstance S inferInstance (fun k => G k → d → ℝ)
      (fun k => F ζ η k (A k)) (fun k => ⟨μ k⟩) (fun k => inferInstanceAs (SigmaFinite (μ k)))
  have hf (ζ η : activeBlocks (d := d) ℓ h → Bool) : Integrable (f ζ η) (Measure.pi μ) :=
    integrable_finset_sum Finset.univ (fun s _ => (hp ζ η (A s)).const_mul (coeff ζ s))
  have hg (ζ η : activeBlocks (d := d) ℓ h → Bool) : Integrable (g ζ η) (Measure.pi μ) :=
    (hp ζ η (fun _ => ∅)).mul_const (cells ζ)
  have hfint (ζ η : activeBlocks (d := d) ℓ h → Bool) :
      (∫ ghost, f ζ η ghost ∂Measure.pi μ) = ∑ s : I → Option S, coeff ζ s * ∏ k, W ζ η k (A s k) := by
    dsimp only [f]
    rw [integral_finset_sum Finset.univ (fun s _ => (hp ζ η (A s)).const_mul (coeff ζ s))]
    simp only [integral_const_mul, hi]
  have hgint (ζ η : activeBlocks (d := d) ℓ h → Bool) :
      (∫ ghost, g ζ η ghost ∂Measure.pi μ) = (∏ k, W ζ η k ∅) * cells ζ := by
    dsimp only [g]
    rw [integral_mul_const, hi]
  have hNp : 0 < N := (div_pos hN₀ hc).trans_le hN
  have he (ghost : ∀ k, G k → d → ℝ) :
      independentSigns.expect (fun ζ => Walsh.resampleAverage
        (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) (fun η => f ζ η ghost) ζ) =
      independentSigns.expect (fun ζ => Walsh.resampleAverage
        (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) (fun η => g ζ η ghost) ζ) := by
    simpa only [f, g, F, coeff, cells, A, u₀, partialPhysicalPatternWeight_empty] using
      physical_untapered_observation_matching Q hQ ρ S x₀ ℓ r h c w N ja b t hℓ hr hh hw hw1 hNp.ne' hm
        x y hsep hcover htr B G e ghost ξ
  have hh := integrated_resampled_matching
    (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) (Measure.pi μ) f g hf hg he
  simpa only [hfint, hgint, W, A, coeff, cells, u₀] using hh

end CausalLowerbound.PartC
