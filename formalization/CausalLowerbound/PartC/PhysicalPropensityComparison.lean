import CausalLowerbound.PartC.ObservationComparisonBounds
import CausalLowerbound.PartC.PropensitySignRestoration
import CausalLowerbound.PartC.PropensityChoiceBounds
import CausalLowerbound.PartC.ObservationTaperRemoval

/-! The complete pattern comparison on separated assignment interiors.
All matching and resampling estimates are proved for the actual physical
weights. The resulting bound retains the target amplitude ja * b * t. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

theorem selectedGhostTaper_empty {A G : Type*} [Fintype A] [Fintype G]
    (Q : ℕ) (e : A ⊕ G ≃ Fin Q) (τ : ℝ) (u : A → d → ℝ) :
    selectedGhostTaper Q e τ u ∅ = (fun _ => 1) := by
  funext g
  simp only [selectedGhostTaper, if_pos rfl, if_true]

theorem physical_propensity_pattern_comparison_bound
    (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ ja b t τ : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hh : 0 < h) (hw : 0 < w) (hw1 : w ≤ 1)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ z : d → ℝ, assignmentMultiplier c w z * linearPartition z = assignmentPartition w z)
    (hmb : ∀ z : d → ℝ, 0 ≤ assignmentMultiplier c w z ∧ assignmentMultiplier c w z ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (hja : 0 ≤ ja) (hsmall : ja * (1 + N₀) ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (ht : 0 ≤ t) (hbtja : b * t ≤ ja)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (hB : ∀ k, ‖B k‖ ≤ 2) (hreflect : ∀ k, reflection (B k) = B k)
    (x : I → d → ℝ) (y : I → Bool × Bool)
    (hsep : ∀ i j, i ≠ j → 2 * ℓ < ‖x i - x j‖)
    (hcover : ∀ i, coarseBump x₀ h (x i) ≠ 0 → ∀ k, assignmentWeight w x₀ r k (x i) ≠ 0 → k ∈ S)
    (htr : ∀ i, coarseBump x₀ h (x i) ≠ 0 → x i ∉ assignmentTransitionUnion S w x₀ r)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q))
    (hsmooth : ∀ i, |b * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
      (globalCarriedPolynomial Q S x₀ r (x i))| ≤ 1) :
    let T := Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))
    let F := propensityObservationGhostProduct Q hQ S x₀ ℓ r h c w N ja τ B x G e
    let base := propensityObservationUntaperedGhostProduct Q hQ S x₀ ℓ r h c w N ja B x G e (fun _ => none)
    let cells := fun side ζ => ∏ i, eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
      (mixedPropensityCellPolynomial Q side S x₀ ℓ r h ja b t ζ (x i) (y i))
    let C := 1 + N₀ / c + 1 / (c * N₀)
    let signCost := (2 * C ^ Q) ^ Fintype.card S * ∑ k, ∑ j ∈ T,
      C ^ Q * (2 * ‖symbolPart j (B k)‖ + ‖B k - unit‖ *
        ((Fintype.card (G k) : ℝ) * ((2 / (c * N)) * (ℓ / (2 * r)) ^ Fintype.card d)))
    let taperCost := (2 * C ^ Q) ^ Fintype.card S * ∑ k,
      (2 * C ^ Q) * completedGhostTaperDefect Q (e k) τ
        (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))
    let scale := (2 : ℝ) ^ Fintype.card I * ((Fintype.card I : ℝ) + 1) * (t * (ja * (1 + N₀)))
    |independentSigns.expect (fun ζ => ∑ s : I → Option S,
        propensityObservationCoefficient Q ρ false S x₀ ℓ r h ja b t ζ x y ξ s * F s ζ ζ) -
      independentSigns.expect (fun ζ => base ζ ζ * cells true ζ)| ≤
      (((Fintype.card S : ℝ) + 1) ^ Fintype.card I * b) *
        (signCost * scale + taperCost * scale) +
      signCost * ((2 : ℝ) ^ Fintype.card I * Fintype.card I * (|ja * b * t| / 2)) := by
  dsimp only
  let T := Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))
  let F := propensityObservationGhostProduct Q hQ S x₀ ℓ r h c w N ja τ B x G e
  let W := propensityObservationUntaperedGhostProduct Q hQ S x₀ ℓ r h c w N ja B x G e
  let base := W (fun _ => none)
  let cells := fun side ζ => ∏ i, eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
    (mixedPropensityCellPolynomial Q side S x₀ ℓ r h ja b t ζ (x i) (y i))
  let a := fun ζ s => propensityObservationCoefficient Q ρ false S x₀ ℓ r h ja b t ζ x y ξ s
  let g := fun s => b * |propensityChoiceNormalizedCoefficient Q ρ S x₀ r b x y ξ s|
  let C := 1 + N₀ / c + 1 / (c * N₀)
  let signCost := (2 * C ^ Q) ^ Fintype.card S * ∑ k, ∑ j ∈ T,
    C ^ Q * (2 * ‖symbolPart j (B k)‖ + ‖B k - unit‖ *
      ((Fintype.card (G k) : ℝ) * ((2 / (c * N)) * (ℓ / (2 * r)) ^ Fintype.card d)))
  let taperCost := (2 * C ^ Q) ^ Fintype.card S * ∑ k,
    (2 * C ^ Q) * completedGhostTaperDefect Q (e k) τ
      (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val)))
  let scale := (2 : ℝ) ^ Fintype.card I * ((Fintype.card I : ℝ) + 1) * (t * (ja * (1 + N₀)))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hNpos : 0 < N := (div_pos hN₀ hc).trans_le hN
  have hsignCost : 0 ≤ signCost := by dsimp [signCost]; positivity
  have htaperCost : 0 ≤ taperCost := by
    apply mul_nonneg (pow_nonneg (mul_nonneg (by norm_num) (pow_nonneg hC Q)) _) (Finset.sum_nonneg _)
    intro k _
    exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hC Q))
      (completedGhostTaperDefect_bounds Q (e k) τ _).1
  have hscale : 0 ≤ scale := by dsimp [scale]; positivity
  have hja1 : ja ≤ 1 := (le_mul_of_one_le_right hja (by linarith : 1 ≤ 1 + N₀)).trans hsmall
  have hja2 : ja ^ 2 ≤ 1 := pow_le_one₀ hja hja1
  have htarget : |ja * b * t| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg hja hb) ht), mul_assoc]
    exact (mul_le_mul hja1 (hbtja.trans hja1) (mul_nonneg hb ht) zero_le_one).trans (by norm_num)
  have hfirst (s : I → Option S) (hs : 0 < choiceDegree s) :
      |independentSigns.expect (fun ζ => a ζ s * (F s ζ ζ - Walsh.resampleAverage T (F s ζ) ζ))| ≤
        g s * (signCost * scale) := by
    have he := propensity_observation_resampling_bound Q hQ ρ S x₀ ℓ r h hℓ hr c w N N₀ ja b t τ
      hc hN₀ hN hmb hrough hja hsmall hb ht hbtja B hB hreflect x y G e ξ s hs T
    simpa only [a, F, g, signCost, scale, C, mul_assoc] using he
  have hsecond (s : I → Option S) (hs : 0 < choiceDegree s) :
      |independentSigns.expect (fun ζ => a ζ s * Walsh.resampleAverage T (fun η => F s ζ η - W s ζ η) ζ)| ≤
        g s * (taperCost * scale) := by
    have he := propensity_observation_taper_removal_bound Q hQ ρ S x₀ ℓ r h c w N N₀ ja b t τ
      hc hN₀ hN hmb hrough hja hsmall hb ht hbtja B hB hreflect x y G e ξ s hs T
    simpa only [a, F, W, g, taperCost, scale, C, mul_assoc] using he
  have hzero ζ : a ζ (fun _ => none) * F (fun _ => none) ζ ζ = base ζ ζ * cells false ζ := by
    have he := propensityObservationCoefficient_none Q ρ false S x₀ ℓ r h ja b t ζ x y ξ
    simp only [a, he, F, propensityObservationGhostProduct, base, W,
      propensityObservationUntaperedGhostProduct, observationChoiceSet_none, Finset.image_empty,
      physicalGhostPatternWeight, selectedGhostTaper_empty, cells]
    ring
  have hmatch : independentSigns.expect (fun ζ => Walsh.resampleAverage T (fun η => ∑ s : I → Option S,
        if 0 < choiceDegree s then a ζ s * W s ζ η else 0) ζ) =
      independentSigns.expect (fun ζ => Walsh.resampleAverage T (fun η => base ζ η * (cells true ζ - cells false ζ)) ζ) := by
    have he := physical_untapered_ghost_increment_matching Q hQ ρ S x₀ ℓ r h c w N N₀ ja b t
      hℓ hr hh hw hw1 hc hN₀ hN hja2 hm hmb hrough x y hsep hcover htr B G e ξ
    refine Eq.trans ?_ (Eq.trans he ?_)
    · apply FiniteLaw.expect_congr
      intro ζ
      unfold Walsh.resampleAverage
      apply FiniteLaw.expect_congr
      intro fresh
      apply Finset.sum_congr rfl
      intro s _
      by_cases hs : 0 < choiceDegree s
      · simp only [if_pos hs]
        apply congrArg (fun v : ℝ => a ζ s * v)
        dsimp only [W, propensityObservationUntaperedGhostProduct]
        apply Finset.prod_congr rfl
        intro k _
        congr 1
        ext v
        simp only [Finset.mem_image]
      · simp only [if_neg hs]
    · apply FiniteLaw.expect_congr
      intro ζ
      unfold Walsh.resampleAverage
      apply FiniteLaw.expect_congr
      intro fresh
      apply congrArg (fun v : ℝ => v * (cells true ζ - cells false ζ))
      dsimp only [base, W, propensityObservationUntaperedGhostProduct]
      simp only [observationChoiceSet_none, Finset.image_empty]
      apply Finset.prod_congr rfl
      intro k _
      congr 1
  have hrestore : |independentSigns.expect (fun ζ => Walsh.resampleAverage T
        (fun η => base ζ η * (cells true ζ - cells false ζ)) ζ) -
      independentSigns.expect (fun ζ => base ζ ζ * (cells true ζ - cells false ζ))| ≤
      signCost * ((2 : ℝ) ^ Fintype.card I * Fintype.card I * (|ja * b * t| / 2)) := by
    have he := physical_propensity_increment_restoration_bound Q S
      (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2) x₀ ℓ r h hℓ hr c w N N₀ ja b t
      hc hN₀ hN hmb hrough hja hsmall htarget B hB x y hsmooth G e T
    simpa only [base, W, propensityObservationUntaperedGhostProduct, observationChoiceSet_none,
      Finset.image_empty, cells, signCost, C] using he
  exact observation_pattern_comparison_bound T a F W base cells g (signCost * scale) (taperCost * scale)
    _ _ (mul_nonneg hsignCost hscale) (mul_nonneg htaperCost hscale)
    (propensityChoiceNormalizedCoefficient_sum_bound Q ρ S x₀ r b hb x y ξ hsmooth)
    hfirst hsecond hzero hmatch hrestore

end CausalLowerbound.PartC
