import CausalLowerbound.PartC.ObservationPatternCrudeBound
import CausalLowerbound.PartC.RawPropensityComparison

/-! A comparison valid on every configuration, including collisions and
assignment transitions. Its constant depends on the numbers of observations
and incident blocks, but the error still contains the full target amplitude. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {Ω K d I : Type*} [Fintype Ω] [Fintype K] [DecidableEq K]
  [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

theorem observation_pattern_crude_bound (μ : FiniteLaw Ω)
    (f : Ω → (I → Option K) → ℝ) (base : Ω → ℝ) (cells : Bool → Ω → ℝ)
    (g : (I → Option K) → ℝ) (A C R : ℝ) (hA : 0 ≤ A)
    (hg : (∑ s : I → Option K, if 0 < choiceDegree s then g s else 0) ≤ C)
    (hf : ∀ s, 0 < choiceDegree s → |μ.expect (fun ω => f ω s)| ≤ g s * A)
    (hzero : ∀ ω, f ω (fun _ => none) = base ω * cells false ω)
    (hdelta : |μ.expect (fun ω => base ω * (cells true ω - cells false ω))| ≤ R) :
    |μ.expect (fun ω => ∑ s : I → Option K, f ω s) -
      μ.expect (fun ω => base ω * cells true ω)| ≤ C * A + R := by
  have hn : |μ.expect (fun ω => ∑ s : I → Option K,
      if 0 < choiceDegree s then f ω s else 0)| ≤ C * A := by
    rw [nonempty_choice_expect_sum]
    calc
      _ ≤ ∑ s : I → Option K, |if 0 < choiceDegree s then μ.expect (fun ω => f ω s) else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s : I → Option K, if 0 < choiceDegree s then g s * A else 0 := by
        apply Finset.sum_le_sum
        intro s _
        by_cases hs : 0 < choiceDegree s
        · simpa only [if_pos hs] using hf s hs
        · simp only [if_neg hs, abs_zero, le_refl]
      _ = (∑ s : I → Option K, if 0 < choiceDegree s then g s else 0) * A := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro s _
        by_cases hs : 0 < choiceDegree s <;> simp only [hs, if_true, if_false, zero_mul]
      _ ≤ C * A := mul_le_mul_of_nonneg_right hg hA
  have hz ω : (∑ s : I → Option K, f ω s) =
      (∑ s : I → Option K, if 0 < choiceDegree s then f ω s else 0) + base ω * cells false ω := by
    have he := nonempty_observation_choice_sum (f ω)
    rw [hzero ω] at he
    linarith
  have he : μ.expect (fun ω => ∑ s : I → Option K, f ω s) -
      μ.expect (fun ω => base ω * cells true ω) =
      μ.expect (fun ω => ∑ s : I → Option K, if 0 < choiceDegree s then f ω s else 0) -
      μ.expect (fun ω => base ω * (cells true ω - cells false ω)) := by
    rw [FiniteLaw.expect_congr _ hz, FiniteLaw.expect_add]
    simp only [mul_sub, FiniteLaw.expect_sub]
    ring
  rw [he]
  exact (abs_sub _ _).trans (add_le_add hn hdelta)

def propensityCrudeConstant (Q q k : ℕ) (c N₀ : ℝ) : ℝ :=
  (2 * (1 + N₀ / c + 1 / (c * N₀)) ^ Q) ^ k *
    (((k : ℝ) + 1) ^ q * (2 : ℝ) ^ q * ((q : ℝ) + 1) * (1 + N₀) +
      (2 : ℝ) ^ q * q / 2)

theorem propensityCrudeConstant_nonneg (Q q k : ℕ) (c N₀ : ℝ)
    (hc : 0 < c) (hN₀ : 0 < N₀) : 0 ≤ propensityCrudeConstant Q q k c N₀ := by
  unfold propensityCrudeConstant
  positivity

theorem physical_propensity_pattern_crude_bound
    (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ ja b t τ : ℝ)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ z : d → ℝ, 0 ≤ assignmentMultiplier c w z ∧ assignmentMultiplier c w z ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (hja : 0 ≤ ja) (hsmall : ja * (1 + N₀) ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (ht : 0 ≤ t) (hbtja : b * t ≤ ja)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (hB : ∀ k, ‖B k‖ ≤ 2) (hreflect : ∀ k, reflection (B k) = B k)
    (x : I → d → ℝ) (y : I → Bool × Bool)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q))
    (hsmooth : ∀ i, |b * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
      (globalCarriedPolynomial Q S x₀ r (x i))| ≤ 1) :
    let F := propensityObservationGhostProduct Q hQ S x₀ ℓ r h c w N ja τ B x G e
    let base := propensityObservationUntaperedGhostProduct Q hQ S x₀ ℓ r h c w N ja B x G e (fun _ => none)
    |independentSigns.expect (fun ζ => ∑ s : I → Option S,
        propensityObservationCoefficient Q ρ false S x₀ ℓ r h ja b t ζ x y ξ s * F s ζ ζ) -
      independentSigns.expect (fun ζ => base ζ ζ * ∏ i,
        eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
          (mixedPropensityCellPolynomial Q true S x₀ ℓ r h ja b t ζ (x i) (y i)))| ≤
      propensityCrudeConstant Q (Fintype.card I) (Fintype.card S) c N₀ * |ja * b * t| := by
  dsimp only
  let F := propensityObservationGhostProduct Q hQ S x₀ ℓ r h c w N ja τ B x G e
  let base := propensityObservationUntaperedGhostProduct Q hQ S x₀ ℓ r h c w N ja B x G e (fun _ => none)
  let cells := fun side ζ => ∏ i, eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
    (mixedPropensityCellPolynomial Q side S x₀ ℓ r h ja b t ζ (x i) (y i))
  let a := fun ζ s => propensityObservationCoefficient Q ρ false S x₀ ℓ r h ja b t ζ x y ξ s
  let g := fun s => b * |propensityChoiceNormalizedCoefficient Q ρ S x₀ r b x y ξ s|
  let C := 1 + N₀ / c + 1 / (c * N₀)
  let M := (2 * C ^ Q) ^ Fintype.card S
  let A := M * (2 : ℝ) ^ Fintype.card I * ((Fintype.card I : ℝ) + 1) * (t * (ja * (1 + N₀)))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hja1 : ja ≤ 1 := (le_mul_of_one_le_right hja (by linarith : 1 ≤ 1 + N₀)).trans hsmall
  have hja2 : ja ^ 2 ≤ 1 := pow_le_one₀ hja hja1
  have htarget : |ja * b * t| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg hja hb) ht), mul_assoc]
    exact (mul_le_mul hja1 (hbtja.trans hja1) (mul_nonneg hb ht) zero_le_one).trans (by norm_num)
  have hbase ζ : |base ζ ζ| ≤ M := by
    have hf : base ζ ζ = ∏ k : S, physicalGhostPatternWeight Q x₀ ℓ r h k.val c w N ja τ
        (B k) (e k) (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val))) ζ ζ ∅ := by
      simp only [base, propensityObservationUntaperedGhostProduct, observationChoiceSet_none,
        Finset.image_empty, physicalGhostPatternWeight, selectedGhostTaper_empty]
    rw [hf, Finset.abs_prod]
    apply (Finset.prod_le_prod (fun k _ => abs_nonneg _) (fun k _ =>
      (physicalGhostPatternWeight_bound Q x₀ ℓ r h k.val c w N N₀ ja τ hc hN₀ hN hm hrough hja2
        (B k) (e k) _ ζ ζ ∅).trans (show C ^ Q * ‖B k‖ ≤ 2 * C ^ Q from
          by nlinarith [pow_nonneg hC Q, hB k]))).trans
    simp only [Finset.prod_const, Finset.card_univ, M]
    exact le_refl _
  have hcells ζ : |cells true ζ - cells false ζ| ≤
      (2 : ℝ) ^ Fintype.card I * Fintype.card I * (|ja * b * t| / 2) := by
    apply mixedPropensityCellProduct_sub_abs_le Q S _ x₀ ℓ r h ja b t ζ x y _ hsmooth htarget
    intro i
    have hx : |physicalRoughField x₀ ℓ h ζ (x i)| ≤ N₀ := by
      rw [← physicalRoughWalsh_evaluate]
      exact (Walsh.evaluate_bound ζ _).trans (hrough _)
    rw [abs_mul, abs_of_nonneg hja]
    exact (mul_le_mul_of_nonneg_left hx hja).trans (by nlinarith)
  have hz ζ : a ζ (fun _ => none) * F (fun _ => none) ζ ζ = base ζ ζ * cells false ζ := by
    have he := propensityObservationCoefficient_none Q ρ false S x₀ ℓ r h ja b t ζ x y ξ
    simp only [a, he, F, propensityObservationGhostProduct, base,
      propensityObservationUntaperedGhostProduct, observationChoiceSet_none, Finset.image_empty,
      physicalGhostPatternWeight, selectedGhostTaper_empty, cells]
    ring
  have hd : |independentSigns.expect (fun ζ => base ζ ζ * (cells true ζ - cells false ζ))| ≤
      M * ((2 : ℝ) ^ Fintype.card I * Fintype.card I * (|ja * b * t| / 2)) := by
    apply FiniteLaw.abs_expect_le_bound
    intro ζ
    rw [abs_mul]
    exact mul_le_mul (hbase ζ) (hcells ζ) (abs_nonneg _) hM
  have he := observation_pattern_crude_bound independentSigns (fun ζ s => a ζ s * F s ζ ζ)
    (fun ζ => base ζ ζ) cells g A (((Fintype.card S : ℝ) + 1) ^ Fintype.card I * b) _ hA
    (propensityChoiceNormalizedCoefficient_sum_bound Q ρ S x₀ r b hb x y ξ hsmooth)
    (fun s hs => propensity_observation_pattern_bound Q hQ ρ S x₀ ℓ r h c w N N₀ ja b t τ
      hc hN₀ hN hm hrough hja hsmall hb ht hbtja B hB hreflect x y G e ξ s hs) hz hd
  apply he.trans_eq
  dsimp [A, M, C, propensityCrudeConstant]
  rw [abs_of_nonneg (mul_nonneg (mul_nonneg hja hb) ht)]
  ring

theorem physical_propensity_pattern_average_crude_bound
    (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ ja b t τ : ℝ)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ z : d → ℝ, 0 ≤ assignmentMultiplier c w z ∧ assignmentMultiplier c w z ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (hja : 0 ≤ ja) (hsmall : ja * (1 + N₀) ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (ht : 0 ≤ t) (hbtja : b * t ≤ ja)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (hB : ∀ k, ‖B k‖ ≤ 2) (hreflect : ∀ k, reflection (B k) = B k)
    (x : I → d → ℝ) (y : I → Bool × Bool)
    (G : S → Type) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (hsmooth : ∀ (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) i,
      |b * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (globalCarriedPolynomial Q S x₀ r (x i))| ≤ 1) :
    let base := propensityObservationUntaperedGhostProduct Q hQ S x₀ ℓ r h c w N ja B x G e (fun _ => none)
    |independentSigns.expect (fun ζ => propensityObservationPatternSum Q hQ ρ false S x₀ ℓ r h c w N ja b t τ B ζ x y G e) -
      independentSigns.expect (fun ζ => (FiniteLaw.independent (fun _ : S => paperCoefficientLaw Q)).expect (fun ξ =>
        base ζ ζ * ∏ i, eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
          (mixedPropensityCellPolynomial Q true S x₀ ℓ r h ja b t ζ (x i) (y i))))| ≤
      propensityCrudeConstant Q (Fintype.card I) (Fintype.card S) c N₀ * |ja * b * t| := by
  dsimp only
  let base := propensityObservationUntaperedGhostProduct Q hQ S x₀ ℓ r h c w N ja B x G e (fun _ => none)
  let f := fun ζ ξ => ∑ s : I → Option S,
    propensityObservationCoefficient Q ρ false S x₀ ℓ r h ja b t ζ x y ξ s *
      propensityObservationGhostProduct Q hQ S x₀ ℓ r h c w N ja τ B x G e s ζ ζ
  let g := fun ζ (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) => base ζ ζ * ∏ i,
    eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
      (mixedPropensityCellPolynomial Q true S x₀ ℓ r h ja b t ζ (x i) (y i))
  have he ξ : |independentSigns.expect (fun ζ => f ζ ξ) - independentSigns.expect (fun ζ => g ζ ξ)| ≤
      propensityCrudeConstant Q (Fintype.card I) (Fintype.card S) c N₀ * |ja * b * t| :=
    physical_propensity_pattern_crude_bound Q hQ ρ S x₀ ℓ r h c w N N₀ ja b t τ
      hc hN₀ hN hm hrough hja hsmall hb hb1 ht hbtja B hB hreflect x y G e ξ (hsmooth ξ)
  have hd := double_average_comparison_bound independentSigns
    (FiniteLaw.independent (fun _ : S => paperCoefficientLaw Q)) f g
    (fun _ => propensityCrudeConstant Q (Fintype.card I) (Fintype.card S) c N₀ * |ja * b * t|) he
  simpa only [FiniteLaw.expect_const, f, g, base, propensityObservationPatternSum,
    propensityObservationGhostProduct] using hd

theorem physical_propensity_raw_crude_bound
    (Q : ℕ) (hQ : 0 < Q) (ρ : ℝ) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ r h c w N N₀ θ ja b t τ C₀ δ : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N) (hθ : 0 ≤ θ)
    (hm : ∀ z : d → ℝ, 0 ≤ assignmentMultiplier c w z ∧ assignmentMultiplier c w z ≤ 1 / c)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (hja : 0 ≤ ja) (hsmall : ja * (1 + N₀) ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (ht : 0 ≤ t) (hbtja : b * t ≤ ja)
    (hcarr : ∀ k : S, HasPaperPropensityCarrier Q ρ x₀ ℓ r h k.val c w N N₀ θ ja t τ C₀ δ)
    (R : ∀ k : S, PropensityMomentWitness Q ρ x₀ ℓ r h k.val c w N θ ja t τ)
    (x : I → d → ℝ) (y : I → Bool × Bool) (hcard : Fintype.card I ≤ Q)
    (G : S → Type) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q)
    (hsmooth : ∀ (ξ : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) i,
      |b * eval (fun ka => paperCoefficientAtoms Q ρ (ξ ka.1) ka.2)
        (globalCarriedPolynomial Q S x₀ r (x i))| ≤ 1) :
    let raw := fun side => physicalPropensityRawLikelihood Q ρ side S x₀ ℓ r h c w N N₀ θ ja b t
      hℓ hr hc hN₀ hN hm hrough hθ x y
    |(signBlockPrior (fun k => (R k).law) (fun k => (R k).kernel)).expect (raw false) -
      (signBlockPrior (fun k => (R k).law) (fun _ _ _ => paperCoefficientLaw Q)).expect (raw true)| ≤
      propensityCrudeConstant Q (Fintype.card I) (Fintype.card S) c N₀ * |ja * b * t| := by
  dsimp only
  let raw := fun side => physicalPropensityRawLikelihood Q ρ side S x₀ ℓ r h c w N N₀ θ ja b t
    hℓ hr hc hN₀ hN hm hrough hθ x y
  let reference := (signBlockPrior (fun k => (R k).law) (fun _ _ _ => paperCoefficientLaw Q)).expect (raw true)
  let F := fun ζ (σ : S → Equiv.Perm (Fin Q)) =>
    propensityObservationPatternSum Q hQ ρ false S x₀ ℓ r h c w N ja b t τ
      (fun k => (R k).representative) ζ x y G (fun k => (e k).trans (σ k).symm)
  let E := propensityCrudeConstant Q (Fintype.card I) (Fintype.card S) c N₀ * |ja * b * t|
  have hja1 : ja ≤ 1 := (le_mul_of_one_le_right hja (by linarith : 1 ≤ 1 + N₀)).trans hsmall
  have hraw : (signBlockPrior (fun k => (R k).law) (fun k => (R k).kernel)).expect (raw false) =
      independentSigns.expect (fun ζ => (FiniteLaw.independent (fun _ : S => permutationLaw (Fin Q))).expect (F ζ)) :=
    physical_propensity_raw_cell_expansion Q hQ ρ false S x₀ ℓ r h c w N N₀ θ ja b t τ C₀ δ
      hℓ hr hc hN₀ hN hm hrough hθ (pow_le_one₀ hja hja1) hcarr R x y hcard G e
  have hbσ (σ : S → Equiv.Perm (Fin Q)) :
      |independentSigns.expect (fun ζ => F ζ σ) -
        independentSigns.expect (fun _ : activeBlocks (d := d) ℓ h → Bool => reference)| ≤ E := by
    rw [FiniteLaw.expect_const]
    have href := physical_propensity_reference_raw_cell Q ρ true S x₀ ℓ r h c w N N₀ θ ja b t τ C₀ δ
      hℓ hr hc hN₀ hN hm hrough hθ hcarr R x y G (fun k => (e k).trans (σ k).symm)
    change reference = _ at href
    rw [href]
    have he := physical_propensity_pattern_average_crude_bound Q hQ ρ S x₀ ℓ r h c w N N₀ ja b t τ
      hc hN₀ hN hm hrough hja hsmall hb hb1 ht hbtja
      (fun k => (R k).representative) (fun k => (R k).norm_le) (fun k => (R k).reflection_fixed)
      x y G (fun k => (e k).trans (σ k).symm) hsmooth
    simpa only [F, E, propensityObservationUntaperedGhostProduct, observationChoiceSet_none,
      Finset.image_empty] using he
  have he := double_average_comparison_bound independentSigns
    (FiniteLaw.independent (fun _ : S => permutationLaw (Fin Q))) F (fun _ _ => reference) (fun _ => E) hbσ
  simp only [FiniteLaw.expect_const] at he
  change |(signBlockPrior (fun k => (R k).law) (fun k => (R k).kernel)).expect (raw false) - reference| ≤ _
  rw [hraw]
  exact he

end CausalLowerbound.PartC
