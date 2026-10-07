import CausalLowerbound.PartC.OutcomeObservationErrors
import CausalLowerbound.PartC.FinitePatternComparison

/-! Sum all actual cubic observation errors, use exact untapered
increment matching, and restore the shared signs on the real increment. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
attribute [local instance] cubicObservationChoiceFintype cubicObservationChoiceDecidableEq
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

def outcomeObservationComparisonError
    (Q : ℕ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h c N N₀ a jb t τ : ℝ)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3) (x : I → d → ℝ)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) : ℝ :=
  let T := Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))
  let A := outcomeObservationSignCost Q S ℓ r h c N N₀ B G T
  let D := outcomeObservationTaperCost Q S x₀ r c N₀ τ x G e
  (Fintype.card (I → CubicObservationChoice S) : ℝ) *
    ((A + D) * outcomeObservationScalarScale (Fintype.card I) N₀ jb (a * t)) +
      A * ((5 : ℝ) ^ Fintype.card I * Fintype.card I * ((3 / 2 : ℝ) * |a * t * jb|))

theorem physical_outcome_observation_comparison_bound
    (Q : ℕ) (hQ : 0 < Q) (S : Finset (d → ℤ)) (U : S → CoefficientExponent d Q → ℝ)
    (x₀ : d → ℝ) (ℓ r h c w N N₀ a jb t τ : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hh : 0 < h) (hc : 0 < c)
    (hw : 0 < w) (hw1 : w ≤ 1) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hidentity : ∀ z : d → ℝ, assignmentMultiplier c w z * linearPartition z = assignmentPartition w z)
    (hrough : ∀ z, ‖physicalRoughWalsh x₀ ℓ h z‖ ≤ N₀)
    (hjb : 0 ≤ jb) (hsmall : jb * (1 + N₀) ≤ 1) (hshift : 0 ≤ a * t) (hsjb : a * t ≤ jb)
    (x : I → d → ℝ) (y : I → Bool × Bool)
    (hsmooth : ∀ i, |a * eval (fun ka => U ka.1 ka.2) (globalCarriedPolynomial Q S x₀ r (x i))| ≤ 1)
    (hsep : ∀ i j, i ≠ j → 2 * ℓ < ‖x i - x j‖)
    (hcover : ∀ i, coarseBump x₀ h (x i) ≠ 0 → ∀ k, assignmentWeight w x₀ r k (x i) ≠ 0 → k ∈ S)
    (htr : ∀ i, coarseBump x₀ h (x i) ≠ 0 → x i ∉ assignmentTransitionUnion S w x₀ r)
    (B : S → Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3)
    (hB : ∀ k, ‖B k‖ ≤ 2) (hreflect : ∀ k, reflection (B k) = B k)
    (G : S → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k : S, {i // x i ∈ carrierBox x₀ r k.val} ⊕ G k ≃ Fin Q) :
    |independentSigns.expect (fun ζ =>
        outcomeObservationValue true Q hQ S x₀ ℓ r h c w N jb (a * t) τ B x y
          (fun i => a * eval (fun ka => U ka.1 ka.2) (globalCarriedPolynomial Q S x₀ r (x i))) G e ζ ζ) -
      independentSigns.expect (fun ζ =>
        (∏ k, outcomeObservationPatternWeight false Q S x₀ ℓ r h c w N τ B x G e ζ ζ k 0) *
          eval (fun ka => U ka.1 ka.2) (mixedOutcomeComponentPolynomial Q true S x₀ ℓ r h a jb t ζ x y))| ≤
      outcomeObservationComparisonError Q S x₀ ℓ r h c N N₀ a jb t τ B x G e := by
  let T := Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))
  let smooth := fun i => a * eval (fun ka => U ka.1 ka.2) (globalCarriedPolynomial Q S x₀ r (x i))
  let coeff := fun ζ s => outcomeObservationChoiceCoefficient S x₀ ℓ r h jb (a * t) x y smooth s ζ
  let F := outcomeObservationPatternProduct true Q hQ S x₀ ℓ r h c w N τ B x G e
  let W := outcomeObservationPatternProduct false Q hQ S x₀ ℓ r h c w N τ B x G e
  let value := fun ζ => outcomeObservationValue true Q hQ S x₀ ℓ r h c w N jb (a * t) τ B x y smooth G e ζ ζ
  let base := fun ζ η => ∏ k, outcomeObservationPatternWeight false Q S x₀ ℓ r h c w N τ B x G e ζ η k 0
  let cells := fun side ζ => eval (fun ka => U ka.1 ka.2)
    (mixedOutcomeComponentPolynomial Q side S x₀ ℓ r h a jb t ζ x y)
  let g := fun (s : I → CubicObservationChoice S) => (1 / 4 : ℝ) ^ Fintype.card I *
    |cubicObservationChoiceWeight (fun (i : I) (k : S) => linearPartition (localCoordinate x₀ r k.val (x i))) s|
  let choices := Finset.univ.erase (cubicZeroChoice : I → CubicObservationChoice S)
  let A := outcomeObservationSignCost Q S ℓ r h c N N₀ B G T
  let D := outcomeObservationTaperCost Q S x₀ r c N₀ τ x G e
  let scale := outcomeObservationScalarScale (Fintype.card I) N₀ jb (a * t)
  let restore := A * ((5 : ℝ) ^ Fintype.card I * Fintype.card I * ((3 / 2 : ℝ) * |a * t * jb|))
  have hA : 0 ≤ A := outcomeObservationSignCost_nonneg Q S ℓ r h c N N₀ hℓ.le hr.le hc.le
    ((div_pos hN₀ hc).trans_le hN).le B G T
  have hD : 0 ≤ D := outcomeObservationTaperCost_nonneg Q S x₀ r c N₀ τ x G e
  have hscale : 0 ≤ scale := outcomeObservationScalarScale_nonneg (Fintype.card I) N₀ jb (a * t) hN₀.le hjb hshift
  have hg : (∑ s ∈ choices, g s) ≤ (Fintype.card (I → CubicObservationChoice S) : ℝ) :=
    cubicObservation_normalized_weight_sum_bound (I := I) (K := S)
      (fun (i : I) (k : S) => linearPartition (localCoordinate x₀ r k.val (x i))) (fun i k => by
        rw [abs_of_nonneg (linearPartition_bounds _).1]
        exact (linearPartition_bounds _).2)
  have hfirst s (hs : s ∈ choices) :
      |independentSigns.expect (fun ζ => coeff ζ s * (F s ζ ζ - Walsh.resampleAverage T (F s ζ) ζ))| ≤
        g s * (A * scale) :=
    outcome_observation_pattern_resampling_bound Q hQ S x₀ ℓ r h hℓ hr c w N N₀ jb (a * t) τ
      hc hN₀ hN hm hrough hjb hsmall hshift hsjb B hB hreflect x y smooth hsmooth G e s
        (Finset.mem_erase.mp hs).1 T
  have hsecond s (hs : s ∈ choices) :
      |independentSigns.expect (fun ζ => coeff ζ s *
        Walsh.resampleAverage T (fun η => F s ζ η - W s ζ η) ζ)| ≤ g s * (D * scale) :=
    outcome_observation_pattern_taper_bound Q hQ S x₀ ℓ r h c w N N₀ jb (a * t) τ hℓ
      hc hN₀ hN hm hrough hjb hsmall hshift hsjb B hB hreflect x y smooth hsmooth G e s
        (Finset.mem_erase.mp hs).1 T
  have hzero ζ : value ζ = (∑ s ∈ choices, coeff ζ s * F s ζ ζ) + base ζ ζ * cells false ζ :=
    outcomeObservationValue_baseline true Q hQ S U x₀ ℓ r h c w N a jb t τ B x y G e ζ ζ
  have hmatch : independentSigns.expect (fun ζ => Walsh.resampleAverage T
        (fun η => ∑ s ∈ choices, coeff ζ s * W s ζ η) ζ) =
      independentSigns.expect (fun ζ => Walsh.resampleAverage T
        (fun η => base ζ η * (cells true ζ - cells false ζ)) ζ) := by
    have he := physical_outcome_untapered_increment_matching Q hQ S U x₀ ℓ r h c w N a jb t
      hℓ hr hh hc hw hw1 ((div_pos hN₀ hc).trans_le hN).ne' hidentity x y hsep hcover htr B G e
    simp_rw [outcomeUntaperedPositiveValue_factor Q hQ S x₀ ℓ r h c w N jb (a * t) τ] at he
    unfold base outcomeObservationPatternWeight
    simp only [Bool.false_eq_true, if_false]
    rw [show finOrderedDecEq Q = instDecidableEqFin Q from Subsingleton.elim _ _]
    exact he
  have hrestore : |independentSigns.expect (fun ζ => Walsh.resampleAverage T
        (fun η => base ζ η * (cells true ζ - cells false ζ)) ζ) -
      independentSigns.expect (fun ζ => base ζ ζ * (cells true ζ - cells false ζ))| ≤ restore := by
    have he := physical_outcome_increment_restoration_bound Q S (fun ka => U ka.1 ka.2)
      x₀ ℓ r h hℓ hr c w N N₀ a jb t hc hN₀ hN hm hrough hjb hsmall hshift hsjb B hB x y hsmooth G e T
    simpa only [base, cells, restore, A, outcomeObservationSignCost, outcomeObservationPatternWeight,
      Bool.false_eq_true, if_false, mixedOutcomeComponentPolynomial, map_prod] using he
  have he := finite_observation_comparison_bound choices T coeff F W value base cells g
    (A * scale) (D * scale) (Fintype.card (I → CubicObservationChoice S)) restore
    (mul_nonneg hA hscale) (mul_nonneg hD hscale) hg hfirst hsecond hzero hmatch hrestore
  change |independentSigns.expect value - independentSigns.expect (fun ζ => base ζ ζ * cells true ζ)| ≤
    (Fintype.card (I → CubicObservationChoice S) : ℝ) * ((A + D) * scale) + restore
  simpa only [add_mul] using he

end CausalLowerbound.PartC


