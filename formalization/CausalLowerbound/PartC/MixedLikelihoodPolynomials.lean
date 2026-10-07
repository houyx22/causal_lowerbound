import CausalLowerbound.PartC.MixedObservationLocality

/-! Polynomials of all carried coefficients for the actual binary cell
probabilities. The two mixed cases have degrees one and three per site.
Their coefficients may depend on the common rough-sign configuration. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry MvPolynomial
variable {d A I Ω : Type*} [Fintype d] [DecidableEq d] [Fintype A] [Fintype I]
  [Fintype Ω] [Inhabited Ω]

def globalCarriedPolynomial (Q : ℕ) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (r : ℝ) (x : d → ℝ) : MvPolynomial (S × CoefficientExponent d Q) ℝ :=
  ∑ k : S, ∑ a, C (linearPartition (localCoordinate x₀ r k.val x) *
    polynomialFeature (carrierCoordinate (localCoordinate x₀ r k.val x)) a) * X (k, a)

theorem globalCarriedPolynomial_degree (Q : ℕ) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (r : ℝ) (x : d → ℝ) :
    (globalCarriedPolynomial Q S x₀ r x).totalDegree ≤ 1 := by
  apply (totalDegree_finset_sum _ _).trans
  apply Finset.sup_le
  intro k _
  apply (totalDegree_finset_sum _ _).trans
  apply Finset.sup_le
  intro a _
  exact (polynomial_const_mul_degree _ _).trans (by simp)

theorem globalCarriedPolynomial_eval (Q : ℕ) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (U : S → Ω)
    (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r) (x : d → ℝ) :
    eval (fun ka => atoms (U ka.1) ka.2) (globalCarriedPolynomial Q S x₀ r x) =
      carriedField S (fun k => atoms (extendBlockSample S U k)) x₀ r x := by
  rw [carriedField_eq_physical _ _ _ _ hr, ← Finset.sum_coe_sort]
  simp only [globalCarriedPolynomial, map_sum, map_mul, eval_C, eval_X,
    coefficientEvaluation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [extendBlockSample, dif_pos k.property]
  apply Finset.sum_congr rfl
  intro a _
  change (linearPartition (localCoordinate x₀ r k.val x) *
    polynomialFeature (carrierCoordinate (localCoordinate x₀ r k.val x)) a) * atoms (U k) a =
      linearPartition (localCoordinate x₀ r k.val x) *
        (atoms (U k) a * polynomialFeature (carrierCoordinate (localCoordinate x₀ r k.val x)) a)
  ring

def propensitySitePolynomial (side : Bool) (R T ja b δ Λ : ℝ)
    (z : MvPolynomial A ℝ) : MvPolynomial A ℝ :=
  C (1 + R * ja * Λ) * (1 + C (T * b) * z) +
    C (if side then RoughPropensity.realField R T ja δ Λ else 0)

omit [Fintype A] in
theorem propensitySitePolynomial_eval (side : Bool) (R T ja b δ Λ : ℝ)
    (z : MvPolynomial A ℝ) (U : A → ℝ) :
    eval U (propensitySitePolynomial side R T ja b δ Λ z) =
      RoughPropensity.likelihood R T ja (b * eval U z) Λ +
        if side then RoughPropensity.realField R T ja δ Λ else 0 := by
  simp only [propensitySitePolynomial, map_add, map_mul, map_one, eval_C,
    RoughPropensity.likelihood]
  ring

theorem propensitySitePolynomial_degree (side : Bool) (R T ja b δ Λ : ℝ)
    (z : MvPolynomial A ℝ) (hz : z.totalDegree ≤ 1) :
    (propensitySitePolynomial side R T ja b δ Λ z).totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans
  apply max_le _ (by simp)
  apply (polynomial_const_mul_degree _ _).trans
  exact (totalDegree_add _ _).trans (max_le (by simp)
    ((polynomial_const_mul_degree _ _).trans hz))

def outcomeSitePolynomial (side : Bool) (R T a jb η δ Λ : ℝ)
    (z : MvPolynomial A ℝ) : MvPolynomial A ℝ :=
  let p := C a * z
  (1 + C R * p) * (1 + C (T * jb * Λ) * (C (1 + η) - p ^ 2)) +
    if side then C (-2 * δ * T) * p + C (δ * R * T) * (1 - C 3 * p ^ 2) else 0

omit [Fintype A] in
theorem outcomeSitePolynomial_eval (side : Bool) (R T a jb η δ Λ : ℝ)
    (z : MvPolynomial A ℝ) (U : A → ℝ) :
    eval U (outcomeSitePolynomial side R T a jb η δ Λ z) =
      RoughOutcome.likelihood R T jb η (a * eval U z) Λ +
        if side then RoughOutcome.realField R T (a * eval U z) δ else 0 := by
  cases side <;>
    simp only [outcomeSitePolynomial, Bool.false_eq_true, if_false, if_true,
      map_add, map_mul, map_sub, map_pow, map_one, map_zero, eval_C,
      RoughOutcome.likelihood, RoughOutcome.outcome, RoughOutcome.realField] <;> ring

theorem outcomeSitePolynomial_degree (side : Bool) (R T a jb η δ Λ : ℝ)
    (z : MvPolynomial A ℝ) (hz : z.totalDegree ≤ 1) :
    (outcomeSitePolynomial side R T a jb η δ Λ z).totalDegree ≤ 3 := by
  let p := C a * z
  have hp : p.totalDegree ≤ 1 := (polynomial_const_mul_degree _ _).trans hz
  have hp2 : (p ^ 2).totalDegree ≤ 2 := (totalDegree_pow p 2).trans (by omega)
  have hleft : (1 + C R * p).totalDegree ≤ 1 :=
    (totalDegree_add _ _).trans (max_le (by simp) ((polynomial_const_mul_degree _ _).trans hp))
  have hright : (1 + C (T * jb * Λ) * (C (1 + η) - p ^ 2)).totalDegree ≤ 2 := by
    apply (totalDegree_add _ _).trans
    apply max_le (by simp)
    apply (polynomial_const_mul_degree _ _).trans
    exact (totalDegree_sub _ _).trans (max_le (by simp only [totalDegree_C]; omega) hp2)
  have hreal : (C (-2 * δ * T) * p + C (δ * R * T) * (1 - C 3 * p ^ 2)).totalDegree ≤ 2 := by
    apply (totalDegree_add _ _).trans
    apply max_le ((polynomial_const_mul_degree _ _).trans (hp.trans (by omega)))
    apply (polynomial_const_mul_degree _ _).trans
    exact (totalDegree_sub _ _).trans (max_le (by simp) ((polynomial_const_mul_degree _ _).trans hp2))
  have hprod : ((1 + C R * p) * (1 + C (T * jb * Λ) * (C (1 + η) - p ^ 2))).totalDegree ≤ 3 :=
    (totalDegree_mul _ _).trans (by omega)
  unfold outcomeSitePolynomial
  apply (totalDegree_add _ _).trans
  apply max_le hprod
  cases side
  · simp
  · exact hreal.trans (by omega)

def mixedPropensityCellPolynomial (Q : ℕ) (side : Bool) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ r h ja b t : ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (x : d → ℝ) (y : Bool × Bool) : MvPolynomial (S × CoefficientExponent d Q) ℝ :=
  C (1 / 4) * propensitySitePolynomial side (sign y.1) (sign y.2) ja b
    (targetField x₀ h (ja * b * t) x) (physicalRoughField x₀ ℓ h ζ x)
    (globalCarriedPolynomial Q S x₀ r x)

def mixedOutcomeCellPolynomial (Q : ℕ) (side : Bool) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ r h a jb t : ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (x : d → ℝ) (y : Bool × Bool) : MvPolynomial (S × CoefficientExponent d Q) ℝ :=
  C (1 / 4) * outcomeSitePolynomial side (sign y.1) (sign y.2) a jb
    (physicalRoughCorrection x₀ ℓ h (a * t) x) (targetField x₀ h (a * t * jb) x)
    (physicalRoughField x₀ ℓ h ζ x) (globalCarriedPolynomial Q S x₀ r x)

theorem mixedPropensityCellPolynomial_eval (Q : ℕ) (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (U : S → Ω)
    (x₀ : d → ℝ) (ℓ r h ja b t : ℝ) (hr : 0 < r)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (x : d → ℝ) (y : Bool × Bool) :
    eval (fun ka => atoms (U ka.1) ka.2) (mixedPropensityCellPolynomial Q side S x₀ ℓ r h ja b t ζ x y) =
      nuisanceCellMass (roughPropensityFields side S (fun k => atoms (extendBlockSample S U k))
        x₀ ℓ r h ja b t ζ) x y := by
  simp only [mixedPropensityCellPolynomial, map_mul, eval_C, propensitySitePolynomial_eval,
    globalCarriedPolynomial_eval Q S atoms U x₀ r hr]
  unfold nuisanceCellMass
  rw [roughPropensityFields_likelihood]
  ring

theorem mixedOutcomeCellPolynomial_eval (Q : ℕ) (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (U : S → Ω)
    (x₀ : d → ℝ) (ℓ r h a jb t : ℝ) (hr : 0 < r)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (x : d → ℝ) (y : Bool × Bool) :
    eval (fun ka => atoms (U ka.1) ka.2) (mixedOutcomeCellPolynomial Q side S x₀ ℓ r h a jb t ζ x y) =
      nuisanceCellMass (roughOutcomeFields side S (fun k => atoms (extendBlockSample S U k))
        x₀ ℓ r h a jb t ζ) x y := by
  simp only [mixedOutcomeCellPolynomial, map_mul, eval_C, outcomeSitePolynomial_eval,
    globalCarriedPolynomial_eval Q S atoms U x₀ r hr]
  unfold nuisanceCellMass
  rw [roughOutcomeFields_likelihood]
  ring

theorem mixedPropensityCellPolynomial_degree (Q : ℕ) (side : Bool) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ r h ja b t : ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (x : d → ℝ) (y : Bool × Bool) :
    (mixedPropensityCellPolynomial Q side S x₀ ℓ r h ja b t ζ x y).totalDegree ≤ 1 :=
  (polynomial_const_mul_degree _ _).trans (propensitySitePolynomial_degree _ _ _ _ _ _ _ _
    (globalCarriedPolynomial_degree _ _ _ _ _))

theorem mixedOutcomeCellPolynomial_degree (Q : ℕ) (side : Bool) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ r h a jb t : ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (x : d → ℝ) (y : Bool × Bool) :
    (mixedOutcomeCellPolynomial Q side S x₀ ℓ r h a jb t ζ x y).totalDegree ≤ 3 :=
  (polynomial_const_mul_degree _ _).trans (outcomeSitePolynomial_degree _ _ _ _ _ _ _ _ _
    (globalCarriedPolynomial_degree _ _ _ _ _))

def mixedPropensityComponentPolynomial (Q : ℕ) (side : Bool) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ r h ja b t : ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (x : I → d → ℝ) (y : I → Bool × Bool) : MvPolynomial (S × CoefficientExponent d Q) ℝ :=
  ∏ i, mixedPropensityCellPolynomial Q side S x₀ ℓ r h ja b t ζ (x i) (y i)

def mixedOutcomeComponentPolynomial (Q : ℕ) (side : Bool) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ r h a jb t : ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (x : I → d → ℝ) (y : I → Bool × Bool) : MvPolynomial (S × CoefficientExponent d Q) ℝ :=
  ∏ i, mixedOutcomeCellPolynomial Q side S x₀ ℓ r h a jb t ζ (x i) (y i)

theorem mixedPropensityComponentPolynomial_eval (Q : ℕ) (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (U : S → Ω)
    (x₀ : d → ℝ) (ℓ r h ja b t : ℝ) (hr : 0 < r)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (x : I → d → ℝ) (y : I → Bool × Bool) :
    eval (fun ka => atoms (U ka.1) ka.2)
      (mixedPropensityComponentPolynomial Q side S x₀ ℓ r h ja b t ζ x y) =
      ∏ i, nuisanceCellMass (roughPropensityFields side S (fun k => atoms (extendBlockSample S U k))
        x₀ ℓ r h ja b t ζ) (x i) (y i) := by
  simp only [mixedPropensityComponentPolynomial, map_prod,
    mixedPropensityCellPolynomial_eval Q side S atoms U x₀ ℓ r h ja b t hr]

theorem mixedOutcomeComponentPolynomial_eval (Q : ℕ) (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (U : S → Ω)
    (x₀ : d → ℝ) (ℓ r h a jb t : ℝ) (hr : 0 < r)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (x : I → d → ℝ) (y : I → Bool × Bool) :
    eval (fun ka => atoms (U ka.1) ka.2)
      (mixedOutcomeComponentPolynomial Q side S x₀ ℓ r h a jb t ζ x y) =
      ∏ i, nuisanceCellMass (roughOutcomeFields side S (fun k => atoms (extendBlockSample S U k))
        x₀ ℓ r h a jb t ζ) (x i) (y i) := by
  simp only [mixedOutcomeComponentPolynomial, map_prod,
    mixedOutcomeCellPolynomial_eval Q side S atoms U x₀ ℓ r h a jb t hr]

theorem mixedPropensityComponentPolynomial_degree (Q : ℕ) (side : Bool) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ r h ja b t : ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (x : I → d → ℝ) (y : I → Bool × Bool) :
    (mixedPropensityComponentPolynomial Q side S x₀ ℓ r h ja b t ζ x y).totalDegree ≤ Fintype.card I := by
  apply (totalDegree_finset_prod _ _).trans
  calc
    _ ≤ ∑ _i : I, 1 := Finset.sum_le_sum (fun i _ => mixedPropensityCellPolynomial_degree _ _ _ _ _ _ _ _ _ _ _ _ _)
    _ = _ := by simp

theorem mixedOutcomeComponentPolynomial_degree (Q : ℕ) (side : Bool) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ r h a jb t : ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (x : I → d → ℝ) (y : I → Bool × Bool) :
    (mixedOutcomeComponentPolynomial Q side S x₀ ℓ r h a jb t ζ x y).totalDegree ≤ 3 * Fintype.card I := by
  apply (totalDegree_finset_prod _ _).trans
  calc
    _ ≤ ∑ _i : I, 3 := Finset.sum_le_sum (fun i _ => mixedOutcomeCellPolynomial_degree _ _ _ _ _ _ _ _ _ _ _ _ _)
    _ = _ := by simp [mul_comm]

end CausalLowerbound.PartC
