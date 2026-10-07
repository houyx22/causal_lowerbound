import CausalLowerbound.PartB.PolynomialMoments
import CausalLowerbound.PartB.NuisanceLegality
import CausalLowerbound.PartB.CubicBridge
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Actual likelihood polynomials. Their degree bound follows from the
cubic regression and the coded Bernoulli likelihood, for either side.
A block enters only through its retained linear evaluations. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace CausalLowerbound.PartB.ShellGeometry
open MvPolynomial
variable {A I d : Type*} [Fintype A] [Fintype I] [Fintype d] [DecidableEq d]

theorem polynomial_const_mul_degree (c : ℝ) (p : MvPolynomial A ℝ) :
    (C c * p).totalDegree ≤ p.totalDegree := by
  simpa only [totalDegree_C, zero_add] using totalDegree_mul (C c) p

def codedLikelihoodPolynomial (R T τ : ℝ) (p y : MvPolynomial A ℝ) : MvPolynomial A ℝ :=
  1 + C R * p + C T * (y + C τ * (1 + p)) + C (R * T) * (p * y + C τ * (1 + p))

theorem codedLikelihoodPolynomial_eval (R T τ : ℝ) (p y : MvPolynomial A ℝ) (U : A → ℝ) :
    eval U (codedLikelihoodPolynomial R T τ p y) = codedLikelihood R T (eval U p) (eval U y) τ := by
  simp [codedLikelihoodPolynomial, codedLikelihood]

theorem codedLikelihoodPolynomial_degree (R T τ : ℝ) (p y : MvPolynomial A ℝ)
    (hp : p.totalDegree ≤ 1) (hy : y.totalDegree ≤ 3) :
    (codedLikelihoodPolynomial R T τ p y).totalDegree ≤ 4 := by
  have h1p : (1 + p).totalDegree ≤ 1 :=
    (totalDegree_add 1 p).trans (max_le (by simp) hp)
  have ht : (C τ * (1 + p)).totalDegree ≤ 1 := (polynomial_const_mul_degree τ _).trans h1p
  have hpy : (p * y).totalDegree ≤ 4 := (totalDegree_mul p y).trans (by omega)
  have hleft : (y + C τ * (1 + p)).totalDegree ≤ 3 :=
    (totalDegree_add _ _).trans (max_le hy (by omega))
  have hright : (p * y + C τ * (1 + p)).totalDegree ≤ 4 :=
    (totalDegree_add _ _).trans (max_le hpy (by omega))
  unfold codedLikelihoodPolynomial
  apply (totalDegree_add _ _).trans
  apply max_le _ ((polynomial_const_mul_degree _ _).trans hright)
  apply (totalDegree_add _ _).trans
  apply max_le _ ((polynomial_const_mul_degree _ _).trans (hleft.trans (by omega)))
  apply (totalDegree_add _ _).trans
  exact max_le (by simp) ((polynomial_const_mul_degree _ _).trans (hp.trans (by omega)))

def siteFieldLikelihood (side : Bool) (R T a b η δ z : ℝ) : ℝ :=
  codedLikelihood R T (a * z)
    (if side then b * ((1 + η) * z - (a ^ 2 / 3) * z ^ 3) - δ * (1 + 2 * a * z)
      else b * ((1 + η) * z - (a ^ 2 / 3) * z ^ 3))
    (if side then δ else 0)

def siteLikelihoodPolynomial (side : Bool) (R T a b η δ : ℝ)
    (z : MvPolynomial A ℝ) : MvPolynomial A ℝ :=
  let k := C b * (C (1 + η) * z - C (a ^ 2 / 3) * z ^ 3)
  codedLikelihoodPolynomial R T (if side then δ else 0) (C a * z)
    (if side then k - C δ * (1 + C (2 * a) * z) else k)

theorem siteLikelihoodPolynomial_eval (side : Bool) (R T a b η δ : ℝ)
    (z : MvPolynomial A ℝ) (U : A → ℝ) :
    eval U (siteLikelihoodPolynomial side R T a b η δ z) =
      siteFieldLikelihood side R T a b η δ (eval U z) := by
  cases side <;> simp [siteLikelihoodPolynomial, codedLikelihoodPolynomial_eval, siteFieldLikelihood]

theorem siteLikelihoodPolynomial_degree (side : Bool) (R T a b η δ : ℝ)
    (z : MvPolynomial A ℝ) (hz : z.totalDegree ≤ 1) :
    (siteLikelihoodPolynomial side R T a b η δ z).totalDegree ≤ 4 := by
  have hz3 : (z ^ 3).totalDegree ≤ 3 := (totalDegree_pow z 3).trans (by omega)
  have hk : (C b * (C (1 + η) * z - C (a ^ 2 / 3) * z ^ 3)).totalDegree ≤ 3 := by
    apply (polynomial_const_mul_degree _ _).trans
    apply (totalDegree_sub _ _).trans
    exact max_le ((polynomial_const_mul_degree _ _).trans (hz.trans (by omega)))
      ((polynomial_const_mul_degree _ _).trans hz3)
  have hc : (C δ * (1 + C (2 * a) * z)).totalDegree ≤ 1 := by
    apply (polynomial_const_mul_degree _ _).trans
    apply (totalDegree_add _ _).trans
    exact max_le (by simp) ((polynomial_const_mul_degree _ _).trans hz)
  apply codedLikelihoodPolynomial_degree _ _ _ _ _ ((polynomial_const_mul_degree _ _).trans hz)
  cases side
  · exact hk
  · exact (totalDegree_sub _ _).trans (max_le hk (hc.trans (by omega)))

def componentLikelihoodPolynomial (side : Bool) (R T : I → ℝ) (a b : ℝ) (η δ : I → ℝ)
    (z : I → MvPolynomial A ℝ) : MvPolynomial A ℝ :=
  ∏ i, siteLikelihoodPolynomial side (R i) (T i) a b (η i) (δ i) (z i)

theorem componentLikelihoodPolynomial_degree (side : Bool) (R T : I → ℝ) (a b : ℝ) (η δ : I → ℝ)
    (z : I → MvPolynomial A ℝ) (hz : ∀ i, (z i).totalDegree ≤ 1) :
    (componentLikelihoodPolynomial side R T a b η δ z).totalDegree ≤ 4 * Fintype.card I := by
  apply (totalDegree_finset_prod _ _).trans
  calc
    _ ≤ ∑ _i : I, 4 := Finset.sum_le_sum (fun i _ =>
      siteLikelihoodPolynomial_degree side (R i) (T i) a b (η i) (δ i) (z i) (hz i))
    _ = _ := by simp [mul_comm]

theorem componentLikelihoodPolynomial_eval (side : Bool) (R T : I → ℝ) (a b : ℝ) (η δ : I → ℝ)
    (z : I → MvPolynomial A ℝ) (U : A → ℝ) :
    eval U (componentLikelihoodPolynomial side R T a b η δ z) =
      ∏ i, siteFieldLikelihood side (R i) (T i) a b (η i) (δ i) (eval U (z i)) := by
  simp only [componentLikelihoodPolynomial, map_prod, siteLikelihoodPolynomial_eval]

def retainedFieldPolynomial (Q : ℕ) (offset ψ : ℝ) (x : d → ℝ) :
    MvPolynomial (CoefficientExponent d Q) ℝ :=
  C offset + ∑ κ, C (ψ * polynomialFeature x κ) * X κ

theorem retainedFieldPolynomial_degree (Q : ℕ) (offset ψ : ℝ) (x : d → ℝ) :
    (retainedFieldPolynomial Q offset ψ x).totalDegree ≤ 1 := by
  apply (totalDegree_add _ _).trans
  apply max_le (by simp)
  apply (totalDegree_finset_sum _ _).trans
  apply Finset.sup_le
  intro κ _
  exact (polynomial_const_mul_degree _ _).trans (by simp)

theorem retainedFieldPolynomial_eval (Q : ℕ) (offset ψ : ℝ) (x : d → ℝ)
    (U : CoefficientExponent d Q → ℝ) :
    eval U (retainedFieldPolynomial Q offset ψ x) = offset + ψ * coefficientEvaluation U x := by
  simp only [retainedFieldPolynomial, map_add, map_sum, map_mul, eval_C, eval_X,
    coefficientEvaluation, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro κ _
  ring

theorem model_codedLikelihood_eq_site {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h a b t δ : ℝ)
    (x : d → ℝ) (R T : ℝ) :
    codedLikelihood R T (2 * (modelFields side S U x₀ r h a b t δ).propensity x - 1)
      (2 * (modelFields side S U x₀ r h a b t δ).baseline x - 1)
      ((modelFields side S U x₀ r h a b t δ).effect x) =
    siteFieldLikelihood side R T a b (packetEta S x₀ r h a t x) (targetField x₀ h δ x)
      (packetField S U x₀ r h x) := by
  cases side <;>
    simp only [modelFields, codedOutcome, normalizedCubic, propensityPerturbation,
      siteFieldLikelihood, Bool.false_eq_true, if_false, if_true, codedLikelihood] <;> ring

end CausalLowerbound.PartB.ShellGeometry
