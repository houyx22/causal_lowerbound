import CausalLowerbound.PartC.CubicObservationNormalization

/-! Move a common amplitude normalization from all cubic occurrences
into their block weights, keeping every mixed monomial. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial Representative
variable {I K V : Type*} [Fintype I] [DecidableEq I]
  [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]

theorem block_cubic_observation_rescale (w : K → Degree V 3 → ℝ)
    (b : I → Fin 4 → ℝ) (δ : I → K → ℝ) (slot : K → I → V) (amp N : ℝ) :
    blockPolynomialFunctional (fun k => cubicSiteFunctional (w k))
      (∏ i, ∑ n : Fin 4, C (b i n) * (∑ k, C ((amp * N) * δ i k) * X (k, slot k i)) ^ n.val) =
      blockPolynomialFunctional (fun k => cubicSiteFunctional (fun f => N ^ degreeSize f * w k f))
        (∏ i, ∑ n : Fin 4, C (b i n) * (∑ k, C (amp * δ i k) * X (k, slot k i)) ^ n.val) :=
  (block_cubic_observation_normalized w b δ slot amp N).trans
    (block_cubic_observation_scaled_expansion (fun k f => N ^ degreeSize f * w k f) b δ slot amp).symm

theorem block_outcome_taylor_rescale (w : K → Degree V 3 → ℝ)
    (R T jb η smooth rough : I → ℝ) (δ : I → K → ℝ) (slot : K → I → V) (amp N : ℝ) :
    blockPolynomialFunctional (fun k => cubicSiteFunctional (w k))
      (∏ i, outcomeTaylorPolynomial (R i) (T i) 1 (jb i) (η i) (smooth i) (rough i)
        (∑ k, C ((amp * N) * δ i k) * X (k, slot k i))) =
      blockPolynomialFunctional (fun k => cubicSiteFunctional (fun f => N ^ degreeSize f * w k f))
        (∏ i, outcomeTaylorPolynomial (R i) (T i) 1 (jb i) (η i) (smooth i) (rough i)
          (∑ k, C (amp * δ i k) * X (k, slot k i))) := by
  simp_rw [outcomeTaylorPolynomial_eq_sum]
  exact block_cubic_observation_rescale w
    (fun i => outcomeTaylorCoefficient (R i) (T i) 1 (jb i) (η i) (smooth i) (rough i)) δ slot amp N

end CausalLowerbound.PartC
