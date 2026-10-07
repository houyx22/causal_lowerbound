import CausalLowerbound.PartB.Rademacher

/-!
# Exact matching at independent observation sites

Conditional on the baseline field, the paper uses different independent virtual
signs at each observation, even when sites share a block. This file builds that
product law explicitly. No independence of the baseline field is asserted.
-/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.PartB

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Ξ : ι → Type*} [∀ i, Fintype (Ξ i)]

/-- The joint full-jitter identity, conditional on any fixed baseline realization. -/
theorem joint_likelihood_bridge (laws : ∀ i, FiniteLaw (Ξ i))
    (δ : ∀ i, Ξ i → ℝ) (p c η R T : ι → ℝ)
    (hmean : ∀ i, (laws i).expect (δ i) = 0)
    (hthird : ∀ i, (laws i).expect (fun ω => δ i ω ^ 3) = 0)
    (hcorrection : ∀ i, 3 * η i * (laws i).expect (fun ω => δ i ω ^ 2) =
      (laws i).expect (fun ω => δ i ω ^ 4)) :
    (FiniteLaw.independent laws).expect (fun ω => ∏ i,
      codedLikelihood (R i) (T i) (p i + δ i (ω i))
        (cubic (c i) (η i) (p i + δ i (ω i))) 0) =
    ∏ i, codedLikelihood (R i) (T i) (p i)
      (cubic (c i) (η i) (p i) -
        (c i * (laws i).expect (fun ω => δ i ω ^ 2)) * (1 + 2 * p i))
      (c i * (laws i).expect (fun ω => δ i ω ^ 2)) := by
  rw [FiniteLaw.expect_independent_prod laws (fun i ω =>
    codedLikelihood (R i) (T i) (p i + δ i ω) (cubic (c i) (η i) (p i + δ i ω)) 0)]
  apply Finset.prod_congr rfl
  intro i _
  exact single_site_likelihood_bridge (laws i) (δ i) (p i) (c i) (η i)
    (hmean i) (hthird i) (hcorrection i) (R i) (T i)

/-- Joint matching with all moments supplied by the actual independent sign laws. -/
theorem joint_aggregate_likelihood_bridge (w : ι → List ℝ)
    (hw : ∀ i, sumSq (w i) = 1) (p c j R T : ι → ℝ) :
    (FiniteLaw.independent (fun i => signLaw (w i).length)).expect (fun ω => ∏ i,
      codedLikelihood (R i) (T i) (p i + j i * signSum (w i) (ω i))
        (cubic (c i) (j i ^ 2 / 3 * (3 - 2 * sumFourth (w i)))
          (p i + j i * signSum (w i) (ω i))) 0) =
    ∏ i, codedLikelihood (R i) (T i) (p i)
      (cubic (c i) (j i ^ 2 / 3 * (3 - 2 * sumFourth (w i))) (p i) -
        (c i * j i ^ 2) * (1 + 2 * p i)) (c i * j i ^ 2) := by
  rw [FiniteLaw.expect_independent_prod (fun i => signLaw (w i).length) (fun i ω =>
    codedLikelihood (R i) (T i) (p i + j i * signSum (w i) ω)
      (cubic (c i) (j i ^ 2 / 3 * (3 - 2 * sumFourth (w i)))
        (p i + j i * signSum (w i) ω)) 0)]
  apply Finset.prod_congr rfl
  intro i _
  exact aggregate_likelihood_bridge (w i) (hw i) (p i) (c i) (j i) (R i) (T i)

/-- Propensity-only characters match even for partial shifts. -/
theorem joint_propensity_match (laws : ∀ i, FiniteLaw (Ξ i))
    (δ : ∀ i, Ξ i → ℝ) (p : ι → ℝ)
    (hmean : ∀ i, (laws i).expect (δ i) = 0) :
    (FiniteLaw.independent laws).expect (fun ω => ∏ i, (p i + δ i (ω i))) =
      ∏ i, p i := by
  rw [FiniteLaw.expect_independent_prod laws (fun i ω => p i + δ i ω)]
  apply Finset.prod_congr rfl
  intro i _
  exact expect_shift (laws i) (δ i) (p i) (hmean i)

end CausalLowerbound.PartB
