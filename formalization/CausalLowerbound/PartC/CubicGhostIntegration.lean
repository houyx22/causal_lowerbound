import CausalLowerbound.PartC.BlockCubicFunctional
import CausalLowerbound.PartC.CubeGhostIntegrability

/-! Integrating cubic block functionals over independent ghost cubes
integrates each pattern weight. Integrability follows from continuity on
the compact cubes, with no external integrability assumption. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry MvPolynomial Representative
variable {d K V : Type*} [Fintype d] [Fintype K] [DecidableEq K]
  [Fintype V] [DecidableEq V]

theorem block_cubic_cube_integral (G : K → Type*) [∀ k, Fintype (G k)]
    (w : ∀ k, (G k → d → ℝ) → Degree V 3 → ℝ)
    (hw : ∀ k f, Continuous (fun g => w k g f)) (p : MvPolynomial (K × V) ℝ) :
    (∫ ghost : ∀ k, G k → d → ℝ,
      blockPolynomialFunctional (fun k => cubicSiteFunctional (w k (ghost k))) p
        ∂Measure.pi (fun k => Measure.pi (fun _ : G k => cubeMeasure d))) =
      blockPolynomialFunctional (fun k => cubicSiteFunctional (fun f =>
        ∫ g : G k → d → ℝ, w k g f ∂Measure.pi (fun _ : G k => cubeMeasure d))) p := by
  let μ := fun k => Measure.pi (fun _ : G k => cubeMeasure d)
  have hi (m : (K × V) →₀ ℕ) :
      Integrable (fun ghost : ∀ k, G k → d → ℝ => p.coeff m *
        (if hm : ∀ v, m v ≤ 3 then ∏ k, w k (ghost k) (fun v => cubicSiteDegree m hm (k, v)) else 0))
          (Measure.pi μ) := by
    apply continuous_integrable_cubeBlocks G
    by_cases hm : ∀ v, m v ≤ 3
    · simp only [dif_pos hm]
      apply continuous_const.mul
      apply continuous_finset_prod
      intro k _
      exact (hw k _).comp (continuous_apply k)
    · simp only [dif_neg hm, mul_zero]
      exact continuous_const
  simp_rw [blockPolynomialFunctional_expansion, block_cubic_pattern_product]
  rw [integral_finset_sum p.support (fun m _ => hi m)]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : ∀ v, m v ≤ 3
  · simp only [dif_pos hm]
    rw [integral_const_mul]
    apply congrArg (fun z : ℝ => p.coeff m * z)
    exact @integral_fintype_prod_eq_prod ℝ inferInstance K inferInstance (fun k => G k → d → ℝ)
      (fun k g => w k g (fun v => cubicSiteDegree m hm (k, v)))
      (fun k => ⟨μ k⟩) (fun k => inferInstanceAs (SigmaFinite (μ k)))
  · simp only [dif_neg hm, mul_zero, integral_zero]

end CausalLowerbound.PartC
