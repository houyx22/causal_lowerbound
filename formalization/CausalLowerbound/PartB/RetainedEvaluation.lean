import CausalLowerbound.PartB.VirtualShift
import CausalLowerbound.PartB.IdealIncrementDiagonal

/-! After evaluation, the virtual shift at retained sites is independent
of the ghost coordinates. This holds for every function of the retained
evaluations, and therefore in particular for likelihood polynomials. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace CausalLowerbound.PartB.ShellGeometry
open ConfigurationShells
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d V J Ω : Type*} [Fintype d] [DecidableEq d]
  [Fintype V] [LinearOrder V] [Fintype Ω]

theorem taper_nonzero_chord_ne_zero (u : V × d → ℝ) (ε : ℝ)
    (hχ : graphTaper edgeLeft edgeRight taperCutoff ε (graphDistance edgeLeft edgeRight u) ≠ 0) :
    ∀ i j, i ≠ j → chordDistance (configurationSite u i) (configurationSite u j) ≠ 0 := by
  intro i j hij hz
  have he (a b : V) (hab : a < b)
      (hz : chordDistance (configurationSite u a) (configurationSite u b) = 0) : False := by
    apply hχ
    apply graphTaper_zero_of_zero_edge edgeLeft edgeRight ε _ (⟨(a, b), hab⟩ : CompleteEdge V)
    change distanceCap (chordDistance (configurationSite u a) (configurationSite u b)) = 0
    rw [hz]
    exact distanceCap_small (by norm_num)
  rcases lt_or_gt_of_ne hij with h | h
  · exact he i j h hz
  · exact he j i h (by rw [chordDistance_symm]; exact hz)

theorem retained_shift_evaluation (Q : ℕ) (hQ : 0 < Q) (hcard : Fintype.card V ≤ Q)
    (U : CoefficientExponent d Q → ℝ) (u : V × d → ℝ) (ε t : ℝ) (ζ : V → ℝ)
    (keep : J → V) (sites : J → d → ℝ) (hkeep : ∀ j, configurationSite u (keep j) = sites j)
    (ψ : J → ℝ) (f : (J → ℝ) → ℝ)
    (hχ : graphTaper edgeLeft edgeRight taperCutoff ε (graphDistance edgeLeft edgeRight u) ≠ 0) :
    f (fun j => ψ j * coefficientEvaluation (virtualCoefficientShift U u t ζ) (sites j)) =
      f (fun j => ψ j * (coefficientEvaluation U (sites j) + t * ζ (keep j))) := by
  congr 1
  funext j
  rw [← hkeep j, virtualCoefficientShift_evaluation Q hQ hcard U u
    (taper_nonzero_chord_ne_zero u ε hχ)]

/-- Ghost signs may remain in the expectation: the integrand depends only
on the retained signs, so they require no additional independence premise. -/
theorem retained_virtual_moment (Q : ℕ) (hQ : 0 < Q) (hcard : Fintype.card V ≤ Q)
    (μ : FiniteLaw Ω) (U : Ω → CoefficientExponent d Q → ℝ)
    (u : V × d → ℝ) (ε t : ℝ) (keep : J → V) (sites : J → d → ℝ)
    (hkeep : ∀ j, configurationSite u (keep j) = sites j)
    (ψ : J → ℝ) (f : (J → ℝ) → ℝ) :
    graphTaper edgeLeft edgeRight taperCutoff ε (graphDistance edgeLeft edgeRight u) *
      ((μ.prod (independentSigns (ι := V))).expect (fun z =>
        f (fun j => ψ j * coefficientEvaluation
          (virtualCoefficientShift (U z.1) u t (fun i => sign (z.2 i))) (sites j)))
        - μ.expect (fun s => f (fun j => ψ j * coefficientEvaluation (U s) (sites j)))) =
    graphTaper edgeLeft edgeRight taperCutoff ε (graphDistance edgeLeft edgeRight u) *
      ((μ.prod (independentSigns (ι := V))).expect (fun z =>
        f (fun j => ψ j * (coefficientEvaluation (U z.1) (sites j) + t * sign (z.2 (keep j)))))
        - μ.expect (fun s => f (fun j => ψ j * coefficientEvaluation (U s) (sites j)))) := by
  by_cases hχ : graphTaper edgeLeft edgeRight taperCutoff ε (graphDistance edgeLeft edgeRight u) = 0
  · simp only [hχ, zero_mul]
  · congr 2
    apply FiniteLaw.expect_congr
    intro z
    exact retained_shift_evaluation Q hQ hcard (U z.1) u ε t _ keep sites hkeep ψ f hχ

end CausalLowerbound.PartB.ShellGeometry
