import CausalLowerbound.FiniteExpectation
import Mathlib.Tactic.Ring

/-!
# Part B: the aggregate cubic bridge

Source: `LowerBound_Complete_Revised.tex`, labels `B:eq:cubic`, `B:eq:u`,
`B:lem:cubic`, `B:eq:partial-k`, and `B:eq:partial-pk`.

Here `c = b / a`, `v = E[δ²]`, and `d_* = c * v`. The correction is expressed
without division as `3 * η * v = E[δ⁴]`. This includes the zero-variance case.
Only the first and third moments of δ are assumed to vanish; the cubic bridge
itself and the complete coded-likelihood identity are proved below.
-/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.PartB

open FiniteLaw

variable {Ω : Type*} [Fintype Ω]

/-- The polynomial in `B:eq:cubic`, with `c = b / a`. -/
def cubic (c η z : ℝ) : ℝ := c * (1 + η) * z - (c / 3) * z ^ 3

/-- The coded likelihood from Part I. For binary `R,T`, the cell mass is `L/4`.
The treatment effect `τ` is on the original, uncoded outcome scale. -/
def codedLikelihood (R T p y τ : ℝ) : ℝ :=
  1 + R * p + T * (y + τ * (1 + p)) + R * T * (p * y + τ * (1 + p))

/-- For a binary treatment sign, the coded likelihood is the product of the
propensity and conditional-outcome factors. Dividing by four gives the cell mass. -/
theorem codedLikelihood_eq_factors (R T p y τ : ℝ) (hR : R ^ 2 = 1) :
    codedLikelihood R T p y τ =
      (1 + R * p) * (1 + T * (y + τ * (1 + R))) := by
  symm
  calc
    _ = codedLikelihood R T p y τ + (R ^ 2 - 1) * (p * T * τ) := by
      unfold codedLikelihood
      ring
    _ = _ := by rw [hR]; ring

section ShiftedMoments

variable (μ : FiniteLaw Ω) (δ : Ω → ℝ) (p : ℝ)
variable (hmean : μ.expect δ = 0)
variable (hthird : μ.expect (fun ω => δ ω ^ 3) = 0)

include hmean

theorem expect_shift : μ.expect (fun ω => p + δ ω) = p := by
  rw [μ.expect_add, μ.expect_const, hmean, add_zero]

theorem expect_shift_sq :
    μ.expect (fun ω => (p + δ ω) ^ 2) =
      p ^ 2 + μ.expect (fun ω => δ ω ^ 2) := by
  calc
    _ = μ.expect (fun ω => p ^ 2 + (2 * p) * δ ω + δ ω ^ 2) := by
      apply μ.expect_congr
      intro ω
      ring
    _ = _ := by
      rw [μ.expect_add, μ.expect_add, μ.expect_const, μ.expect_mul, hmean]
      ring

include hthird

theorem expect_shift_cube :
    μ.expect (fun ω => (p + δ ω) ^ 3) =
      p ^ 3 + (3 * p) * μ.expect (fun ω => δ ω ^ 2) := by
  calc
    _ = μ.expect (fun ω =>
        p ^ 3 + (3 * p ^ 2) * δ ω + (3 * p) * δ ω ^ 2 + δ ω ^ 3) := by
      apply μ.expect_congr
      intro ω
      ring
    _ = _ := by
      simp only [μ.expect_add, μ.expect_const, μ.expect_mul, hmean, hthird]
      ring

theorem expect_shift_fourth :
    μ.expect (fun ω => (p + δ ω) ^ 4) =
      p ^ 4 + (6 * p ^ 2) * μ.expect (fun ω => δ ω ^ 2) +
        μ.expect (fun ω => δ ω ^ 4) := by
  calc
    _ = μ.expect (fun ω => p ^ 4 + (4 * p ^ 3) * δ ω +
        (6 * p ^ 2) * δ ω ^ 2 + (4 * p) * δ ω ^ 3 + δ ω ^ 4) := by
      apply μ.expect_congr
      intro ω
      ring
    _ = _ := by
      simp only [μ.expect_add, μ.expect_const, μ.expect_mul, hmean, hthird]
      ring

end ShiftedMoments

section CubicMoments

variable (μ : FiniteLaw Ω) (δ : Ω → ℝ) (p c η : ℝ)
variable (hmean : μ.expect δ = 0)
variable (hthird : μ.expect (fun ω => δ ω ^ 3) = 0)

include hmean hthird

/-- `B:eq:partial-k`, valid before imposing the fourth-moment correction. -/
theorem expect_cubic :
    μ.expect (fun ω => cubic c η (p + δ ω)) =
      cubic c η p - c * p * μ.expect (fun ω => δ ω ^ 2) := by
  simp only [cubic, μ.expect_sub, μ.expect_mul]
  rw [expect_shift μ δ p hmean, expect_shift_cube μ δ p hmean hthird]
  ring

/-- `B:eq:partial-pk`, also valid for any partial block shift. -/
theorem expect_mul_cubic :
    μ.expect (fun ω => (p + δ ω) * cubic c η (p + δ ω)) =
      p * cubic c η p + c * (1 + η) * μ.expect (fun ω => δ ω ^ 2) -
        (c / 3) * (6 * p ^ 2 * μ.expect (fun ω => δ ω ^ 2) +
          μ.expect (fun ω => δ ω ^ 4)) := by
  calc
    _ = μ.expect (fun ω => c * (1 + η) * (p + δ ω) ^ 2 -
        (c / 3) * (p + δ ω) ^ 4) := by
      apply μ.expect_congr
      intro ω
      unfold cubic
      ring
    _ = _ := by
      rw [μ.expect_sub, μ.expect_mul, μ.expect_mul,
        expect_shift_sq μ δ p hmean, expect_shift_fourth μ δ p hmean hthird]
      unfold cubic
      ring

variable (hcorrection :
  3 * η * μ.expect (fun ω => δ ω ^ 2) = μ.expect (fun ω => δ ω ^ 4))

include hcorrection

/-- The fourth entry in the Walsh-vector identity `B:eq:walsh-vector`. -/
theorem expect_mul_cubic_corrected :
    μ.expect (fun ω => (p + δ ω) * cubic c η (p + δ ω)) =
      p * (cubic c η p - (c * μ.expect (fun ω => δ ω ^ 2)) * p) +
        (c * μ.expect (fun ω => δ ω ^ 2)) * (1 - p ^ 2) := by
  rw [expect_mul_cubic μ δ p c η hmean hthird, ← hcorrection]
  ring

/-- The cubic covariance identity `B:lem:cubic`, with an actual finite law. -/
theorem cubic_covariance :
    μ.covariance (fun ω => p + δ ω) (fun ω => cubic c η (p + δ ω)) =
      (c * μ.expect (fun ω => δ ω ^ 2)) * (1 - p ^ 2) := by
  unfold FiniteLaw.covariance
  rw [expect_mul_cubic_corrected μ δ p c η hmean hthird hcorrection,
    expect_shift μ δ p hmean, expect_cubic μ δ p c η hmean hthird]
  ring

/-- Averaging the virtual Q-side likelihood gives exactly the actual P-side
likelihood. The identity holds for all real R,T, in particular for binary cells. -/
theorem single_site_likelihood_bridge (R T : ℝ) :
    μ.expect (fun ω => codedLikelihood R T (p + δ ω) (cubic c η (p + δ ω)) 0) =
      codedLikelihood R T p
        (cubic c η p - (c * μ.expect (fun ω => δ ω ^ 2)) * (1 + 2 * p))
        (c * μ.expect (fun ω => δ ω ^ 2)) := by
  calc
    _ = μ.expect (fun ω => 1 + R * (p + δ ω) + T * cubic c η (p + δ ω) +
        (R * T) * ((p + δ ω) * cubic c η (p + δ ω))) := by
      apply μ.expect_congr
      intro ω
      unfold codedLikelihood
      ring
    _ = _ := by
      simp only [μ.expect_add, μ.expect_const, μ.expect_mul]
      rw [hmean, expect_cubic μ δ p c η hmean hthird,
        expect_mul_cubic_corrected μ δ p c η hmean hthird hcorrection]
      unfold codedLikelihood
      ring

end CubicMoments
end CausalLowerbound.PartB
