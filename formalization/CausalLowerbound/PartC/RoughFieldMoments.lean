import CausalLowerbound.PartC.SingleSiteBridge

/-! Discharging all moment hypotheses of the mixed bridges using the
actual product Rademacher law. The correction is polynomial in the
envelope and packet weights, including where the envelope vanishes. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace CausalLowerbound.PartC
variable {K : Type*} [Fintype K] [DecidableEq K]

def roughField (G : ℝ) (w : K → ℝ) (ζ : K → Bool) : ℝ :=
  G * PartB.independentSignSum w ζ

def fourthCorrection (ja G : ℝ) (w : K → ℝ) : ℝ :=
  ja ^ 2 * G ^ 2 * (3 - 2 * ∑ k, w k ^ 4)

theorem roughField_moments (G : ℝ) (w : K → ℝ) (hw : ∑ k, w k ^ 2 = 1) :
    PartB.independentSigns.expect (roughField G w) = 0 ∧
    PartB.independentSigns.expect (fun ζ => roughField G w ζ ^ 2) = G ^ 2 ∧
    PartB.independentSigns.expect (fun ζ => roughField G w ζ ^ 3) = 0 ∧
    PartB.independentSigns.expect (fun ζ => roughField G w ζ ^ 4) =
      G ^ 4 * (3 - 2 * ∑ k, w k ^ 4) := by
  obtain ⟨hmean, hvar, hthird, hfourth⟩ := PartB.independentSignSum_moments w
  unfold roughField
  simp only [mul_pow, FiniteLaw.expect_mul, hmean, hvar, hthird, hfourth, hw]
  norm_num

theorem fourthCorrection_identity (ja jb G : ℝ) (w : K → ℝ) (hw : ∑ k, w k ^ 2 = 1) :
    (ja * jb * G ^ 2) * fourthCorrection ja G w =
      ja ^ 3 * jb * PartB.independentSigns.expect (fun ζ => roughField G w ζ ^ 4) := by
  rw [(roughField_moments G w hw).2.2.2]
  unfold fourthCorrection
  ring

theorem roughPropensity_design_bridge (R T ja jb G : ℝ) (w : K → ℝ)
    (hw : ∑ k, w k ^ 2 = 1) (f : ℕ) (hf : f ≤ 1) :
    PartB.independentSigns.expect (fun ζ =>
      RoughPropensity.substitution f ja (G ^ 2) (roughField G w ζ) *
      RoughPropensity.increment R T ja jb (roughField G w ζ)) =
    PartB.independentSigns.expect (fun ζ => roughField G w ζ ^ f *
      RoughPropensity.realField R T ja (ja * jb * G ^ 2) (roughField G w ζ)) := by
  have hm := roughField_moments G w hw
  exact RoughPropensity.design_weighted_bridge _ _ R T ja jb (G ^ 2) hm.1 hm.2.1 f hf

theorem roughOutcome_design_bridge (R T ja jb p G : ℝ) (w : K → ℝ)
    (hw : ∑ k, w k ^ 2 = 1) (f : ℕ) :
    PartB.independentSigns.expect (fun ζ =>
      RoughOutcome.substitution 1 f PartB.independentSigns (roughField G w) (roughField G w ζ) *
        RoughOutcome.incrementOne R T ja jb (fourthCorrection ja G w) p (roughField G w ζ) +
      RoughOutcome.substitution 2 f PartB.independentSigns (roughField G w) (roughField G w ζ) *
        RoughOutcome.incrementTwo R T ja jb p (roughField G w ζ) +
      RoughOutcome.substitution 3 f PartB.independentSigns (roughField G w) (roughField G w ζ) *
        RoughOutcome.incrementThree R T ja jb (roughField G w ζ)) =
    PartB.independentSigns.expect (fun ζ =>
      roughField G w ζ ^ f * RoughOutcome.realField R T p (ja * jb * G ^ 2)) := by
  have hm := roughField_moments G w hw
  exact RoughOutcome.design_weighted_bridge _ _ R T ja jb (fourthCorrection ja G w) p
    (G ^ 2) hm.1 hm.2.1 hm.2.2.1 (fourthCorrection_identity ja jb G w hw) f

theorem fourthCorrection_bounds (ja G : ℝ) (w : K → ℝ) (hw : ∑ k, w k ^ 2 = 1) :
    0 ≤ fourthCorrection ja G w ∧ fourthCorrection ja G w ≤ 3 * ja ^ 2 * G ^ 2 := by
  have hfour : 0 ≤ ∑ k, w k ^ 4 := Finset.sum_nonneg (fun _ _ => by positivity)
  have hle : (∑ k, w k ^ 4) ≤ 1 := by
    calc
      _ = ∑ k, (w k ^ 2) ^ 2 := by apply Finset.sum_congr rfl; intro k _; ring
      _ ≤ (∑ k, w k ^ 2) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => sq_nonneg _)
      _ = 1 := by rw [hw]; norm_num
  unfold fourthCorrection
  constructor
  · exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (by linarith)
  · nlinarith [mul_nonneg (mul_nonneg (sq_nonneg ja) (sq_nonneg G)) hfour]

end CausalLowerbound.PartC
