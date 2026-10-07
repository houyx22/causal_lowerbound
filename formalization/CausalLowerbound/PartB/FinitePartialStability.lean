import CausalLowerbound.PartB.FiniteRademacher
import CausalLowerbound.PartB.BinaryExperiment

/-! Partial-jitter stability for the actual finite block sign product,
with every sign moment proved from that probability law. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
namespace CausalLowerbound.PartB
variable {K : Type*} [Fintype K] [DecidableEq K]

def maskedWeights (w : K → ℝ) (active : K → Bool) (k : K) : ℝ := if active k then w k else 0

theorem masked_variance_le (w : K → ℝ) (active : K → Bool) :
    (∑ k, maskedWeights w active k ^ 2) ≤ ∑ k, w k ^ 2 := by
  apply Finset.sum_le_sum
  intro k _
  cases hk : active k <;> simp [maskedWeights, hk, sq_nonneg]

theorem finite_sign_fourth_bound (w : K → ℝ) :
    independentSigns.expect (fun ζ => independentSignSum w ζ ^ 4) ≤ 3 * (∑ k, w k ^ 2) ^ 2 := by
  rw [(independentSignSum_moments w).2.2.2]
  exact sub_le_self _ (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => by positivity)))

theorem finite_partial_moments (w : K → ℝ) (active : K → Bool) :
    independentSigns.expect (independentSignSum (maskedWeights w active)) = 0 ∧
    independentSigns.expect (fun ζ => independentSignSum (maskedWeights w active) ζ ^ 3) = 0 ∧
    0 ≤ independentSigns.expect (fun ζ => independentSignSum (maskedWeights w active) ζ ^ 2) ∧
    independentSigns.expect (fun ζ => independentSignSum (maskedWeights w active) ζ ^ 2) ≤ ∑ k, w k ^ 2 ∧
    0 ≤ independentSigns.expect (fun ζ => independentSignSum (maskedWeights w active) ζ ^ 4) ∧
    independentSigns.expect (fun ζ => independentSignSum (maskedWeights w active) ζ ^ 4) ≤
      3 * (∑ k, w k ^ 2) ^ 2 := by
  have hm := independentSignSum_moments (maskedWeights w active)
  have hs := masked_variance_le w active
  have hs0 : 0 ≤ ∑ k, maskedWeights w active k ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  refine ⟨hm.1, hm.2.2.1, independentSigns.expect_nonneg _ (fun _ => sq_nonneg _),
    hm.2.1.le.trans hs, independentSigns.expect_nonneg _ (fun _ => by positivity), ?_⟩
  exact (finite_sign_fourth_bound _).trans (by nlinarith)

theorem finite_partial_walsh_stability (w : K → ℝ) (active : K → Bool)
    (p c η : ℝ) (hp : |p| ≤ 1) (hc : 0 ≤ c) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hv1 : (∑ k, w k ^ 2) ≤ 1)
    (hcorrection : 3 * η * (∑ k, w k ^ 2) = 3 * (∑ k, w k ^ 2) ^ 2 - 2 * ∑ k, w k ^ 4)
    (χ : WalshCharacter) :
    |independentSigns.expect (fun ζ => walshCoefficient χ
        (p + independentSignSum (maskedWeights w active) ζ)
        (cubic c η (p + independentSignSum (maskedWeights w active) ζ)) 0) -
      walshCoefficient χ p (cubic c η p - (c * (∑ k, w k ^ 2)) * (1 + 2 * p))
        (c * (∑ k, w k ^ 2))| ≤ 3 * (c * (∑ k, w k ^ 2)) := by
  obtain ⟨hmean, hthird, hs0, hsv, hms0, hms⟩ := finite_partial_moments w active
  rw [expect_walsh _ _ _ _ _ hmean hthird]
  apply partial_walsh_stability χ p c η (∑ k, w k ^ 2) _
    (independentSigns.expect (fun ζ => independentSignSum w ζ ^ 4)) _
    hp hc hη0 hη1 (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hv1 hs0 hsv
    (independentSigns.expect_nonneg _ (fun _ => by positivity))
    (finite_sign_fourth_bound w) hms0 hms
  rw [(independentSignSum_moments w).2.2.2]
  exact hcorrection

theorem finite_full_likelihood_match (w : K → ℝ) (p c η R T : ℝ)
    (hcorrection : 3 * η * (∑ k, w k ^ 2) = 3 * (∑ k, w k ^ 2) ^ 2 - 2 * ∑ k, w k ^ 4) :
    independentSigns.expect (fun ζ => codedLikelihood R T (p + independentSignSum w ζ)
      (cubic c η (p + independentSignSum w ζ)) 0) =
      codedLikelihood R T p (cubic c η p - (c * (∑ k, w k ^ 2)) * (1 + 2 * p))
        (c * (∑ k, w k ^ 2)) := by
  obtain ⟨hmean, hvar, hthird, hfourth⟩ := independentSignSum_moments w
  have he := single_site_likelihood_bridge independentSigns (independentSignSum w) p c η
    hmean hthird (by rw [hvar, hfourth]; exact hcorrection) R T
  simpa only [hvar] using he

theorem codedLikelihood_walsh (R T p y τ : ℝ) :
    codedLikelihood R T p y τ = 1 + R * p +
      T * walshCoefficient .outcome p y τ + R * T * walshCoefficient .interaction p y τ := rfl

/-- The difference is of order c*v, even though the retained signs are a
proper subset of blocks. This is a bound on the full binary likelihood. -/
theorem finite_partial_likelihood_stability (w : K → ℝ) (active : K → Bool)
    (p c η : ℝ) (hp : |p| ≤ 1) (hc : 0 ≤ c) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hv1 : (∑ k, w k ^ 2) ≤ 1)
    (hcorrection : 3 * η * (∑ k, w k ^ 2) = 3 * (∑ k, w k ^ 2) ^ 2 - 2 * ∑ k, w k ^ 4)
    (R T : Bool) :
    |independentSigns.expect (fun ζ => codedLikelihood (sign R) (sign T)
        (p + independentSignSum (maskedWeights w active) ζ)
        (cubic c η (p + independentSignSum (maskedWeights w active) ζ)) 0) -
      codedLikelihood (sign R) (sign T) p
        (cubic c η p - (c * (∑ k, w k ^ 2)) * (1 + 2 * p)) (c * (∑ k, w k ^ 2))| ≤
      6 * (c * (∑ k, w k ^ 2)) := by
  let A : WalshCharacter → ℝ := fun χ => independentSigns.expect (fun ζ => walshCoefficient χ
    (p + independentSignSum (maskedWeights w active) ζ)
    (cubic c η (p + independentSignSum (maskedWeights w active) ζ)) 0) -
      walshCoefficient χ p (cubic c η p - (c * (∑ k, w k ^ 2)) * (1 + 2 * p))
        (c * (∑ k, w k ^ 2))
  have hA (χ : WalshCharacter) : |A χ| ≤ 3 * (c * (∑ k, w k ^ 2)) :=
    finite_partial_walsh_stability w active p c η hp hc hη0 hη1 hv1 hcorrection χ
  have he : independentSigns.expect (fun ζ => codedLikelihood (sign R) (sign T)
        (p + independentSignSum (maskedWeights w active) ζ)
        (cubic c η (p + independentSignSum (maskedWeights w active) ζ)) 0) -
      codedLikelihood (sign R) (sign T) p
        (cubic c η p - (c * (∑ k, w k ^ 2)) * (1 + 2 * p)) (c * (∑ k, w k ^ 2)) =
      sign T * A .outcome + sign R * sign T * A .interaction := by
    simp_rw [codedLikelihood_walsh, FiniteLaw.expect_add, FiniteLaw.expect_mul, FiniteLaw.expect_const]
    rw [expect_shift _ _ _ (finite_partial_moments w active).1]
    dsimp only [A]
    ring
  rw [he]
  calc
    _ ≤ |sign T * A .outcome| + |sign R * sign T * A .interaction| := abs_add _ _
    _ = |A .outcome| + |A .interaction| := by simp [abs_mul, abs_sign]
    _ ≤ _ := by linarith [hA .outcome, hA .interaction]

end CausalLowerbound.PartB
