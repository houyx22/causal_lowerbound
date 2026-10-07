import CausalLowerbound.PartB.CarrierProbability
import CausalLowerbound.PartB.MomentPerturbation
import Mathlib.Analysis.Normed.Group.Constructions

/-!
# Common-label coefficient laws for the positive carrier

The moment radius supplied by the finite-support lemma is used to build
conditional coefficient laws. Zero coefficient labels are handled explicitly.
-/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.PartB

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def normalizedCoefficient (K : ℝ) (a : V) : V := (K * ‖a‖)⁻¹ • a

theorem normalizedCoefficient_scale (K : ℝ) (hK : 0 < K) (a : V) :
    (K * ‖a‖) • normalizedCoefficient K a = a := by
  by_cases ha : a = 0
  · simp [ha, normalizedCoefficient]
  · have hw : K * ‖a‖ ≠ 0 := mul_ne_zero (ne_of_gt hK) (norm_ne_zero_iff.mpr ha)
    simp only [normalizedCoefficient, ← mul_smul, mul_inv_cancel₀ hw, one_smul]

theorem normalizedCoefficient_norm_le (K : ℝ) (hK : 0 < K) (a : V) :
    ‖normalizedCoefficient K a‖ ≤ K⁻¹ := by
  by_cases ha : a = 0
  · simp only [ha, normalizedCoefficient, smul_zero, norm_zero]
    exact inv_nonneg.mpr hK.le
  · have ha' : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
    rw [normalizedCoefficient, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (mul_nonneg hK.le (norm_nonneg _))), mul_inv_rev]
    calc
      _ = K⁻¹ * (‖a‖⁻¹ * ‖a‖) := by ring
      _ = K⁻¹ := by rw [inv_mul_cancel₀ ha', mul_one]
      _ ≤ _ := le_rfl

variable {I Γ : Type*} [Fintype I] [Fintype Γ]

theorem normalizedCoefficient_coord_le (K : ℝ) (hK : 0 < K) (a : I → ℝ) (i : I) :
    |normalizedCoefficient K a i| ≤ K⁻¹ := by
  have h : ‖normalizedCoefficient K a i‖ ≤ ‖normalizedCoefficient K a‖ := norm_le_pi_norm _ i
  exact h.trans (normalizedCoefficient_norm_le K hK a)

/-- The two kernels share the entire label law and the same finite coefficient
sample space. The baseline kernel is constant; label zero has no perturbation. -/
theorem exists_carrier_kernel (feature : I → Γ → ℝ) (μ : FiniteLaw Γ)
    (δ : ℝ)
    (realize : ∀ v : I → ℝ, (∀ i, |v i| ≤ δ) →
      ∃ ν : FiniteLaw Γ, (∀ x, 0 < ν.weight x) ∧
        ∀ i, ν.expect (feature i) = μ.expect (feature i) + v i)
    (a : ℕ → I → ℝ) (K : ℝ) (hK : 0 < K) (hδ : K⁻¹ ≤ δ) :
    ∃ kernel : ℕ → FiniteLaw Γ, kernel 0 = μ ∧
      (∀ m x, 0 < (kernel (m + 1)).weight x) ∧
      ∀ m i, (kernel (m + 1)).expect (feature i) =
        μ.expect (feature i) + normalizedCoefficient K (a m) i := by
  have hex : ∀ m, ∃ ν : FiniteLaw Γ, (∀ x, 0 < ν.weight x) ∧
      ∀ i, ν.expect (feature i) = μ.expect (feature i) + normalizedCoefficient K (a m) i := by
    intro m
    apply realize
    intro i
    exact (normalizedCoefficient_coord_le K hK (a m) i).trans hδ
  choose ν hνpos hνmom using hex
  refine ⟨(fun n => match n with | 0 => μ | m + 1 => ν m), rfl, hνpos, hνmom⟩

open scoped BigOperators

/-- The master moment equality for genuine countable-label joint laws.
Positive polarization will identify the series on the right with D*J_n. -/
theorem carrier_master_moment (feature : I → Γ → ℝ) (μ : FiniteLaw Γ)
    (a : ℕ → I → ℝ) (ha : Summable (fun m => ‖a m‖))
    (K : ℝ) (hK : 0 < K) (H : DiscreteLaw ℕ)
    (hweight : ∀ m, H.weight (m + 1) = K * ‖a m‖)
    (kernel : ℕ → FiniteLaw Γ) (hzero : kernel 0 = μ)
    (hmoment : ∀ m i, (kernel (m + 1)).expect (feature i) =
      μ.expect (feature i) + normalizedCoefficient K (a m) i)
    (g : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hg : ∀ n, |g n| ≤ C) (i : I) :
    (H.joint kernel).expect (fun z => g z.1 * feature i z.2) -
      (H.joint (fun _ => μ)).expect (fun z => g z.1 * feature i z.2) =
      ∑' m, g (m + 1) * a m i := by
  classical
  have hfeature : ∀ x, |feature i x| ≤ ∑ y, |feature i y| := fun x =>
    Finset.single_le_sum (f := fun y => |feature i y|)
      (fun y _ => abs_nonneg _) (Finset.mem_univ x)
  rw [H.weighted_moment_difference (fun _ => μ) kernel g (feature i)
    C (∑ y, |feature i y|) hC hg hfeature]
  have hs : Summable (fun m => g (m + 1) * a m i) := by
    apply Summable.of_norm_bounded (fun m => C * ‖a m‖) (ha.mul_left C)
    intro m
    rw [Real.norm_eq_abs, abs_mul]
    have hcoord : |a m i| ≤ ‖a m‖ := norm_le_pi_norm (a m) i
    exact mul_le_mul (hg (m + 1)) hcoord (abs_nonneg _) hC
  let s : ℕ → ℝ := fun n => H.weight n * (g n *
    ((kernel n).expect (feature i) - μ.expect (feature i)))
  have hz : s 0 = 0 := by simp [s, hzero]
  have htail : ∀ m, s (m + 1) = g (m + 1) * a m i := by
    intro m
    have he := congrFun (normalizedCoefficient_scale K hK (a m)) i
    change (K * ‖a m‖) * normalizedCoefficient K (a m) i = a m i at he
    dsimp [s]
    rw [hweight m, hmoment m i]
    calc
      _ = g (m + 1) * ((K * ‖a m‖) * normalizedCoefficient K (a m) i) := by ring
      _ = _ := by rw [he]
  have hs' : HasSum (fun m => s (m + 1)) (∑' m, g (m + 1) * a m i) := by
    simpa only [htail] using hs.hasSum
  have h := (hasSum_nat_add_iff (f := s) 1).mp hs'
  simp only [Finset.sum_range_one, hz, add_zero] at h
  exact h.tsum_eq

end CausalLowerbound.PartB
