import CausalLowerbound.FiniteBounds
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# The countable positive-carrier fixed point

This is the Banach-space step in `B:prop:carrier`. The countable coefficient
map is assumed to have the absolute summability and Lipschitz bounds that
Wiener polarization must supply. Convergence, contraction, existence,
uniqueness, the radius bound, and the probability-mass bound are proved here.
Neither the Wiener algebra nor its polarization operator is constructed here.
-/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.PartB

open scoped NNReal

variable {E V : Type*} [NormedAddCommGroup E] [NormedAddCommGroup V]

/-- For the paper, L = C_pol * δ_n and coeff D is the polarization of D*J_n. -/
structure CarrierCoefficients (E V : Type*) [NormedAddCommGroup E] [NormedAddCommGroup V]
    (L : ℝ) where
  coeff : E → ℕ → V
  summable_norm : ∀ D, Summable (fun m => ‖coeff D m‖)
  zero : ∀ m, coeff 0 m = 0
  difference_bound : ∀ D D',
    (∑' m, ‖coeff D m - coeff D' m‖) ≤ L * ‖D - D'‖

theorem summable_bounded_synthesis [NormedSpace ℝ E] [CompleteSpace E]
    (b : ℕ → ℝ) (hb : Summable (fun m => |b m|))
    (G : ℕ → E) (M : ℝ) (hG : ∀ m, ‖G m‖ ≤ M) :
    Summable (fun m => b m • G m) := by
  apply Summable.of_norm_bounded (fun m => M * |b m|) (hb.mul_left M)
  intro m
  rw [norm_smul, Real.norm_eq_abs, mul_comm M]
  exact mul_le_mul_of_nonneg_left (hG m) (abs_nonneg _)

theorem norm_bounded_synthesis [NormedSpace ℝ E]
    (b : ℕ → ℝ) (hb : Summable (fun m => |b m|))
    (G : ℕ → E) (M : ℝ) (hG : ∀ m, ‖G m‖ ≤ M) :
    ‖∑' m, b m • G m‖ ≤ M * ∑' m, |b m| := by
  apply tsum_of_norm_bounded (hb.hasSum.mul_left M)
  intro m
  rw [norm_smul, Real.norm_eq_abs, mul_comm M]
  exact mul_le_mul_of_nonneg_left (hG m) (abs_nonneg _)

namespace CarrierCoefficients

variable {L : ℝ} (A : CarrierCoefficients E V L)

def weight (K : ℝ) (D : E) (m : ℕ) : ℝ := K * ‖A.coeff D m‖

def mass (K : ℝ) (D : E) : ℝ := ∑' m, A.weight K D m

def update [NormedSpace ℝ E] (K : ℝ) (e : E) (F : ℕ → E) (D : E) : E :=
  e + ∑' m, A.weight K D m • (F m - e)

theorem norm_sum_bound (D : E) : (∑' m, ‖A.coeff D m‖) ≤ L * ‖D‖ := by
  simpa only [A.zero, sub_zero] using A.difference_bound D 0

theorem weight_nonneg (K : ℝ) (hK : 0 ≤ K) (D : E) (m : ℕ) :
    0 ≤ A.weight K D m := mul_nonneg hK (norm_nonneg _)

theorem weight_summable (K : ℝ) (D : E) : Summable (A.weight K D) :=
  (A.summable_norm D).mul_left K

theorem mass_eq (K : ℝ) (D : E) : A.mass K D = K * ∑' m, ‖A.coeff D m‖ := by
  exact tsum_mul_left

theorem mass_nonneg (K : ℝ) (hK : 0 ≤ K) (D : E) : 0 ≤ A.mass K D :=
  tsum_nonneg (A.weight_nonneg K hK D)

theorem mass_bound (K : ℝ) (hK : 0 ≤ K) (D : E) : A.mass K D ≤ K * L * ‖D‖ := by
  rw [A.mass_eq]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (A.norm_sum_bound D) hK

theorem weight_abs_summable (K : ℝ) (hK : 0 ≤ K) (D : E) :
    Summable (fun m => |A.weight K D m|) := by
  simpa only [abs_of_nonneg (A.weight_nonneg K hK D _)] using A.weight_summable K D

theorem update_summable [NormedSpace ℝ E] [CompleteSpace E]
    (K : ℝ) (hK : 0 ≤ K) (e : E) (F : ℕ → E)
    (M : ℝ) (hF : ∀ m, ‖F m - e‖ ≤ M) (D : E) :
    Summable (fun m => A.weight K D m • (F m - e)) :=
  summable_bounded_synthesis _ (A.weight_abs_summable K hK D) _ M hF

theorem update_distance_bound [NormedSpace ℝ E]
    (K : ℝ) (hK : 0 ≤ K) (e : E) (F : ℕ → E)
    (M : ℝ) (hM : 0 ≤ M) (hF : ∀ m, ‖F m - e‖ ≤ M) (D : E) :
    ‖A.update K e F D - e‖ ≤ (K * M * L) * ‖D‖ := by
  have h := norm_bounded_synthesis _ (A.weight_abs_summable K hK D)
    (fun m => F m - e) M hF
  simp only [abs_of_nonneg (A.weight_nonneg K hK D _)] at h
  calc
    _ = ‖∑' m, A.weight K D m • (F m - e)‖ := by simp [update]
    _ ≤ M * A.mass K D := h
    _ ≤ M * (K * L * ‖D‖) := mul_le_mul_of_nonneg_left (A.mass_bound K hK D) hM
    _ = _ := by ring

theorem summable_norm_difference (D D' : E) :
    Summable (fun m => ‖A.coeff D m - A.coeff D' m‖) := by
  exact Summable.of_nonneg_of_le (fun m => norm_nonneg _)
    (fun m => norm_sub_le _ _) ((A.summable_norm D).add (A.summable_norm D'))

theorem weight_difference_bound (K : ℝ) (hK : 0 ≤ K) (D D' : E) (m : ℕ) :
    |A.weight K D m - A.weight K D' m| ≤ K * ‖A.coeff D m - A.coeff D' m‖ := by
  rw [weight, weight, ← mul_sub, abs_mul, abs_of_nonneg hK]
  exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le _ _) hK

theorem weight_difference_summable (K : ℝ) (hK : 0 ≤ K) (D D' : E) :
    Summable (fun m => |A.weight K D m - A.weight K D' m|) :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (A.weight_difference_bound K hK D D') ((A.summable_norm_difference D D').mul_left K)

theorem weight_difference_sum_bound (K : ℝ) (hK : 0 ≤ K) (D D' : E) :
    (∑' m, |A.weight K D m - A.weight K D' m|) ≤ K * L * ‖D - D'‖ := by
  calc
    _ ≤ ∑' m, K * ‖A.coeff D m - A.coeff D' m‖ :=
      (A.weight_difference_summable K hK D D').tsum_le_tsum
        (A.weight_difference_bound K hK D D') ((A.summable_norm_difference D D').mul_left K)
    _ = K * ∑' m, ‖A.coeff D m - A.coeff D' m‖ := tsum_mul_left
    _ ≤ K * (L * ‖D - D'‖) := mul_le_mul_of_nonneg_left (A.difference_bound D D') hK
    _ = _ := by ring

/-- The contraction estimate is derived from the coefficient Lipschitz bound. -/
theorem update_lipschitz_bound [NormedSpace ℝ E] [CompleteSpace E]
    (K : ℝ) (hK : 0 ≤ K) (e : E) (F : ℕ → E)
    (M : ℝ) (hM : 0 ≤ M) (hF : ∀ m, ‖F m - e‖ ≤ M) (D D' : E) :
    ‖A.update K e F D - A.update K e F D'‖ ≤ (K * M * L) * ‖D - D'‖ := by
  have hsum := (A.update_summable K hK e F M hF D).tsum_sub
    (A.update_summable K hK e F M hF D')
  calc
    _ = ‖∑' m, (A.weight K D m - A.weight K D' m) • (F m - e)‖ := by
      simp only [update, add_sub_add_left_eq_sub]
      rw [← hsum]
      simp only [sub_smul]
    _ ≤ M * ∑' m, |A.weight K D m - A.weight K D' m| :=
      norm_bounded_synthesis _ (A.weight_difference_summable K hK D D') _ M hF
    _ ≤ M * (K * L * ‖D - D'‖) :=
      mul_le_mul_of_nonneg_left (A.weight_difference_sum_bound K hK D D') hM
    _ = _ := by ring

/-- Banach yields a unique carrier; smallness yields its radius and positive
remaining mass. The space E may be the closed subspace of symmetric tensors. -/
theorem exists_unique_positive_fixed_point [NormedSpace ℝ E] [CompleteSpace E]
    (K M : ℝ) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hL : 0 ≤ L) (e : E) (he : ‖e‖ ≤ 1) (F : ℕ → E)
    (hF : ∀ m, ‖F m - e‖ ≤ M) (hsmall : K * M * L ≤ 1 / 2)
    (hmass : 2 * K * L < 1) :
    ∃ D : E, A.update K e F D = D ∧ ‖D - e‖ ≤ 2 * (K * M * L) ∧
      A.mass K D < 1 ∧ ∀ D', A.update K e F D' = D' → D' = D := by
  let q : ℝ≥0 := ⟨K * M * L, mul_nonneg (mul_nonneg hK hM) hL⟩
  have hcon : ContractingWith q (A.update K e F) := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul (fun D D' => ?_)⟩
    · change K * M * L < 1
      linarith
    · simpa only [dist_eq_norm] using A.update_lipschitz_bound K hK e F M hM hF D D'
  let D := hcon.fixedPoint (A.update K e F)
  have hfixed : A.update K e F D = D := hcon.fixedPoint_isFixedPt
  have hdist := A.update_distance_bound K hK e F M hM hF D
  rw [hfixed] at hdist
  have hnorm : ‖D‖ ≤ ‖D - e‖ + 1 := by
    calc
      _ ≤ ‖D - e‖ + ‖e‖ := by simpa only [sub_add_cancel] using norm_add_le (D - e) e
      _ ≤ _ := add_le_add_left he _
  have hq0 : 0 ≤ K * M * L := q.property
  have hball : ‖D - e‖ ≤ 2 * (K * M * L) := by
    have h₁ := mul_le_mul_of_nonneg_left hnorm hq0
    have h₂ := mul_le_mul_of_nonneg_right hsmall (norm_nonneg (D - e))
    nlinarith
  have hnorm2 : ‖D‖ ≤ 2 := by linarith
  have htotal : A.mass K D < 1 := by
    have h := (A.mass_bound K hK D).trans
      (mul_le_mul_of_nonneg_left hnorm2 (mul_nonneg hK hL))
    nlinarith
  refine ⟨D, hfixed, hball, htotal, ?_⟩
  intro D' hD'
  exact hcon.fixedPoint_unique hD'

end CarrierCoefficients
end CausalLowerbound.PartB
