import CausalLowerbound.SmoothCompact
import CausalLowerbound.WienerDerivativeDecay

/-! Uniform sampled Wiener bounds for actual smooth compact families. No
separate derivative bound is an input: it follows from joint smoothness and
compactness, including parameters at the boundary of their compact set. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff Topology

namespace CausalLowerbound.Wiener

variable {P α : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [Fintype α]

theorem compact_smooth_family_wiener_bound
    (f : P × EuclideanSpace ℝ α → ℂ) (Kp : Set P) (Kx : Set (EuclideanSpace ℝ α))
    (hKp : IsCompact Kp) (hKx : IsCompact Kx)
    (hsupport : ∀ p ∈ Kp, tsupport (fun x => f (p, x)) ⊆ Kx)
    (hf : ∀ p ∈ Kp, ∀ x ∈ Kx, ContDiffAt ℝ ∞ f (p, x)) :
    ∃ C ≥ 0, ∀ p ∈ Kp, ∀ N : α → ℕ, (∀ i, N i ≠ 0) →
      Summable (fun k => ‖sampledFourier (fun x => f (p, x)) N k‖) ∧
      (∑' k, ‖sampledFourier (fun x => f (p, x)) N k‖) ≤ C := by
  obtain ⟨B, hB, hb⟩ := compact_slice_derivative_bound f (Kp ×ˢ Kx) (hKp.prod hKx)
    (fun y hy => hf y.1 hy.1 y.2 hy.2) (2 * Fintype.card α)
  let C := ((2 : ℝ) ^ Fintype.card α * (2 : ℝ) ^ (2 * Fintype.card α)) *
    (((2 * Fintype.card α : ℕ) + 1 : ℝ) * B * volume.real Kx) *
    latticeConstant ^ Fintype.card α
  refine ⟨C, mul_nonneg (by dsimp; positivity) (pow_nonneg latticeConstant_nonneg _), ?_⟩
  intro p hp N hN
  have hsmooth : ContDiff ℝ ∞ (fun x => f (p, x)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ Kx
    · exact (hf p hp x hx).comp x (contDiffAt_const.prodMk contDiffAt_id)
    · have hx' : x ∉ tsupport (fun x => f (p, x)) := fun h => hx (hsupport p hp h)
      apply contDiffAt_const.congr_of_eventuallyEq
      exact not_mem_tsupport_iff_eventuallyEq.mp hx'
  apply compact_profile_wiener_bound _ (hsmooth.of_le (WithTop.coe_le_coe.mpr le_top))
    Kx hKx (hsupport p hp) B _ N hN
  intro j hj x
  by_cases hx : x ∈ Kx
  · exact hb j hj p x ⟨hp, hx⟩
  · have hz : iteratedFDeriv ℝ j (fun x => f (p, x)) x = 0 := by
      by_contra hn
      exact hx (hsupport p hp (support_iteratedFDeriv_subset j hn))
    rw [hz, norm_zero]
    exact hB.le

end CausalLowerbound.Wiener
