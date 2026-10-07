import CausalLowerbound.PartB.CarrierMoments

/-! Conditional coefficient laws evaluated from a common normed coefficient
space. The normalization uses the coefficient norm before sign evaluation, so
the countable label weights do not depend on the signs. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartC

open PartB

variable {V Z I Γ : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype Γ]

theorem evaluated_normalizedCoefficient_scale (ev : V →ₗ[ℝ] ℝ)
    (K : ℝ) (hK : 0 < K) (a : V) :
    (K * ‖a‖) * ev (normalizedCoefficient K a) = ev a := by
  simpa only [map_smul, smul_eq_mul] using
    congrArg ev (normalizedCoefficient_scale K hK a)

/-- The same coefficient sequence supplies a positive kernel for every sign
configuration. Label zero always uses the baseline law. -/
theorem exists_sign_carrier_kernel (feature : I → Γ → ℝ) (μ : FiniteLaw Γ)
    (radius : ℝ)
    (realize : ∀ v : I → ℝ, (∀ i, |v i| ≤ radius) →
      ∃ ν : FiniteLaw Γ, (∀ x, 0 < ν.weight x) ∧
        ∀ i, ν.expect (feature i) = μ.expect (feature i) + v i)
    (ev : Z → I → V →ₗ[ℝ] ℝ)
    (hev : ∀ ζ i a, |ev ζ i a| ≤ ‖a‖)
    (a : ℕ → V) (K : ℝ) (hK : 0 < K) (hinv : K⁻¹ ≤ radius) :
    ∃ kernel : Z → ℕ → FiniteLaw Γ,
      (∀ ζ, kernel ζ 0 = μ) ∧
      (∀ ζ m x, 0 < (kernel ζ (m + 1)).weight x) ∧
      ∀ ζ m i, (kernel ζ (m + 1)).expect (feature i) =
        μ.expect (feature i) + ev ζ i (normalizedCoefficient K (a m)) := by
  have hex : ∀ ζ m, ∃ ν : FiniteLaw Γ, (∀ x, 0 < ν.weight x) ∧
      ∀ i, ν.expect (feature i) =
        μ.expect (feature i) + ev ζ i (normalizedCoefficient K (a m)) := by
    intro ζ m
    apply realize
    intro i
    exact (hev ζ i _).trans ((normalizedCoefficient_norm_le K hK _).trans hinv)
  choose ν hpos hmom using hex
  exact ⟨fun ζ n => match n with | 0 => μ | m + 1 => ν ζ m,
    fun _ => rfl, hpos, hmom⟩

/-- The master identity holds for actual joint probability laws. In particular,
the common weights are `K * ‖a m‖`, not norms of the evaluated coefficients. -/
theorem sign_carrier_master_moment (feature : I → Γ → ℝ) (μ : FiniteLaw Γ)
    (ev : I → V →ₗ[ℝ] ℝ) (hev : ∀ i a, |ev i a| ≤ ‖a‖)
    (a : ℕ → V) (ha : Summable (fun m => ‖a m‖))
    (K : ℝ) (hK : 0 < K) (H : DiscreteLaw ℕ)
    (hweight : ∀ m, H.weight (m + 1) = K * ‖a m‖)
    (kernel : ℕ → FiniteLaw Γ) (hzero : kernel 0 = μ)
    (hmoment : ∀ m i, (kernel (m + 1)).expect (feature i) =
      μ.expect (feature i) + ev i (normalizedCoefficient K (a m)))
    (g : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (hg : ∀ n, |g n| ≤ C) (i : I) :
    (H.joint kernel).expect (fun z => g z.1 * feature i z.2) -
      (H.joint (fun _ => μ)).expect (fun z => g z.1 * feature i z.2) =
      ∑' m, g (m + 1) * ev i (a m) := by
  classical
  have hfeature : ∀ x, |feature i x| ≤ ∑ y, |feature i y| := fun x =>
    Finset.single_le_sum (f := fun y => |feature i y|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ x)
  rw [H.weighted_moment_difference (fun _ => μ) kernel g (feature i)
    C (∑ y, |feature i y|) hC hg hfeature]
  have hs : Summable (fun m => g (m + 1) * ev i (a m)) := by
    apply Summable.of_norm_bounded (fun m => C * ‖a m‖) (ha.mul_left C)
    intro m
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hg (m + 1)) (hev i _) (abs_nonneg _) hC
  let s : ℕ → ℝ := fun n => H.weight n * (g n *
    ((kernel n).expect (feature i) - μ.expect (feature i)))
  have hz : s 0 = 0 := by simp [s, hzero]
  have htail : ∀ m, s (m + 1) = g (m + 1) * ev i (a m) := by
    intro m
    dsimp [s]
    rw [hweight m, hmoment m i]
    calc
      _ = g (m + 1) * ((K * ‖a m‖) * ev i (normalizedCoefficient K (a m))) := by ring
      _ = _ := by rw [evaluated_normalizedCoefficient_scale _ K hK]
  have hs' : HasSum (fun m => s (m + 1)) (∑' m, g (m + 1) * ev i (a m)) := by
    simpa only [htail] using hs.hasSum
  have h := (hasSum_nat_add_iff (f := s) 1).mp hs'
  simp only [Finset.sum_range_one, hz, add_zero] at h
  exact h.tsum_eq

/-- Banach-valued reconstruction of the same density-weighted moments. -/
theorem sign_carrier_moment_hasSum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (feature : I → Γ → ℝ) (μ : FiniteLaw Γ) (ev : I → V →ₗ[ℝ] ℝ)
    (a : ℕ → V) (K : ℝ) (hK : 0 < K) (H : DiscreteLaw ℕ)
    (hweight : ∀ m, H.weight (m + 1) = K * ‖a m‖)
    (kernel : ℕ → FiniteLaw Γ) (hzero : kernel 0 = μ)
    (hmoment : ∀ m i, (kernel (m + 1)).expect (feature i) =
      μ.expect (feature i) + ev i (normalizedCoefficient K (a m)))
    (e : F) (atom : ℕ → F) (target : I → F)
    (hreconstruct : ∀ i, HasSum (fun m => ev i (a m) • atom m) (target i)) (i : I) :
    HasSum (fun n => (H.weight n *
      ((kernel n).expect (feature i) - μ.expect (feature i))) •
      CarrierCoefficients.labeledAtom e atom n) (target i) := by
  let s : ℕ → F := fun n => (H.weight n *
    ((kernel n).expect (feature i) - μ.expect (feature i))) •
    CarrierCoefficients.labeledAtom e atom n
  have hz : s 0 = 0 := by simp [s, hzero]
  have htail : ∀ m, s (m + 1) = ev i (a m) • atom m := by
    intro m
    change (H.weight (m + 1) *
      ((kernel (m + 1)).expect (feature i) - μ.expect (feature i))) • atom m = _
    rw [hweight m, hmoment m i, add_sub_cancel_left,
      evaluated_normalizedCoefficient_scale _ K hK]
  have hs : HasSum (fun m => s (m + 1)) (target i) := by
    simpa only [htail] using hreconstruct i
  have h := (hasSum_nat_add_iff (f := s) 1).mp hs
  simpa only [Finset.sum_range_one, hz, add_zero] using h

end CausalLowerbound.PartC
