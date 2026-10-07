import CausalLowerbound.WienerLattice
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Derivatives imply uniformly summable sampled Fourier transforms

This is the analytic decay step for compact Euclidean profiles. The remaining
application must identify the periodized shell coefficients with these samples
and establish uniform derivative integrals for the paper's actual profiles.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators FourierTransform ContDiff
attribute [local instance 101] secondCountableTopologyEither_of_left

namespace CausalLowerbound.Wiener

variable {α : Type*} [Fintype α]

def derivativeMass (f : EuclideanSpace ℝ α → ℂ) (M : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (M + 1), ∫ x, ‖iteratedFDeriv ℝ j f x‖

theorem derivativeMass_nonneg (f : EuclideanSpace ℝ α → ℂ) (M : ℕ) :
    0 ≤ derivativeMass f M :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => norm_nonneg _))

theorem derivativeMass_mono (f : EuclideanSpace ℝ α → ℂ) {m M : ℕ} (hm : m ≤ M) :
    derivativeMass f m ≤ derivativeMass f M :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ hm))
    (fun _ _ _ => integral_nonneg (fun _ => norm_nonneg _))

/-- Integration by parts, through the actual Fourier transform derivative
theorem, controls every required power of the frequency. -/
theorem fourier_power_bound (f : EuclideanSpace ℝ α → ℂ) (M : ℕ)
    (hf : ContDiff ℝ (M : ℕ∞) f)
    (hder : ∀ j ≤ M, Integrable (fun x => ‖iteratedFDeriv ℝ j f x‖))
    (n : ℕ) (hn : n ≤ M) (w : EuclideanSpace ℝ α) :
    ‖w‖ ^ n * ‖𝓕 f w‖ ≤ (2 : ℝ) ^ n * derivativeMass f M := by
  have hI : ∀ k j : ℕ, (k : ℕ∞) ≤ 0 → (j : ℕ∞) ≤ (M : ℕ∞) →
      Integrable (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ j f x‖) := by
    intro k j hk hj
    have hk' : k ≤ 0 := by exact_mod_cast hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk'
    subst k
    simpa using hder j (by exact_mod_cast hj)
  have h := Real.pow_mul_norm_iteratedFDeriv_fourierIntegral_le
    (K := 0) (N := (M : ℕ∞)) hf hI (k := 0) (n := n) (by simp) (by exact_mod_cast hn) w
  have h' : ‖w‖ ^ n * ‖𝓕 f w‖ ≤ (2 : ℝ) ^ n * derivativeMass f n := by
    simpa [derivativeMass, Finset.sum_product, norm_iteratedFDeriv_zero] using h
  exact h'.trans (mul_le_mul_of_nonneg_left (derivativeMass_mono f hn) (by positivity))

def derivativeDecayConstant (f : EuclideanSpace ℝ α → ℂ) (p : ℕ) : ℝ :=
  (2 : ℝ) ^ p * (2 : ℝ) ^ (2 * p) * derivativeMass f (2 * p)

theorem derivativeDecayConstant_nonneg (f : EuclideanSpace ℝ α → ℂ) (p : ℕ) :
    0 ≤ derivativeDecayConstant f p :=
  mul_nonneg (by positivity) (derivativeMass_nonneg f _)

theorem fourier_radial_weight_bound (f : EuclideanSpace ℝ α → ℂ) (p : ℕ)
    (hf : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) f)
    (hder : ∀ j ≤ 2 * p, Integrable (fun x => ‖iteratedFDeriv ℝ j f x‖))
    (w : EuclideanSpace ℝ α) :
    (1 + ‖w‖ ^ 2) ^ p * ‖𝓕 f w‖ ≤ derivativeDecayConstant f p := by
  have h0 : ‖𝓕 f w‖ ≤ derivativeMass f (2 * p) := by
    simpa using fourier_power_bound f (2 * p) hf hder 0 (Nat.zero_le _) w
  have hpow := fourier_power_bound f (2 * p) hf hder (2 * p) le_rfl w
  have hD := derivativeMass_nonneg f (2 * p)
  by_cases hw : ‖w‖ ≤ 1
  · have hw2 : ‖w‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w]
    have hbase : (1 + ‖w‖ ^ 2) ^ p ≤ (2 : ℝ) ^ p :=
      pow_le_pow_left₀ (by positivity) (by linarith) p
    calc
      _ ≤ (2 : ℝ) ^ p * derivativeMass f (2 * p) :=
        mul_le_mul hbase h0 (norm_nonneg _) (by positivity)
      _ ≤ (2 : ℝ) ^ p * ((2 : ℝ) ^ (2 * p) * derivativeMass f (2 * p)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact le_mul_of_one_le_left hD (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      _ = _ := by rw [derivativeDecayConstant, mul_assoc]
  · have hw2 : 1 ≤ ‖w‖ ^ 2 := by nlinarith [lt_of_not_ge hw]
    have hbase : (1 + ‖w‖ ^ 2) ^ p ≤ (2 : ℝ) ^ p * ‖w‖ ^ (2 * p) := by
      calc
        _ ≤ (2 * ‖w‖ ^ 2) ^ p := pow_le_pow_left₀ (by positivity) (by linarith) p
        _ = _ := by rw [mul_pow, ← pow_mul]
    calc
      _ ≤ ((2 : ℝ) ^ p * ‖w‖ ^ (2 * p)) * ‖𝓕 f w‖ :=
        mul_le_mul_of_nonneg_right hbase (norm_nonneg _)
      _ = (2 : ℝ) ^ p * (‖w‖ ^ (2 * p) * ‖𝓕 f w‖) := mul_assoc _ _ _
      _ ≤ (2 : ℝ) ^ p * ((2 : ℝ) ^ (2 * p) * derivativeMass f (2 * p)) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by rw [derivativeDecayConstant, mul_assoc]

/-- Product decay follows from sufficiently many genuine Fréchet derivatives.
The order used is twice the total dimension; the shell profiles are smooth. -/
theorem fourier_product_decay (f : EuclideanSpace ℝ α → ℂ)
    (hf : ContDiff ℝ ((2 * Fintype.card α : ℕ) : ℕ∞) f)
    (hder : ∀ j ≤ 2 * Fintype.card α, Integrable (fun x => ‖iteratedFDeriv ℝ j f x‖))
    (w : EuclideanSpace ℝ α) :
    ‖𝓕 f w‖ ≤ derivativeDecayConstant f (Fintype.card α) * ∏ i, decayKernel (w i) := by
  have hd : 0 < ∏ i, (1 + (w i) ^ 2) := Finset.prod_pos (fun _ _ => by positivity)
  have hp : (∏ i, (1 + (w i) ^ 2)) ≤ (1 + ‖w‖ ^ 2) ^ Fintype.card α := by
    calc
      _ ≤ ∏ _i : α, (1 + ‖w‖ ^ 2) := by
        apply Finset.prod_le_prod (fun _ _ => by positivity)
        intro i _
        have hc := PiLp.norm_apply_le w i
        rw [Real.norm_eq_abs] at hc
        nlinarith [sq_abs (w i), abs_nonneg (w i), norm_nonneg w]
      _ = _ := by simp
  have hb := (mul_le_mul_of_nonneg_right hp (norm_nonneg (𝓕 f w))).trans
    (fourier_radial_weight_bound f (Fintype.card α) hf hder w)
  simp only [decayKernel, Finset.prod_div_distrib, Finset.prod_const_one, mul_one_div]
  exact (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using hb)

def gridPoint (N : α → ℕ) (k : α → ℤ) : EuclideanSpace ℝ α :=
  fun i => (k i : ℝ) / N i

def sampledFourier (f : EuclideanSpace ℝ α → ℂ) (N : α → ℕ) (k : α → ℤ) : ℂ :=
  (∏ i, (N i : ℝ)⁻¹) • 𝓕 f (gridPoint N k)

theorem sampledFourier_decay (f : EuclideanSpace ℝ α → ℂ)
    (hf : ContDiff ℝ ((2 * Fintype.card α : ℕ) : ℕ∞) f)
    (hder : ∀ j ≤ 2 * Fintype.card α, Integrable (fun x => ‖iteratedFDeriv ℝ j f x‖))
    (N : α → ℕ) (k : α → ℤ) :
    ‖sampledFourier f N k‖ ≤ derivativeDecayConstant f (Fintype.card α) * anisotropicKernel N k := by
  have hvol : 0 ≤ ∏ i, (N i : ℝ)⁻¹ := Finset.prod_nonneg (fun _ _ => by positivity)
  rw [sampledFourier, norm_smul, Real.norm_eq_abs, abs_of_nonneg hvol]
  have h := mul_le_mul_of_nonneg_left (fourier_product_decay f hf hder (gridPoint N k)) hvol
  simpa only [anisotropicKernel, normalizedKernel, Finset.prod_mul_distrib,
    gridPoint, mul_left_comm] using h

/-- A uniform sampled Fourier ℓ¹ estimate derived from actual derivative
integrals, valid for independently chosen positive integer periods. -/
theorem sampledFourier_wiener_bound (f : EuclideanSpace ℝ α → ℂ)
    (hf : ContDiff ℝ ((2 * Fintype.card α : ℕ) : ℕ∞) f)
    (hder : ∀ j ≤ 2 * Fintype.card α, Integrable (fun x => ‖iteratedFDeriv ℝ j f x‖))
    (N : α → ℕ) (hN : ∀ i, N i ≠ 0) :
    Summable (fun k => ‖sampledFourier f N k‖) ∧
      (∑' k, ‖sampledFourier f N k‖) ≤
        derivativeDecayConstant f (Fintype.card α) * latticeConstant ^ Fintype.card α :=
  ⟨anisotropic_fourier_summable N hN _ _ (sampledFourier_decay f hf hder N),
    anisotropic_fourier_bound N hN _ (derivativeDecayConstant_nonneg f _) _
      (sampledFourier_decay f hf hder N)⟩

theorem compact_derivatives_integrable (f : EuclideanSpace ℝ α → ℂ) (M : ℕ)
    (hf : ContDiff ℝ (M : ℕ∞) f) (hcompact : HasCompactSupport f) :
    ∀ j ≤ M, Integrable (fun x => ‖iteratedFDeriv ℝ j f x‖) := by
  intro j hj
  exact (hf.continuous_iteratedFDeriv (by exact_mod_cast hj)).norm.integrable_of_hasCompactSupport
    (hcompact.iteratedFDeriv j).norm

theorem compact_derivativeMass_bound (f : EuclideanSpace ℝ α → ℂ) (M : ℕ)
    (K : Set (EuclideanSpace ℝ α)) (hK : IsCompact K) (hsupport : tsupport f ⊆ K)
    (C : ℝ) (hC : ∀ j ≤ M, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ C) :
    derivativeMass f M ≤ (M + 1 : ℝ) * C * volume.real K := by
  have hj (j : ℕ) (hj : j ≤ M) :
      (∫ x, ‖iteratedFDeriv ℝ j f x‖) ≤ C * volume.real K := by
    have hz (x : EuclideanSpace ℝ α) (hx : x ∉ K) : iteratedFDeriv ℝ j f x = 0 := by
      by_contra hn
      exact hx (hsupport (support_iteratedFDeriv_subset j hn))
    have he : (∫ x in K, ‖iteratedFDeriv ℝ j f x‖) = ∫ x, ‖iteratedFDeriv ℝ j f x‖ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hz x hx, norm_zero])
    have hb := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (f := fun x => ‖iteratedFDeriv ℝ j f x‖) hK.measure_lt_top
      (fun x (_hx : x ∈ K) => (by simpa only [norm_norm] using hC j hj x))
    rw [he, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))] at hb
    exact hb
  calc
    _ ≤ ∑ _j ∈ Finset.range (M + 1), C * volume.real K :=
      Finset.sum_le_sum (fun j h => hj j (Nat.le_of_lt_succ (Finset.mem_range.mp h)))
    _ = _ := by simp [mul_assoc]

/-- Uniform compact support and uniform derivative bounds imply a sampled
Wiener estimate with no period-dependent constant. -/
theorem compact_profile_wiener_bound (f : EuclideanSpace ℝ α → ℂ)
    (hf : ContDiff ℝ ((2 * Fintype.card α : ℕ) : ℕ∞) f)
    (K : Set (EuclideanSpace ℝ α)) (hK : IsCompact K) (hsupport : tsupport f ⊆ K)
    (C : ℝ) (hC : ∀ j ≤ 2 * Fintype.card α, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ C)
    (N : α → ℕ) (hN : ∀ i, N i ≠ 0) :
    Summable (fun k => ‖sampledFourier f N k‖) ∧
      (∑' k, ‖sampledFourier f N k‖) ≤
        ((2 : ℝ) ^ Fintype.card α * (2 : ℝ) ^ (2 * Fintype.card α)) *
          (((2 * Fintype.card α : ℕ) + 1 : ℝ) * C * volume.real K) *
          latticeConstant ^ Fintype.card α := by
  have hcompact : HasCompactSupport f := hK.of_isClosed_subset isClosed_closure hsupport
  have hder := compact_derivatives_integrable f _ hf hcompact
  have h := sampledFourier_wiener_bound f hf hder N hN
  refine ⟨h.1, h.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg latticeConstant_nonneg _)
  exact mul_le_mul_of_nonneg_left
    (compact_derivativeMass_bound f _ K hK hsupport C hC) (by positivity)

end CausalLowerbound.Wiener
