import CausalLowerbound.PartB.FineShellBounds
import CausalLowerbound.PartB.DyadicCutoffs
import CausalLowerbound.MixedPeriodization

/-! Actual localized elementary Lagrange profiles. A smooth compact cutoff
away from the origin removes every apparent singularity, including at zero
scale, and yields a uniform Wiener realization after periodization. -/

noncomputable section
set_option autoImplicit false
open scoped ContDiff Topology BigOperators
open Filter

namespace CausalLowerbound.PartB.ShellGeometry

open Wiener

variable {d : Type*} [Fintype d]

theorem embedding_integer_period (u : d → ℝ) (k : d → ℤ) :
    embedding (fun i => u i + k i) = embedding u := by
  funext a
  have he : 2 * Real.pi * (u a.1 + (k a.1 : ℝ)) =
      2 * Real.pi * u a.1 + (k a.1 : ℝ) * (2 * Real.pi) := by ring
  simp only [embedding, he, Real.sin_add_int_mul_two_pi, Real.cos_add_int_mul_two_pi]

theorem differenceProfile_integer_period (τ : ℝ) (u z : d → ℝ) (k : d → ℤ) :
    differenceProfile τ (fun i => u i + k i) z = differenceProfile τ u z := by
  funext a
  have he : 2 * Real.pi * (u a.1 + (k a.1 : ℝ)) + Real.pi * τ * z a.1 =
      (2 * Real.pi * u a.1 + Real.pi * τ * z a.1) + (k a.1 : ℝ) * (2 * Real.pi) := by ring
  simp only [differenceProfile, he, Real.sin_add_int_mul_two_pi, Real.cos_add_int_mul_two_pi]

theorem elementaryProfile_integer_period (τ : ℝ) (u z : d → ℝ) (k : d → ℤ) :
    elementaryProfile τ (fun i => u i + k i) z = elementaryProfile τ u z := by
  funext a
  cases a <;> simp only [elementaryProfile, constantProfile, coefficientProfile,
    embedding_integer_period, differenceProfile_integer_period]

def localizedProfile (κ : (d → ℝ) → ℝ) (a : Option (d × Bool))
    (τ : ℝ) (u z : d → ℝ) : ℂ :=
  (κ z * dyadicProfile (chordProfile τ z) * elementaryProfile τ u z a : ℝ)

theorem localizedProfile_integer_period (κ : (d → ℝ) → ℝ) (a : Option (d × Bool))
    (τ : ℝ) (u z : d → ℝ) (k : d → ℤ) :
    localizedProfile κ a τ (latticeTranslate (fun _ => 1) k u) z = localizedProfile κ a τ u z := by
  have he : latticeTranslate (fun _ => 1) k u = (fun i => u i + (k i : ℝ)) := by
    funext i
    simp only [latticeTranslate, Nat.cast_one, one_mul]
  rw [he]
  simp only [localizedProfile, elementaryProfile_integer_period]

theorem localizedProfile_joint_smooth (κ : (d → ℝ) → ℝ) (hκ : ContDiff ℝ ∞ κ)
    (a : Option (d × Bool)) (τ : ℝ) (x : d ⊕ d → ℝ)
    (hD : (fun i => x (Sum.inr i)) ∈ tsupport κ → chordSquare τ (fun i => x (Sum.inr i)) ≠ 0) :
    ContDiffAt ℝ ∞ (fun p : ℝ × (d ⊕ d → ℝ) =>
      localizedProfile κ a p.1 (fun i => p.2 (Sum.inl i)) (fun i => p.2 (Sum.inr i))) (τ, x) := by
  let u := fun i => x (Sum.inl i)
  let z := fun i => x (Sum.inr i)
  have hu : ContDiff ℝ ∞ (fun p : ℝ × (d ⊕ d → ℝ) => fun i => p.2 (Sum.inl i)) :=
    contDiff_pi.mpr (fun i => (contDiff_apply ℝ ℝ (Sum.inl i)).comp contDiff_snd)
  have hz : ContDiff ℝ ∞ (fun p : ℝ × (d ⊕ d → ℝ) => fun i => p.2 (Sum.inr i)) :=
    contDiff_pi.mpr (fun i => (contDiff_apply ℝ ℝ (Sum.inr i)).comp contDiff_snd)
  by_cases hmem : z ∈ tsupport κ
  · have hq := (contDiffAt_chordProfile τ z (hD hmem)).comp (τ, x)
      (contDiff_fst.prodMk hz).contDiffAt
    have he := (contDiffAt_elementaryProfile τ u z (hD hmem)).comp (τ, x)
      (contDiff_fst.prodMk (hu.prodMk hz)).contDiffAt
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp (τ, x)
      (((hκ.comp hz).contDiffAt.mul (dyadicProfile_smooth.contDiffAt.comp (τ, x) hq)).mul
        ((contDiff_apply ℝ ℝ a).contDiffAt.comp (τ, x) he))
  · have hzcont : Tendsto (fun p : ℝ × (d ⊕ d → ℝ) => fun i => p.2 (Sum.inr i))
        (𝓝 (τ, x)) (𝓝 z) := hz.continuous.continuousAt
    have hzero := (not_mem_tsupport_iff_eventuallyEq.mp hmem).comp_tendsto hzcont
    have hconst : ContDiffAt ℝ ∞ (fun _ : ℝ × (d ⊕ d → ℝ) => (0 : ℂ)) (τ, x) :=
      contDiffAt_const
    apply hconst.congr_of_eventuallyEq
    filter_upwards [hzero] with p hp
    change κ (fun i => p.2 (Sum.inr i)) = 0 at hp
    simp only [localizedProfile, hp, zero_mul, Complex.ofReal_zero]

/-- The concrete rescaled quotient, multiplied by the actual dyadic shell
cutoff and any fixed annular cutoff, is an actual Wiener function with one
bound for all sufficiently small scales and all positive integer periods. -/
theorem localizedProfile_uniform_wiener (κ : (d → ℝ) → ℝ) (hκ : ContDiff ℝ ∞ κ)
    (hc : HasCompactSupport κ) (h0 : (0 : d → ℝ) ∉ tsupport κ) (a : Option (d × Bool)) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ τ ∈ Set.Icc 0 ε, ∀ N : d → ℕ, (∀ i, N i ≠ 0) →
      ∃ A : Fourier (d ⊕ d),
        (∀ x, toContinuous A x = mixedPeriodizedTorus
          (fun y => localizedProfile κ a τ (fun i => y (Sum.inl i)) (fun i => y (Sum.inr i))) N x) ∧
        ‖A‖ ≤ C := by
  obtain ⟨R, hR, hb⟩ := hc.isBounded.exists_pos_norm_le
  let ε : ℝ := 1 / (2 * R)
  let H : ℝ × (d ⊕ d → ℝ) → ℂ := fun p =>
    localizedProfile κ a p.1 (fun i => p.2 (Sum.inl i)) (fun i => p.2 (Sum.inr i))
  have hs : ∀ τ ∈ Set.Icc 0 ε, ∀ x, H (τ, x) ≠ 0 → (fun i => x (Sum.inr i)) ∈ tsupport κ := by
    intro τ _ x hx
    apply subset_tsupport
    intro hz
    exact hx (by simp only [H, localizedProfile, hz, zero_mul, Complex.ofReal_zero])
  have hf : ∀ τ ∈ Set.Icc 0 ε, ∀ x, ContDiffAt ℝ ∞ H (τ, x) := by
    intro τ hτ x
    apply localizedProfile_joint_smooth κ hκ a τ x
    intro hz
    exact (chordSquare_pos τ _ (fun h => h0 (h ▸ hz))
      (small_scale_coordinates R hR τ hτ _ (hb _ hz))).ne'
  have hp : ∀ τ ∈ Set.Icc 0 ε, ∀ k u z,
      H (τ, Sum.elim (latticeTranslate (fun _ => 1) k u) z) = H (τ, Sum.elim u z) := by
    intro τ _ k u z
    exact localizedProfile_integer_period κ a τ u z k
  obtain ⟨C, hC, hbound⟩ := mixed_family_wiener H (Set.Icc 0 ε) (tsupport κ)
    isCompact_Icc hc hs hf hp
  exact ⟨ε, by dsimp [ε]; positivity, C, hC, hbound⟩

end CausalLowerbound.PartB.ShellGeometry
