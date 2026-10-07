import CausalLowerbound.PartB.ShellProfiles

/-! Uniform bounds for the concrete fine-shell profiles on an arbitrary fixed
compact annulus and a compact set of base representatives. -/

noncomputable section
set_option autoImplicit false
open scoped ContDiff BigOperators Topology

namespace CausalLowerbound.PartB.ShellGeometry

variable {d : Type*} [Fintype d]

def elementaryProfile (τ : ℝ) (u z : d → ℝ) (a : Option (d × Bool)) : ℝ :=
  match a with
  | none => constantProfile τ u z
  | some b => coefficientProfile τ u z b

theorem contDiffAt_elementaryProfile (τ : ℝ) (u z : d → ℝ) (hD : chordSquare τ z ≠ 0) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ((d → ℝ) × (d → ℝ)) => elementaryProfile p.1 p.2.1 p.2.2)
      (τ, u, z) := by
  apply contDiffAt_pi.mpr
  intro a
  cases a with
  | none => exact contDiffAt_constantProfile τ u z hD
  | some a => exact contDiffAt_coefficientProfile τ u z a hD

theorem small_scale_coordinates (R : ℝ) (hR : 0 < R) (τ : ℝ)
    (hτ : τ ∈ Set.Icc 0 (1 / (2 * R))) (z : d → ℝ) (hz : ‖z‖ ≤ R) (i : d) :
    |τ * z i| < 1 := by
  have hi : |z i| ≤ R := (norm_le_pi_norm z i).trans hz
  rw [abs_mul, abs_of_nonneg hτ.1]
  calc
    τ * |z i| ≤ (1 / (2 * R)) * R :=
      mul_le_mul hτ.2 hi (abs_nonneg _) (by positivity)
    _ = 1 / 2 := by field_simp; ring
    _ < 1 := by norm_num

/-- The actual rescaled Lagrange coefficients have one derivative bound for
all sufficiently small scales, including their smooth value at scale zero. -/
theorem fine_lagrange_uniform_derivatives (Ku Kz : Set (d → ℝ))
    (hKu : IsCompact Ku) (hKz : IsCompact Kz) (hz : (0 : d → ℝ) ∉ Kz) (M : ℕ) :
    ∃ ε > 0, ∃ C > 0, ∀ j ≤ M, ∀ τ ∈ Set.Icc 0 ε, ∀ u ∈ Ku, ∀ z ∈ Kz,
      ‖iteratedFDeriv ℝ j (fun y : (d → ℝ) × (d → ℝ) => elementaryProfile τ y.1 y.2)
          (u, z)‖ ≤ C := by
  obtain ⟨R, hR, hbound⟩ := hKz.isBounded.exists_pos_norm_le
  let ε : ℝ := 1 / (2 * R)
  let K : Set (ℝ × ((d → ℝ) × (d → ℝ))) := Set.Icc 0 ε ×ˢ (Ku ×ˢ Kz)
  have hK : IsCompact K := isCompact_Icc.prod (hKu.prod hKz)
  have hf : ∀ p ∈ K, ContDiffAt ℝ ∞
      (fun y : ℝ × ((d → ℝ) × (d → ℝ)) => elementaryProfile y.1 y.2.1 y.2.2) p := by
    rintro ⟨τ, u, z⟩ hp
    apply contDiffAt_elementaryProfile
    exact (chordSquare_pos τ z (fun h => hz (h ▸ hp.2.2))
      (small_scale_coordinates R hR τ hp.1 z (hbound z hp.2.2))).ne'
  obtain ⟨C, hC, hb⟩ := compact_slice_derivative_bound _ K hK hf M
  refine ⟨ε, by dsimp [ε]; positivity, C, hC, ?_⟩
  intro j hj τ hτ u hu z hz'
  exact hb j hj τ (u, z) ⟨hτ, hu, hz'⟩

/-- The rescaled chordal distance is uniformly positive and smooth on the
fixed annulus. Its lower bound and all derivative bounds are proved together. -/
theorem fine_chord_uniform_bounds (Kz : Set (d → ℝ)) (hKz : IsCompact Kz)
    (hz : (0 : d → ℝ) ∉ Kz) (M : ℕ) :
    ∃ ε > 0, ∃ c > 0, ∃ C > 0, ∀ τ ∈ Set.Icc 0 ε, ∀ z ∈ Kz,
      c ≤ chordProfile τ z ∧
      ∀ j ≤ M, ‖iteratedFDeriv ℝ j (chordProfile τ) z‖ ≤ C := by
  obtain ⟨R, hR, hbound⟩ := hKz.isBounded.exists_pos_norm_le
  let ε : ℝ := 1 / (2 * R)
  let K : Set (ℝ × (d → ℝ)) := Set.Icc 0 ε ×ˢ Kz
  have hK : IsCompact K := isCompact_Icc.prod hKz
  have hpos : ∀ p ∈ K, 0 < chordSquare p.1 p.2 := by
    rintro ⟨τ, z⟩ hp
    exact chordSquare_pos τ z (fun h => hz (h ▸ hp.2))
      (small_scale_coordinates R hR τ hp.1 z (hbound z hp.2))
  have hsmooth : ∀ p ∈ K, ContDiffAt ℝ ∞
      (fun y : ℝ × (d → ℝ) => chordProfile y.1 y.2) p :=
    fun p hp => contDiffAt_chordProfile p.1 p.2 (hpos p hp).ne'
  obtain ⟨c, hc, hlow⟩ := hK.exists_forall_le'
    (fun p hp => (hsmooth p hp).continuousAt.continuousWithinAt)
    (fun p hp => Real.sqrt_pos.mpr (hpos p hp))
  obtain ⟨C, hC, hb⟩ := compact_slice_derivative_bound _ K hK hsmooth M
  refine ⟨ε, by dsimp [ε]; positivity, c, hc, C, hC, ?_⟩
  intro τ hτ z hz'
  exact ⟨hlow (τ, z) ⟨hτ, hz'⟩, fun j hj => hb j hj τ z ⟨hτ, hz'⟩⟩

end CausalLowerbound.PartB.ShellGeometry
