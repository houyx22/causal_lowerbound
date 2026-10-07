import CausalLowerbound.PartB.AnnularCutoff
import CausalLowerbound.PartB.TruncatedDistance

/-! One common scale range controls the whole explicit annular support,
including positivity and exact removal of the distance truncation. -/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.PartB.ShellGeometry

variable {d : Type*} [Fintype d]

theorem fine_annular_domain :
    ∃ ε > 0, ∃ c > 0, ∃ C > 0, ε ≤ 1 / 4 ∧
      ∀ τ ∈ Set.Icc 0 ε, ∀ z ∈ (annularSet (d := d)),
        c ≤ chordProfile τ z ∧ chordProfile τ z ≤ C ∧ chordSquare τ z ≠ 0 ∧
        ∀ u, truncatedDistance (fun i => u i + τ * z i) u = τ * chordProfile τ z := by
  obtain ⟨ε0, hε0, c, hc, C, hC, hb⟩ :=
    fine_chord_uniform_bounds (annularSet (d := d)) annularSet_compact annularSet_avoids_zero 0
  let ε := min ε0 (min (1 / 4) (1 / (16 * C)))
  have hε : 0 < ε := lt_min hε0 (lt_min (by norm_num) (by positivity))
  refine ⟨ε, hε, c, hc, C, hC, (min_le_right _ _).trans (min_le_left _ _), ?_⟩
  intro τ hτ z hz
  have hτ0 : τ ∈ Set.Icc 0 ε0 := ⟨hτ.1, hτ.2.trans (min_le_left _ _)⟩
  have hlo := (hb τ hτ0 z hz).1
  have hhi : chordProfile τ z ≤ C := by
    have h := (hb τ hτ0 z hz).2 0 le_rfl
    have hn : |chordProfile τ z| ≤ C := by
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using h
    exact (le_abs_self _).trans hn
  have hD : chordSquare τ z ≠ 0 := by
    intro hzero
    have : chordProfile τ z = 0 := by simp [chordProfile, hzero]
    linarith
  refine ⟨hlo, hhi, hD, ?_⟩
  intro u
  rw [truncatedDistance, chordDistance_scale τ hτ.1]
  apply distanceCap_small
  have hτC : τ ≤ 1 / (16 * C) :=
    hτ.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  calc
    τ * chordProfile τ z ≤ τ * C := mul_le_mul_of_nonneg_left hhi hτ.1
    _ ≤ (1 / (16 * C)) * C := mul_le_mul_of_nonneg_right hτC hC.le
    _ = 1 / 16 := by field_simp; ring

end CausalLowerbound.PartB.ShellGeometry
