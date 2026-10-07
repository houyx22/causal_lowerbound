import CausalLowerbound.PartB.IncidentFactorLedger
import CausalLowerbound.PartB.FiniteShellPartition

/-! Sum the actual graph shells. A product with one multiplier on every
incident edge per shift site loses exactly one inverse taper scale per site. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartB.ShellGeometry

open Wiener ConfigurationShells
variable {V E S d : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype S] [Fintype d]

def taperedIncidentProduct (a b : E → V) (sites : S → V)
    (tags : IncidentFactorIndex a b sites → Bool × Option (d × Bool)) (t : ℝ) (u : V × d → ℝ) : ℝ :=
  graphTaper a b taperCutoff t (graphDistance a b u) *
    ∏ j, graphFactor a b (incidentFactor a b sites tags j) u

theorem incident_shell_uniform_wiener (a b : E → V) (sites : S → V)
    (tags : IncidentFactorIndex a b sites → Bool × Option (d × Bool)) :
    ∃ m0 : ℕ, ∃ B ≥ 0, ∀ t > 0, ∀ s : E → Option ℕ, ∃ A : Fourier (V × d),
      (∀ u, toContinuous A (torusProjection u) =
        (graphShellMultiplier m0 a b (incidentFactor a b sites tags) t s u : ℝ)) ∧
      ‖A‖ ≤ B * ((2 : ℝ) ^ Fintype.card E / t) ^ Fintype.card S := by
  classical
  obtain ⟨m0, hm0, hbound⟩ := graph_shell_uniform_wiener a b (incidentFactor a b sites tags)
  obtain ⟨B, hB, hb⟩ := hbound m0 le_rfl
  refine ⟨m0, B, hB, ?_⟩
  intro t ht s
  by_cases hz : ∀ u, graphShellMultiplier m0 a b (incidentFactor a b sites tags) t s u = 0
  · refine ⟨0, ?_, ?_⟩
    · intro u
      rw [hz u, map_zero]
      rfl
    · rw [norm_zero]
      positivity
  · push_neg at hz
    obtain ⟨u, hu⟩ := hz
    have htp : graphTaper a b taperCutoff t (graphDistance a b u) *
        (∏ e, shellCutoff m0 (s e) (graphDistance a b u e)) ≠ 0 :=
      (mul_ne_zero_iff.mp hu).1
    have hvertex := nonzero_graph_shell_inverse m0 a b t ht s u htp
    have horder := dyadic_ledger_bound a b sites (fun e => shellLevel m0 (s e))
      ((2 : ℝ) ^ Fintype.card E / t) (fun i => hvertex (sites i))
    rw [inverse_order_ledger] at horder
    obtain ⟨A, hA, hn⟩ := hb t ht s
    refine ⟨A, hA, ?_⟩
    rw [incident_factor_ledger a b sites tags (fun e => shellLevel m0 (s e))] at hn
    exact hn.trans (mul_le_mul_of_nonneg_left horder hB)

/-- A concrete Wiener realization of the full tapered product, including the
finite sum over every graph shell. This is the analytic estimate needed for
each term in the expansion of the ideal moment increment. -/
theorem tapered_incident_product_wiener (a b : E → V) (sites : S → V)
    (tags : IncidentFactorIndex a b sites → Bool × Option (d × Bool)) :
    ∃ B ≥ 0, ∀ t > 0, ∃ A : Fourier (V × d),
      (∀ u, toContinuous A (torusProjection u) = (taperedIncidentProduct a b sites tags t u : ℝ)) ∧
      ‖A‖ ≤ B * ((levelBudget 2 t + 1 : ℕ) : ℝ) ^ Fintype.card E *
        ((2 : ℝ) ^ Fintype.card E / t) ^ Fintype.card S := by
  classical
  obtain ⟨m0, B, hB, hb⟩ := incident_shell_uniform_wiener a b sites tags
  refine ⟨B, hB, ?_⟩
  intro t ht
  let L := levelBudget 2 t
  let label (s : E → Option (Fin L)) : E → Option ℕ := fun e => (s e).map Fin.val
  choose A hA hn using fun s : E → Option (Fin L) => hb t ht (label s)
  refine ⟨∑ s, A s, ?_, ?_⟩
  · intro u
    simp only [map_sum, ContinuousMap.sum_apply, hA]
    rw [← Complex.ofReal_sum]
    congr 1
    have hp := finite_tapered_shell_partition m0 a b t ht (graphDistance a b u)
      (fun _ => truncatedDistance_range _ _)
    unfold graphShellMultiplier
    rw [← Finset.sum_mul]
    change (∑ s : E → Option (Fin L), graphTaper a b taperCutoff t (graphDistance a b u) *
      ∏ e, finiteShellCutoff m0 L (s e) (graphDistance a b u e)) * _ = _
    rw [← hp]
    rfl
  · calc
      ‖∑ s, A s‖ ≤ ∑ s, ‖A s‖ := norm_sum_le _ _
      _ ≤ ∑ _s : E → Option (Fin L), B * ((2 : ℝ) ^ Fintype.card E / t) ^ Fintype.card S :=
        Finset.sum_le_sum (fun s _ => hn s)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun,
          Fintype.card_option, Fintype.card_fin, Nat.cast_pow]
        ring

end CausalLowerbound.PartB.ShellGeometry
