import CausalLowerbound.PartB.FineEdgeWiener

/-! Exact cutoff and coefficient identities for both orientations of a
fine graph edge. These include the boundary where the shell cutoff vanishes. -/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.PartB.ShellGeometry

variable {d : Type*} [Fintype d]

theorem centralDifference_embedding_reverse (u v : d → ℝ) :
    embedding (fun i => u i - centralDifference u v i) = embedding v := by
  have he : (fun i => u i - centralDifference u v i) =
      (fun i => v i + (centralShift u v i : ℝ)) := by
    funext i
    dsimp [centralDifference, centralShift]
    ring
  rw [he, embedding_integer_period]

theorem elementaryProfile_reverse_fineLift (m : ℕ) (u v : d → ℝ) (a : Option (d × Bool)) :
    elementaryProfile (fineScale m) u (-fineLift m u v) a =
      fineScale m * elementaryCoefficient v u a := by
  rw [elementaryProfile_exact_coefficient _ (fineScale_pos m).ne']
  simp only [Pi.neg_apply, mul_neg, fineLift_scaled, ← sub_eq_add_neg]
  rw [elementaryCoefficient_embedding_eq _ u v u (centralDifference_embedding_reverse u v) rfl a]

theorem annular_fineCutoff_exact (m : ℕ) (hm : 5 ≤ m) (u v : d → ℝ) :
    annularCutoff (fineLift m u v) * dyadicProfile (chordProfile (fineScale m) (fineLift m u v)) =
      fineCutoff m (truncatedDistance u v) := by
  rw [fineCutoff_profile_exact m hm]
  by_cases h : dyadicProfile (chordProfile (fineScale m) (fineLift m u v)) = 0
  · simp only [h, mul_zero]
  · rw [annularCutoff_on_fine_shell _ _ (fineLift_central m u v) h, one_mul]

theorem fine_distance_exact_on_shell (m : ℕ) (hm : 5 ≤ m) (u v : d → ℝ)
    (h : fineCutoff m (truncatedDistance u v) ≠ 0) :
    truncatedDistance u v = fineScale m * chordProfile (fineScale m) (fineLift m u v) := by
  rw [(fineCutoff_uncapped m hm u v h).2, chordDistance_fineLift]

end CausalLowerbound.PartB.ShellGeometry
