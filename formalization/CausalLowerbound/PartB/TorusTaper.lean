import CausalLowerbound.PartB.CompleteGraph
import CausalLowerbound.PartB.PhysicalDesign

/-! Descent of the actual complete-graph taper to the compact torus.
The real-lift formula is independent of the selected representatives. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace CausalLowerbound.PartB.ShellGeometry
open Wiener ConfigurationShells
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d]

def completeTaper (Q : ℕ) (ε : ℝ) (u : Fin Q × d → ℝ) : ℝ :=
  graphTaper edgeLeft edgeRight taperCutoff ε (graphDistance edgeLeft edgeRight u)

theorem completeTaper_continuous (Q : ℕ) (ε : ℝ) : Continuous (completeTaper (d := d) Q ε) := by
  unfold completeTaper graphTaper
  apply continuous_finset_prod
  intro i _
  apply taperCutoff_smooth.continuous.comp
  apply Continuous.div_const
  unfold vertexProduct
  apply continuous_finset_prod
  intro e _
  split_ifs
  · have hm : Continuous (fun u : Fin Q × d → ℝ =>
        (configurationSite u (edgeLeft e), configurationSite u (edgeRight e))) := by
      exact (continuous_pi (fun a => continuous_apply (edgeLeft e, a))).prodMk
        (continuous_pi (fun a => continuous_apply (edgeRight e, a)))
    have hh := (truncatedDistance_continuous (d := d)).comp hm
    exact hh
  · exact continuous_const

theorem completeTaper_integer_period (Q : ℕ) (ε : ℝ) (u : Fin Q × d → ℝ) (k : Fin Q × d → ℤ) :
    completeTaper Q ε (fun a => u a + k a) = completeTaper Q ε u := by
  have he : graphDistance edgeLeft edgeRight (fun a => u a + k a) =
      graphDistance edgeLeft edgeRight u := by
    funext e
    have hh := truncatedDistance_integer_period (configurationSite u (edgeLeft e))
      (configurationSite u (edgeRight e)) (fun a => k (edgeLeft e, a)) (fun a => k (edgeRight e, a))
    exact hh
  simp only [completeTaper, he]

def flatTorusTaper (Q : ℕ) (ε : ℝ) (u : Torus (Fin Q × d)) : ℝ :=
  completeTaper Q ε (torusRepresentative u)

theorem flatTorusTaper_lift (Q : ℕ) (ε : ℝ) (u : Fin Q × d → ℝ) :
    flatTorusTaper Q ε (torusProjection u) = completeTaper Q ε u := by
  obtain ⟨k, hk⟩ := torusProjection_eq_integer_shift (torusRepresentative (torusProjection u)) u
    (torusProjection_representative _)
  unfold flatTorusTaper
  rw [hk, completeTaper_integer_period]

theorem flatTorusTaper_continuous (Q : ℕ) (ε : ℝ) : Continuous (flatTorusTaper (d := d) Q ε) := by
  apply torusProjection_quotient.continuous_comp_iff.mp
  have he : flatTorusTaper (d := d) Q ε ∘ torusProjection = completeTaper Q ε :=
    funext (flatTorusTaper_lift Q ε)
  rw [he]
  exact completeTaper_continuous Q ε

def torusTaper (Q : ℕ) (ε : ℝ) (u : Fin Q → Torus d) : ℝ :=
  flatTorusTaper Q ε (fun a => u a.1 a.2)

theorem torusTaper_lift (Q : ℕ) (ε : ℝ) (u : Fin Q × d → ℝ) :
    torusTaper Q ε (fun i => torusProjection (configurationSite u i)) = completeTaper Q ε u :=
  flatTorusTaper_lift Q ε u

theorem torusTaper_continuous (Q : ℕ) (ε : ℝ) : Continuous (torusTaper (d := d) Q ε) := by
  have hm : Continuous (fun u : Fin Q → Torus d => fun a : Fin Q × d => u a.1 a.2) :=
    continuous_pi (fun a => (continuous_apply a.2).comp (continuous_apply a.1))
  exact (flatTorusTaper_continuous Q ε).comp hm

theorem torusTaper_bounds (Q : ℕ) (ε : ℝ) (u : Fin Q → Torus d) :
    0 ≤ torusTaper Q ε u ∧ torusTaper Q ε u ≤ 1 := by
  unfold torusTaper flatTorusTaper completeTaper graphTaper taperCutoff
  constructor
  · exact Finset.prod_nonneg (fun _ _ => Real.smoothTransition.nonneg _)
  · apply Finset.prod_le_one
    · intro _ _; exact Real.smoothTransition.nonneg _
    · intro _ _; exact Real.smoothTransition.le_one _

end CausalLowerbound.PartB.ShellGeometry
