import CausalLowerbound.PartB.IdealIncrementWiener

/-! The concrete increment is exactly the zero extension at collisions. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartB.ShellGeometry
open Wiener ConfigurationShells

variable {Ω K V E d : Type*} [Fintype Ω] [Fintype K] [DecidableEq K]
  [Fintype V] [DecidableEq V] [Fintype E] [Fintype d] [DecidableEq d]

theorem graphTaper_zero_of_zero_edge (a b : E → V) (t : ℝ) (r : E → ℝ) (e : E) (he : r e = 0) :
    graphTaper a b taperCutoff t r = 0 := by
  have hv : vertexProduct a b r (a e) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ e)
    simp [incident, he]
  apply Finset.prod_eq_zero (Finset.mem_univ (a e))
  rw [hv, zero_div]
  exact taperCutoff_zero zero_le_one

theorem idealIncrement_zero_of_zero_edge (a b : E → V) (μ : FiniteLaw Ω) (U : Ω → K → ℝ)
    (ν : K → d × Bool →₀ ℕ) (amp t : ℝ) (u : V × d → ℝ)
    (e : E) (he : graphDistance a b u e = 0) : idealIncrement a b μ U ν amp t u = 0 := by
  rw [idealIncrement, graphTaper_zero_of_zero_edge a b t _ e he, zero_mul]

theorem truncatedDistance_self (u : d → ℝ) : truncatedDistance u u = 0 := by
  simp only [truncatedDistance, chordDistance, sub_self, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, Real.sqrt_zero]
  exact distanceCap_small (by norm_num)

theorem idealIncrement_zero_of_collision (a b : E → V) (μ : FiniteLaw Ω) (U : Ω → K → ℝ)
    (ν : K → d × Bool →₀ ℕ) (amp t : ℝ) (u : V × d → ℝ)
    (e : E) (he : configurationSite u (a e) = configurationSite u (b e)) :
    idealIncrement a b μ U ν amp t u = 0 := by
  apply idealIncrement_zero_of_zero_edge a b μ U ν amp t u e
  unfold graphDistance
  rw [he, truncatedDistance_self]

end CausalLowerbound.PartB.ShellGeometry
