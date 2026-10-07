import CausalLowerbound.PartB.GraphShellMultipliers

/-! Lists with exactly one elementary multiplier per edge incident to each
shift site satisfy the exact inverse-order ledger used for J_n. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartB.ShellGeometry

open Wiener ConfigurationShells
variable {V E S d : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype S] [Fintype d]

abbrev IncidentFactorIndex (a b : E → V) (sites : S → V) :=
  (i : S) × {e : E // incident a b (sites i) e}

def incidentFactor (a b : E → V) (sites : S → V)
    (tags : IncidentFactorIndex a b sites → Bool × Option (d × Bool))
    (j : IncidentFactorIndex a b sites) : GraphFactor E d := (j.2.val, tags j)

theorem incident_factor_ledger (a b : E → V) (sites : S → V)
    (tags : IncidentFactorIndex a b sites → Bool × Option (d × Bool)) (m : E → ℕ) :
    (∑ j, m (incidentFactor a b sites tags j).1) = ∑ i, vertexOrder a b m (sites i) := by
  simp only [incidentFactor, Fintype.sum_sigma, vertexOrder]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter (incident a b (sites i))) (by simp) m).symm

theorem nonzero_graph_shell_inverse (m0 : ℕ) (a b : E → V) (t : ℝ) (ht : 0 < t)
    (s : E → Option ℕ) (u : V × d → ℝ)
    (h : graphTaper a b taperCutoff t (graphDistance a b u) *
      (∏ e, shellCutoff m0 (s e) (graphDistance a b u e)) ≠ 0) (i : V) :
    (2 : ℝ) ^ vertexOrder a b (fun e => shellLevel m0 (s e)) i ≤ (2 : ℝ) ^ Fintype.card E / t := by
  have htaper := taper_nonzero_vertexProduct a b taperCutoff (fun _ _ h => taperCutoff_zero h)
    t ht (graphDistance a b u) (fun e => (truncatedDistance_range _ _).1) (mul_ne_zero_iff.mp h).1 i
  have hs := vertexProduct_shell_bound a b (graphDistance a b u)
    (fun e => (truncatedDistance_range _ _).1) (fun e => shellLevel m0 (s e)) 2 (by norm_num)
    (fun e => shellCutoff_upper m0 (s e) _ (truncatedDistance_range _ _).2
      ((Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp h).2) e (Finset.mem_univ e))) i
  have hh := (lt_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ vertexOrder a b (fun e => shellLevel m0 (s e)) i)).mp
    (htaper.trans_le hs)
  apply (le_div_iff₀ ht).mpr
  simpa only [mul_comm] using hh.le

end CausalLowerbound.PartB.ShellGeometry
