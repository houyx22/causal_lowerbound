import CausalLowerbound.PartB.ConfigurationShells
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-! The nonzero support of the actual product taper imposes the vertex budgets
used by the shell count and inverse-order ledger. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartB.ConfigurationShells

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]

def vertexProduct (a b : E → V) (r : E → ℝ) (i : V) : ℝ :=
  ∏ e, if incident a b i e then r e else 1

def graphTaper (a b : E → V) (θ : ℝ → ℝ) (t : ℝ) (r : E → ℝ) : ℝ :=
  ∏ i, θ (vertexProduct a b r i / t)

def shellWeight (ρ : E → ℝ → ℝ) (r : E → ℝ) : ℝ := ∏ e, ρ e (r e)

theorem vertexProduct_nonneg (a b : E → V) (r : E → ℝ) (hr : ∀ e, 0 ≤ r e) (i : V) :
    0 ≤ vertexProduct a b r i := by
  apply Finset.prod_nonneg
  intro e _
  split_ifs
  · exact hr e
  · exact zero_le_one

theorem taper_nonzero_vertexProduct (a b : E → V) (θ : ℝ → ℝ)
    (hθ : ∀ x, 0 ≤ x → x ≤ 1 → θ x = 0) (t : ℝ) (ht : 0 < t)
    (r : E → ℝ) (hr : ∀ e, 0 ≤ r e) (h : graphTaper a b θ t r ≠ 0) (i : V) :
    t < vertexProduct a b r i := by
  have hi : θ (vertexProduct a b r i / t) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp h) i (Finset.mem_univ i)
  by_contra hle
  apply hi
  exact hθ _ (div_nonneg (vertexProduct_nonneg a b r hr i) ht.le)
    ((div_le_one ht).mpr (le_of_not_gt hle))

theorem vertexProduct_shell_bound (a b : E → V) (r : E → ℝ) (hr : ∀ e, 0 ≤ r e)
    (m : E → ℕ) (C : ℝ) (hC : 1 ≤ C) (hshell : ∀ e, r e ≤ C / (2 : ℝ) ^ m e) (i : V) :
    vertexProduct a b r i ≤ C ^ Fintype.card E / (2 : ℝ) ^ vertexOrder a b m i := by
  calc
    _ ≤ ∏ e, C / (2 : ℝ) ^ (if incident a b i e then m e else 0) := by
      apply Finset.prod_le_prod
      · intro e _; split_ifs
        · exact hr e
        · exact zero_le_one
      · intro e _; split_ifs with h
        · exact hshell e
        · simpa using hC
    _ = _ := by
      rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
      simp only [Finset.prod_const, Finset.card_univ, vertexOrder]

/-- The support implication is proved from the cutoff values and elementary
shell support bounds, rather than inserted as an admissibility hypothesis. -/
theorem taper_shell_inverse_bound (a b : E → V) (θ : ℝ → ℝ)
    (hθ : ∀ x, 0 ≤ x → x ≤ 1 → θ x = 0) (t : ℝ) (ht : 0 < t)
    (ρ : E → ℝ → ℝ) (m : E → ℕ) (C : ℝ) (hC : 1 ≤ C)
    (hshell : ∀ e r, ρ e r ≠ 0 → r ≤ C / (2 : ℝ) ^ m e)
    (r : E → ℝ) (hr : ∀ e, 0 ≤ r e)
    (h : graphTaper a b θ t r * shellWeight ρ r ≠ 0) (i : V) :
    (2 : ℝ) ^ vertexOrder a b m i < C ^ Fintype.card E / t := by
  have htaper := taper_nonzero_vertexProduct a b θ hθ t ht r hr (mul_ne_zero_iff.mp h).1 i
  have hρ := (mul_ne_zero_iff.mp h).2
  have hs := vertexProduct_shell_bound a b r hr m C hC
    (fun e => hshell e (r e) ((Finset.prod_ne_zero_iff.mp hρ) e (Finset.mem_univ e))) i
  have hh : t * (2 : ℝ) ^ vertexOrder a b m i < C ^ Fintype.card E :=
    (lt_div_iff₀ (by positivity)).mp (htaper.trans_le hs)
  exact (lt_div_iff₀ ht).mpr (by simpa only [mul_comm] using hh)

def levelBudget (A t : ℝ) : ℕ := ⌈Real.log (A / t) / Real.log 2⌉₊

theorem level_le_budget {m : ℕ} {A t : ℝ} (h : (2 : ℝ) ^ m ≤ A / t) :
    m ≤ levelBudget A t := by
  have hlog := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ m) h
  rw [Real.log_pow] at hlog
  have hm : (m : ℝ) ≤ Real.log (A / t) / Real.log 2 :=
    (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hlog
  exact_mod_cast hm.trans (Nat.le_ceil _)

theorem taper_shell_admissible (a b : E → V) (θ : ℝ → ℝ)
    (hθ : ∀ x, 0 ≤ x → x ≤ 1 → θ x = 0) (t : ℝ) (ht : 0 < t)
    (ρ : E → ℝ → ℝ) (m : E → ℕ) (C : ℝ) (hC : 1 ≤ C)
    (hshell : ∀ e r, ρ e r ≠ 0 → r ≤ C / (2 : ℝ) ^ m e)
    (r : E → ℝ) (hr : ∀ e, 0 ≤ r e)
    (h : graphTaper a b θ t r * shellWeight ρ r ≠ 0) :
    Admissible a b (levelBudget (C ^ Fintype.card E) t) m := by
  intro i
  exact level_le_budget (taper_shell_inverse_bound a b θ hθ t ht ρ m C hC hshell r hr h i).le

end CausalLowerbound.PartB.ConfigurationShells
