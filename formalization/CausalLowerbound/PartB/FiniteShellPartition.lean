import CausalLowerbound.PartB.DyadicCutoffs

/-! A single finite dyadic partition works on the full support of the taper.
Its length depends only on the taper scale, not on the configuration. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartB

open ConfigurationShells

theorem levelBudget_power (A t : ℝ) (hA : 0 < A) (ht : 0 < t) :
    A / t ≤ (2 : ℝ) ^ levelBudget A t := by
  apply (Real.log_le_log_iff (div_pos hA ht) (by positivity : 0 < (2 : ℝ) ^ levelBudget A t)).mp
  rw [Real.log_pow]
  have h := Nat.le_ceil (Real.log (A / t) / Real.log 2)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact (div_le_iff₀ hlog).mp h

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem vertexProduct_le_incident (a b : E → V) (r : E → ℝ) (hr : ∀ e, r e ∈ Set.Icc 0 1)
    (e : E) : vertexProduct a b r (a e) ≤ r e := by
  classical
  let f : E → ℝ := fun j => if incident a b (a e) j then r j else 1
  have he : f e = r e := by simp [f, incident]
  have hp : (∏ j ∈ Finset.univ.erase e, f j) ≤ 1 := by
    apply Finset.prod_le_one
    · intro j _
      dsimp [f]
      split_ifs
      · exact (hr j).1
      · exact zero_le_one
    · intro j _
      dsimp [f]
      split_ifs
      · exact (hr j).2
      · exact le_rfl
  change (∏ j, f j) ≤ r e
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ e), he]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (hr e).1

theorem taper_nonzero_edge_lower (a b : E → V) (t : ℝ) (ht : 0 < t)
    (r : E → ℝ) (hr : ∀ e, r e ∈ Set.Icc 0 1)
    (h : graphTaper a b taperCutoff t r ≠ 0) (e : E) : t < r e :=
  (taper_nonzero_vertexProduct a b taperCutoff (fun _ _ h => taperCutoff_zero h)
    t ht r (fun e => (hr e).1) h (a e)).trans_le (vertexProduct_le_incident a b r hr e)

def finiteShellCutoff (m0 L : ℕ) (s : Option (Fin L)) (r : ℝ) : ℝ :=
  shellCutoff m0 (s.map Fin.val) r

theorem finiteShellCutoff_sum (m0 L : ℕ) (r : ℝ) :
    ∑ s : Option (Fin L), finiteShellCutoff m0 L s r = coarseCutoff (m0 + L) r := by
  rw [Fintype.sum_option]
  change coarseCutoff m0 r + ∑ j : Fin L, fineCutoff (m0 + j.val) r = _
  rw [Fin.sum_univ_eq_sum_range (fun j => fineCutoff (m0 + j) r)]
  exact dyadic_partial_partition m0 L r

theorem finiteShellCutoff_sum_on_taper (m0 : ℕ) (a b : E → V) (t : ℝ) (ht : 0 < t)
    (r : E → ℝ) (hr : ∀ e, r e ∈ Set.Icc 0 1)
    (h : graphTaper a b taperCutoff t r ≠ 0) (e : E) :
    ∑ s : Option (Fin (levelBudget 2 t)), finiteShellCutoff m0 (levelBudget 2 t) s (r e) = 1 := by
  rw [finiteShellCutoff_sum]
  apply Real.smoothTransition.one_of_one_le
  have hb := levelBudget_power 2 t (by norm_num) ht
  have hp : (2 : ℝ) ^ levelBudget 2 t ≤ 2 ^ (m0 + levelBudget 2 t) :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_add_left _ _)
  have hm : 2 ≤ (2 : ℝ) ^ (m0 + levelBudget 2 t) * t :=
    (div_le_iff₀ ht).mp (hb.trans hp)
  have hed := taper_nonzero_edge_lower a b t ht r hr h e
  have hmul := mul_le_mul_of_nonneg_left hed.le (by positivity : 0 ≤ (2 : ℝ) ^ (m0 + levelBudget 2 t))
  linarith

theorem finite_tapered_shell_partition (m0 : ℕ) (a b : E → V) (t : ℝ) (ht : 0 < t)
    (r : E → ℝ) (hr : ∀ e, r e ∈ Set.Icc 0 1) :
    graphTaper a b taperCutoff t r =
      ∑ s : E → Option (Fin (levelBudget 2 t)),
        graphTaper a b taperCutoff t r * ∏ e, finiteShellCutoff m0 (levelBudget 2 t) (s e) (r e) := by
  by_cases h : graphTaper a b taperCutoff t r = 0
  · simp only [h, zero_mul, Finset.sum_const_zero]
  · rw [← Finset.mul_sum, ← Fintype.prod_sum
      (fun (e : E) (s : Option (Fin (levelBudget 2 t))) => finiteShellCutoff m0 (levelBudget 2 t) s (r e))]
    simp only [finiteShellCutoff_sum_on_taper m0 a b t ht r hr h, Finset.prod_const_one, mul_one]

theorem finite_shell_count (L : ℕ) :
    Fintype.card (E → Option (Fin L)) = (L + 1) ^ Fintype.card E := by
  simp only [Fintype.card_fun, Fintype.card_option, Fintype.card_fin]

end CausalLowerbound.PartB
