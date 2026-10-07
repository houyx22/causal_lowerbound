import CausalLowerbound.WienerSeries

/-! # Bounded linear extension of a finite stencil to all absolute series -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal

namespace CausalLowerbound.Wiener

variable {ν M : Type*} [DecidableEq ν] [Fintype M] [DecidableEq M]

def stencilColumn (w : ν → M → ℝ) (i : ν) : Series (ν × M) ℝ :=
  ∑ m, lp.single 1 (i, m) (w i m)

theorem stencilColumn_bound (w : ν → M → ℝ) (i : ν) :
    ‖stencilColumn w i‖ ≤ ∑ m, |w i m| := by
  calc
    _ ≤ ∑ m, ‖(lp.single 1 (i, m) (w i m) : Series (ν × M) ℝ)‖ := norm_sum_le _ _
    _ = _ := by simp only [lp.norm_single (by norm_num : 0 < (1 : ℝ≥0∞)), Real.norm_eq_abs]

theorem stencilColumn_entry (w : ν → M → ℝ) (i j : ν) (m : M) :
    stencilColumn w i (j, m) = if j = i then w i m else 0 := by
  classical
  simp only [stencilColumn, lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Pi.single_apply]
  by_cases h : j = i
  · subst j
    simp
  · simp [h]

/-- The complete countable coefficient operator. -/
def extendStencil (w : ν → M → ℝ) (C : ℝ) (hw : ∀ i, (∑ m, |w i m|) ≤ C) :
    Series ν ℝ →L[ℝ] Series (ν × M) ℝ :=
  synthesis (stencilColumn w) C (fun i => (stencilColumn_bound w i).trans (hw i))

theorem extendStencil_bound (w : ν → M → ℝ) (C : ℝ) (hw : ∀ i, (∑ m, |w i m|) ≤ C)
    (a : Series ν ℝ) : ‖extendStencil w C hw a‖ ≤ C * ‖a‖ :=
  norm_synthesis (stencilColumn w) C (fun i => (stencilColumn_bound w i).trans (hw i)) a

theorem extendStencil_entry (w : ν → M → ℝ) (C : ℝ) (hw : ∀ i, (∑ m, |w i m|) ≤ C)
    (a : Series ν ℝ) (i : ν) (m : M) : extendStencil w C hw a (i, m) = a i * w i m := by
  change entry (i, m) (synthesis (stencilColumn w) C _ a) = _
  rw [synthesis_apply, (entry (i, m)).map_tsum
    (summable_synthesis (stencilColumn w) C (fun i => (stencilColumn_bound w i).trans (hw i)) a)]
  simp only [map_smul, entry_apply, stencilColumn_entry, smul_eq_mul]
  rw [tsum_eq_single i]
  · simp
  · intro j hj; simp [Ne.symm hj]

theorem extendStencil_absolute_bound (w : ν → M → ℝ) (C : ℝ)
    (hw : ∀ i, (∑ m, |w i m|) ≤ C) (a : Series ν ℝ) :
    Summable (fun p : ν × M => |a p.1 * w p.1 p.2|) ∧
      (∑' p : ν × M, |a p.1 * w p.1 p.2|) ≤ C * ‖a‖ := by
  have hs := summable_norm (extendStencil w C hw a)
  have hb := extendStencil_bound w C hw a
  rw [norm_eq_tsum] at hb
  have he (p : ν × M) : extendStencil w C hw a p = a p.1 * w p.1 p.2 := by
    rcases p with ⟨i, m⟩
    exact extendStencil_entry w C hw a i m
  simp only [he, Real.norm_eq_abs] at hs hb
  exact ⟨hs, hb⟩

theorem extendStencil_lipschitz (w : ν → M → ℝ) (C : ℝ)
    (hw : ∀ i, (∑ m, |w i m|) ≤ C) (a b : Series ν ℝ) :
    (∑' p : ν × M, |extendStencil w C hw a p - extendStencil w C hw b p|) ≤ C * ‖a - b‖ := by
  have h := extendStencil_bound w C hw (a - b)
  rw [map_sub, norm_eq_tsum] at h
  simpa only [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs] using h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [DecidableEq ν] [DecidableEq M] [CompleteSpace E] in
theorem stencil_synthesis_bound (w : ν → M → ℝ) (C : ℝ)
    (hw : ∀ i, (∑ m, |w i m|) ≤ C) (v : ν × M → E) (L : ℝ) (hL : 0 ≤ L)
    (hv : ∀ p, ‖v p‖ ≤ L) (i : ν) : ‖∑ m, w i m • v (i, m)‖ ≤ L * C := by
  calc
    _ ≤ ∑ m, ‖w i m • v (i, m)‖ := norm_sum_le _ _
    _ ≤ ∑ m, L * |w i m| := by
      apply Finset.sum_le_sum
      intro m _
      rw [norm_smul, Real.norm_eq_abs, mul_comm L]
      exact mul_le_mul_of_nonneg_left (hv (i, m)) (abs_nonneg _)
    _ = L * ∑ m, |w i m| := by rw [Finset.mul_sum]
    _ ≤ L * C := mul_le_mul_of_nonneg_left (hw i) hL

/-- Reconstruction survives passage from the finite stencil to the complete
ℓ¹ space. Both sides are bounded linear maps, so equality on the canonical
single-coordinate vectors extends to every absolutely summable series. -/
theorem synthesis_extendStencil (w : ν → M → ℝ) (C : ℝ)
    (hw : ∀ i, (∑ m, |w i m|) ≤ C) (v : ν × M → E) (L : ℝ) (hL : 0 ≤ L)
    (hv : ∀ p, ‖v p‖ ≤ L) (a : Series ν ℝ) :
    synthesis v L hv (extendStencil w C hw a) =
      ∑' i, a i • ∑ m, w i m • v (i, m) := by
  let left := (synthesis v L hv).comp (extendStencil w C hw)
  let right := synthesis (𝕜 := ℝ) (fun i => ∑ m, w i m • v (i, m)) (L * C)
    (stencil_synthesis_bound w C hw v L hL hv)
  have heq : left = right := by
    apply lp.ext_continuousLinearMap (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
    intro i
    apply ContinuousLinearMap.ext
    intro c
    change synthesis v L hv (synthesis (stencilColumn w) C
      (fun i => (stencilColumn_bound w i).trans (hw i)) (lp.single 1 i c)) =
      synthesis (fun i => ∑ m, w i m • v (i, m)) (L * C)
        (stencil_synthesis_bound w C hw v L hL hv) (lp.single 1 i c)
    rw [synthesis_single, synthesis_single, map_smul]
    congr 1
    simp only [stencilColumn, map_sum, synthesis_single]
  exact congrArg (fun f : Series ν ℝ →L[ℝ] E => f a) heq

end CausalLowerbound.Wiener
