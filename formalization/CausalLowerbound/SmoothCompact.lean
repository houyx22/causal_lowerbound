import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Group.Bounded

/-! Compact sets of parameters turn joint smoothness into scale-independent
bounds for all derivatives through any fixed order. -/

noncomputable section
set_option autoImplicit false
open scoped ContDiff BigOperators Topology

namespace CausalLowerbound

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem compact_iteratedFDeriv_bound (f : E → F) (K : Set E) (hK : IsCompact K)
    (hf : ∀ x ∈ K, ContDiffAt ℝ ∞ f x) (M : ℕ) :
    ∃ C > 0, ∀ j ≤ M, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  have hb (j : ℕ) : ∃ C, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
    apply hK.exists_bound_of_continuousOn
    intro x hx
    exact ((hf x hx).iteratedFDeriv_right (m := 0)
      (by simpa using (show (j : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))).continuousAt.continuousWithinAt
  choose B hB using hb
  refine ⟨1 + ∑ j ∈ Finset.range (M + 1), |B j|, by positivity, ?_⟩
  intro j hj x hx
  have hmem : j ∈ Finset.range (M + 1) := Finset.mem_range.mpr (by omega)
  have hle := Finset.single_le_sum (fun i (_ : i ∈ Finset.range (M + 1)) => abs_nonneg (B i)) hmem
  exact (hB j x hx).trans ((le_abs_self _).trans (hle.trans (by linarith)))

variable {G P : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem iteratedFDeriv_comp_linear_at (f : E → F) (g : G →L[ℝ] E) (x : G) (j : ℕ)
    (hf : ContDiffAt ℝ j f (g x)) :
    iteratedFDeriv ℝ j (f ∘ g) x =
      (iteratedFDeriv ℝ j f (g x)).compContinuousLinearMap (fun _ => g) := by
  obtain ⟨U, hUx, hU⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hUx
  have hpre := hV.preimage g.continuous
  have h := g.iteratedFDerivWithin_comp_right (hU.mono hVU) hV.uniqueDiffOn
    hpre.uniqueDiffOn hxV (i := j) le_rfl
  rw [iteratedFDerivWithin_of_isOpen j hpre hxV,
    iteratedFDerivWithin_of_isOpen j hV hxV] at h
  exact h

/-- Restricting to the variables of a profile cannot increase the norm of its
joint derivative; the parameter is held fixed, including boundary parameters. -/
theorem norm_iteratedFDeriv_slice_le (f : P × E → F) (p : P) (x : E) (j : ℕ)
    (hf : ContDiffAt ℝ j f (p, x)) :
    ‖iteratedFDeriv ℝ j (fun y => f (p, y)) x‖ ≤ ‖iteratedFDeriv ℝ j f (p, x)‖ := by
  let g : E →L[ℝ] P × E := ContinuousLinearMap.inr ℝ P E
  let h : P × E → F := fun y => f ((p, 0) + y)
  have hh : ContDiffAt ℝ j h (g x) := by
    have heq : (p, (0 : E)) + g x = (p, x) := by ext <;> simp [g]
    have hf' : ContDiffAt ℝ j f ((p, 0) + g x) := heq.symm ▸ hf
    exact hf'.comp (g x) (contDiffAt_const.add contDiffAt_id)
  have he := iteratedFDeriv_comp_linear_at h g x j hh
  have he' : iteratedFDeriv ℝ j (fun y => f (p, y)) x =
      (iteratedFDeriv ℝ j f (p, x)).compContinuousLinearMap (fun _ => g) := by
    simpa [h, g, Function.comp_def, iteratedFDeriv_comp_add_left] using he
  have hg : ‖g‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y
    simp [g]
  rw [he']
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hp : (∏ _i : Fin j, ‖g‖) ≤ 1 := by
    simpa using (Finset.prod_le_prod (s := Finset.univ) (fun _ _ => norm_nonneg g)
      (fun _ _ => hg) : (∏ _i : Fin j, ‖g‖) ≤ ∏ _i : Fin j, (1 : ℝ))
  exact mul_le_of_le_one_right (norm_nonneg _) hp

theorem compact_slice_derivative_bound (f : P × E → F) (K : Set (P × E)) (hK : IsCompact K)
    (hf : ∀ y ∈ K, ContDiffAt ℝ ∞ f y) (M : ℕ) :
    ∃ C > 0, ∀ j ≤ M, ∀ p x, (p, x) ∈ K →
      ‖iteratedFDeriv ℝ j (fun y => f (p, y)) x‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compact_iteratedFDeriv_bound f K hK hf M
  refine ⟨C, hC, fun j hj p x hx => ?_⟩
  exact (norm_iteratedFDeriv_slice_le f p x j
    ((hf (p, x) hx).of_le (WithTop.coe_le_coe.mpr le_top))).trans (hb j hj (p, x) hx)

end CausalLowerbound
