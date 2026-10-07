import CausalLowerbound.PartC.UntaperedGhostMatching

/-! Removing the actual complete-graph ghost taper has a quantitative
cost. The cost is the cube integral of its defect, and the pattern bound
keeps the selected-slot normalization independent of N. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I G : Type*} [Fintype d] [DecidableEq d] [Fintype I] [Fintype G]

theorem integral_taper_removal_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (F χ : X → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hi : Integrable F μ) (hχm : AEStronglyMeasurable χ μ)
    (hF : ∀ x, |F x| ≤ M) (hχ : ∀ x, |χ x| ≤ 1) :
    |(∫ x, χ x * F x ∂μ) - ∫ x, F x ∂μ| ≤ M * ∫ x, 1 - χ x ∂μ := by
  have hiχ : Integrable (fun x => χ x * F x) μ := (integrable_const M).mono'
    (hχm.mul hi.aestronglyMeasurable) (Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul (hχ x) (hF x) (abs_nonneg _) zero_le_one).trans_eq (one_mul M)))
  have hnonneg (x : X) : 0 ≤ 1 - χ x := sub_nonneg.mpr ((le_abs_self _).trans (hχ x))
  have hχi : Integrable (fun x => 1 - χ x) μ := (integrable_const (2 : ℝ)).mono'
    (aestronglyMeasurable_const.sub hχm) (Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs]
      exact (abs_sub _ _).trans (by have h := hχ x; norm_num at *; linarith)))
  have hb (x : X) : |χ x * F x - F x| ≤ M * (1 - χ x) := by
    have he : χ x * F x - F x = -(1 - χ x) * F x := by ring
    rw [he, abs_mul, abs_neg, abs_of_nonneg (hnonneg x)]
    exact (mul_le_mul_of_nonneg_left (hF x) (hnonneg x)).trans_eq (mul_comm _ _)
  rw [← integral_sub hiχ hi]
  apply abs_integral_le_integral_abs.trans
  exact (integral_mono (hiχ.sub hi).abs (hχi.const_mul M) hb).trans_eq (integral_const_mul M _)

def completedGhostTaperDefect (Q : ℕ) (e : I ⊕ G ≃ Fin Q) (τ : ℝ) (u : I → d → ℝ) : ℝ :=
  ∫ g : G → d → ℝ, 1 - completedCubeTaper Q e τ (u, g) ∂Measure.pi (fun _ : G => cubeMeasure d)

theorem completedGhostTaperDefect_bounds (Q : ℕ) (e : I ⊕ G ≃ Fin Q) (τ : ℝ) (u : I → d → ℝ) :
    0 ≤ completedGhostTaperDefect Q e τ u ∧ completedGhostTaperDefect Q e τ u ≤ 1 := by
  have hm : AEStronglyMeasurable (fun g : G → d → ℝ => 1 - completedCubeTaper Q e τ (u, g))
      (Measure.pi (fun _ : G => cubeMeasure d)) :=
    (continuous_const.sub ((completedCubeTaper_continuous Q e τ).comp
      (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  have hb (g : G → d → ℝ) : 0 ≤ 1 - completedCubeTaper Q e τ (u, g) ∧
      1 - completedCubeTaper Q e τ (u, g) ≤ 1 := by
    have h := completedCubeTaper_bounds Q e τ (u, g)
    constructor <;> linarith
  have hi : Integrable (fun g : G → d → ℝ => 1 - completedCubeTaper Q e τ (u, g))
      (Measure.pi (fun _ : G => cubeMeasure d)) :=
    (integrable_const (1 : ℝ)).mono' hm (Filter.Eventually.of_forall (fun g => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hb g).1] using (hb g).2))
  refine ⟨integral_nonneg (fun g => (hb g).1), ?_⟩
  have h := integral_mono hi (integrable_const (1 : ℝ)) (fun g => (hb g).2)
  simpa only [completedGhostTaperDefect, integral_const, measureReal_univ_eq_one, one_smul] using h

theorem selectedGhostTaper_defect_integrable (Q : ℕ) (e : I ⊕ G ≃ Fin Q) (τ : ℝ)
    (u : I → d → ℝ) (A : Finset (Fin Q)) :
    Integrable (fun g => 1 - selectedGhostTaper Q e τ u A g) (Measure.pi (fun _ : G => cubeMeasure d)) := by
  apply (integrable_const (2 : ℝ)).mono'
    (continuous_const.sub (selectedGhostTaper_continuous Q e τ u A)).aestronglyMeasurable
  filter_upwards [] with g
  change |1 - selectedGhostTaper Q e τ u A g| ≤ 2
  exact (abs_sub _ _).trans (by have h := selectedGhostTaper_abs_le Q e τ u A g; norm_num at *; linarith)

theorem selectedGhostTaper_defect_le (Q : ℕ) (e : I ⊕ G ≃ Fin Q) (τ : ℝ)
    (u : I → d → ℝ) (A : Finset (Fin Q)) :
    (∫ g, 1 - selectedGhostTaper Q e τ u A g ∂Measure.pi (fun _ : G => cubeMeasure d)) ≤
      completedGhostTaperDefect Q e τ u := by
  by_cases hA : A = ∅
  · simpa only [selectedGhostTaper, if_pos hA, sub_self, integral_zero] using
      (completedGhostTaperDefect_bounds Q e τ u).1
  · simp only [selectedGhostTaper, if_neg hA, completedGhostTaperDefect, le_refl]

theorem physicalGhostPatternWeight_taper_removal_bound
    (Q : ℕ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N N₀ ja τ : ℝ)
    (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀) (hja : ja ^ 2 ≤ 1)
    (B : Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (e : I ⊕ G ≃ Fin Q) (u : I → d → ℝ)
    (ζ η : activeBlocks (d := d) ℓ h → Bool) (A : Finset (Fin Q)) :
    |physicalGhostPatternWeight Q x₀ ℓ r h k c w N ja τ B e u ζ η A -
      ghostPatternIntegral x₀ ℓ r h k c w N ja B e u
        (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (u i)) η A (fun _ => 1)| ≤
      ((1 + N₀ / c + 1 / (c * N₀)) ^ Q * ‖B‖) * completedGhostTaperDefect Q e τ u := by
  let μ := Measure.pi (fun _ : G => cubeMeasure d)
  let F := partialPhysicalPatternWeight x₀ ℓ r h k c w N ja B e u
    (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (u i)) η A
  let χ := selectedGhostTaper Q e τ u A
  let C := 1 + N₀ / c + 1 / (c * N₀)
  let M := C ^ Q * ‖B‖
  have hcz : 0 ≤ N₀ / c := by positivity
  have hcκ : 0 ≤ 1 / (c * N₀) := by positivity
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hCz : N₀ / c ≤ C := by dsimp [C]; linarith
  have hCκ : 1 / (c * N₀) ≤ C := by dsimp [C]; linarith
  have hM : 0 ≤ M := mul_nonneg (pow_nonneg (zero_le_one.trans hC) Q) (norm_nonneg _)
  have hF (g : G → d → ℝ) : |F g| ≤ M := by
    simpa only [Fintype.card_fin] using partialPhysicalPatternWeight_bound x₀ ℓ r h k c w N N₀ ja
      hc hN₀ hN hm hrough hja B e u _
      (fun i => normalizedRoughChart_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough ζ (u i))
      C hC hCz hCκ (fun i =>
        (normalizedRoughChart_scaled_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough ζ (u i)).trans hCz)
      η A g
  have hi : Integrable F μ := (integrable_const M).mono'
    (partialPhysicalPatternWeight_continuous x₀ ℓ r h k c w N ja hc B e u _ η A).aestronglyMeasurable
    (Filter.Eventually.of_forall hF)
  change |(∫ g, χ g * F g ∂μ) - ∫ g, (1 : ℝ) * F g ∂μ| ≤ _
  simp only [one_mul]
  apply (integral_taper_removal_bound μ F χ M hM hi
    (selectedGhostTaper_continuous Q e τ u A).aestronglyMeasurable hF
    (selectedGhostTaper_abs_le Q e τ u A)).trans
  exact mul_le_mul_of_nonneg_left (selectedGhostTaper_defect_le Q e τ u A) hM

end CausalLowerbound.PartC
