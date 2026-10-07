import CausalLowerbound.PartB.PhysicalJitterMoments

/-! Full matching and quantitative partial matching at a physical
observation, using the actual smooth packet variance and correction. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
namespace CausalLowerbound.PartB.ShellGeometry
variable {d : Type*} [Fintype d] [DecidableEq d]

def physicalJitterField (x₀ : d → ℝ) (r h t : ℝ) (x : d → ℝ)
    (active : activeBlocks (d := d) r h → Bool) (ζ : activeBlocks (d := d) r h → Bool) : ℝ :=
  t * ∑ k, (if active k then packet (coarseBump x₀ h) x₀ r k.val x else 0) * sign (ζ k)

theorem physicalJitter_propensity (x₀ : d → ℝ) (r h a t : ℝ) (x : d → ℝ)
    (active ζ : activeBlocks (d := d) r h → Bool) (z : ℝ) :
    a * (z + physicalJitterField x₀ r h t x active ζ) =
      a * z + independentSignSum (maskedWeights (physicalJitterWeights x₀ r h a t x) active) ζ := by
  rw [mul_add]
  congr 1
  simp only [physicalJitterField, independentSignSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  cases hk : active k <;> simp [maskedWeights, physicalJitterWeights, hk] <;> ring

theorem siteFieldLikelihood_as_cubic (side : Bool) (R T a b η δ z : ℝ) (ha : a ≠ 0) :
    siteFieldLikelihood side R T a b η δ z =
      codedLikelihood R T (a * z)
        (if side then cubic (b / a) η (a * z) - δ * (1 + 2 * (a * z)) else cubic (b / a) η (a * z))
        (if side then δ else 0) := by
  have he : b * ((1 + η) * z - a ^ 2 / 3 * z ^ 3) = cubic (b / a) η (a * z) := by
    unfold cubic
    field_simp
    ring
  unfold siteFieldLikelihood
  rw [he]
  congr 1
  cases side <;> simp only [Bool.false_eq_true, if_false, if_true] <;> ring

theorem physical_partial_likelihood_stability (x₀ : d → ℝ) (r h a b t : ℝ)
    (hr : 0 < r) (hh : 0 < h) (ha : 0 < a) (hb : 0 ≤ b) (hat : a ^ 2 * t ^ 2 ≤ 1)
    (x : d → ℝ) (z : ℝ) (hp : |a * z| ≤ 1)
    (active : activeBlocks (d := d) r h → Bool) (R T : Bool) :
    |independentSigns.expect (fun ζ => siteFieldLikelihood false (sign R) (sign T) a b
        (packetEta (activeBlocks r h) x₀ r h a t x) (targetField x₀ h (a * b * t ^ 2) x)
          (z + physicalJitterField x₀ r h t x active ζ)) -
      siteFieldLikelihood true (sign R) (sign T) a b
        (packetEta (activeBlocks r h) x₀ r h a t x) (targetField x₀ h (a * b * t ^ 2) x) z| ≤
      6 * (a * b * t ^ 2) := by
  have hη := physical_packetEta_bounds x₀ r h a t hr hat x
  have he := finite_partial_likelihood_stability (physicalJitterWeights x₀ r h a t x) active
    (a * z) (b / a) (packetEta (activeBlocks r h) x₀ r h a t x) hp (div_nonneg hb ha.le)
    hη.1 hη.2 (physicalJitter_variance_le_one x₀ r h a t hr hh hat x)
    (physicalJitter_correction x₀ r h a t hr hh x) R T
  rw [physicalJitter_target x₀ r h a b t hr hh ha.ne'] at he
  simp_rw [siteFieldLikelihood_as_cubic _ _ _ _ _ _ _ _ ha.ne',
    Bool.false_eq_true, if_false, if_true, physicalJitter_propensity]
  have hδ : 0 ≤ a * b * t ^ 2 := mul_nonneg (mul_nonneg ha.le hb) (sq_nonneg t)
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact (le_abs_self _).trans ((targetField_abs_le x₀ h (a * b * t ^ 2) x).trans (le_of_eq (abs_of_nonneg hδ)))

theorem physical_full_likelihood_match (x₀ : d → ℝ) (r h a b t : ℝ)
    (hr : 0 < r) (hh : 0 < h) (ha : a ≠ 0) (x : d → ℝ) (z R T : ℝ) :
    independentSigns.expect (fun ζ => siteFieldLikelihood false R T a b
      (packetEta (activeBlocks r h) x₀ r h a t x) (targetField x₀ h (a * b * t ^ 2) x)
        (z + physicalJitterField x₀ r h t x (fun _ => true) ζ)) =
      siteFieldLikelihood true R T a b (packetEta (activeBlocks r h) x₀ r h a t x)
        (targetField x₀ h (a * b * t ^ 2) x) z := by
  have he := finite_full_likelihood_match (physicalJitterWeights x₀ r h a t x)
    (a * z) (b / a) (packetEta (activeBlocks r h) x₀ r h a t x) R T
    (physicalJitter_correction x₀ r h a t hr hh x)
  rw [physicalJitter_target x₀ r h a b t hr hh ha] at he
  simp_rw [siteFieldLikelihood_as_cubic _ _ _ _ _ _ _ _ ha,
    Bool.false_eq_true, if_false, if_true, physicalJitter_propensity]
  have hw : maskedWeights (physicalJitterWeights x₀ r h a t x) (fun _ => true) =
      physicalJitterWeights x₀ r h a t x := by funext k; simp [maskedWeights]
  rw [hw]
  exact he

end CausalLowerbound.PartB.ShellGeometry
