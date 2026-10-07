import CausalLowerbound.PartC.CarriedField
import CausalLowerbound.PartC.PhysicalRoughRegularity
import CausalLowerbound.PartB.PacketAmplitudes

/-! Uniform derivative bounds for both complete coded outcomes. The
rough-outcome correction is controlled at the fine scale and the
rough-propensity outcome at the carrier scale. -/
noncomputable section
set_option autoImplicit false
open scoped ContDiff
namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [Fintype Ω]

theorem coarseSquare_scale_control (M : ℕ) :
    ∃ C > 0, ∀ (x₀ : d → ℝ) (r h : ℝ), 0 < r → r ≤ h →
      ScaleControl M r C (fun x => coarseBump x₀ h x ^ 2) := by
  obtain ⟨C, hC, hb⟩ := compact_smooth_derivatives_bounded (targetProfile (d := d))
    targetProfile_smooth targetProfile_compact M
  refine ⟨C, hC, fun x₀ r h hr hrh => ?_⟩
  have hh := hr.trans_le hrh
  have he : ScaleControl M h C (rescaled targetProfile x₀ h) :=
    ⟨rescaled_smooth _ targetProfile_smooth _ _, hh, hC.le,
      fun j hj x => rescaled_derivative_bound _ targetProfile_smooth _ h hh j C hC.le (hb j hj) x⟩
  exact he.finer hr hrh

def normalizedPropensityOutcome {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h ja t : ℝ) (x : d → ℝ) : ℝ :=
  if side then carriedField S U x₀ r x - (ja * t) * coarseBump x₀ h x ^ 2
  else carriedField S U x₀ r x

def normalizedRoughOutcome {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (ℓ r h a ja : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (x : d → ℝ) : ℝ :=
  physicalRoughField x₀ ℓ h ζ x *
    (1 + physicalRoughCorrection x₀ ℓ h ja x - (a * carriedField S U x₀ r x) ^ 2) -
    if side then ja * (coarseBump x₀ h x ^ 2 * (1 + 3 * (a * carriedField S U x₀ r x))) else 0

theorem physicalRoughCorrection_smooth (x₀ : d → ℝ) (ℓ h ja : ℝ) :
    ContDiff ℝ ∞ (physicalRoughCorrection x₀ ℓ h ja) :=
  (contDiff_const.mul ((rescaled_smooth _ quadraticPartition_smooth _ _).pow 2)).mul
    (contDiff_const.sub (contDiff_const.mul (quarticField_smooth _ _ _)))

theorem normalizedPropensityOutcome_smooth {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h ja t : ℝ) :
    ContDiff ℝ ∞ (normalizedPropensityOutcome side S U x₀ r h ja t) := by
  cases side with
  | false => exact carriedField_smooth _ _ _ _
  | true =>
    exact (carriedField_smooth _ _ _ _).sub
      (contDiff_const.mul ((rescaled_smooth _ quadraticPartition_smooth _ _).pow 2))

theorem normalizedRoughOutcome_smooth {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (ℓ r h a ja : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) :
    ContDiff ℝ ∞ (normalizedRoughOutcome side S U x₀ ℓ r h a ja ζ) := by
  have hp : ContDiff ℝ ∞ (fun x => a * carriedField S U x₀ r x) :=
    contDiff_const.mul (carriedField_smooth S U x₀ r)
  have hy : ContDiff ℝ ∞ (fun x => physicalRoughField x₀ ℓ h ζ x *
      (1 + physicalRoughCorrection x₀ ℓ h ja x - (a * carriedField S U x₀ r x) ^ 2)) :=
    (physicalRoughField_smooth x₀ ℓ h ζ).mul
      ((contDiff_const.add (physicalRoughCorrection_smooth x₀ ℓ h ja)).sub (hp.pow 2))
  cases side with
  | false =>
    change ContDiff ℝ ∞ (fun x => physicalRoughField x₀ ℓ h ζ x *
      (1 + physicalRoughCorrection x₀ ℓ h ja x - (a * carriedField S U x₀ r x) ^ 2) - 0)
    simpa only [sub_zero] using hy
  | true => exact hy.sub (contDiff_const.mul
      (((rescaled_smooth _ quadraticPartition_smooth _ _).pow 2).mul
        (contDiff_const.add (contDiff_const.mul hp))))

theorem normalizedPropensityOutcome_scale_control {Q : ℕ}
    (U : Ω → CoefficientExponent d Q → ℝ) (M : ℕ) :
    ∃ C > 0, ∀ (side : Bool) (S : Finset (d → ℤ)) (sample : (d → ℤ) → Ω)
      (x₀ : d → ℝ) (r h ja t : ℝ), 0 < r → r ≤ h → 0 ≤ ja → ja ≤ 1 → 0 ≤ t → t ≤ 1 →
      ScaleControl M r C (normalizedPropensityOutcome side S (fun k => U (sample k)) x₀ r h ja t) := by
  obtain ⟨A, hA, ha⟩ := carriedField_scale_control U M
  obtain ⟨B, hB, hb⟩ := coarseSquare_scale_control (d := d) M
  refine ⟨A + B, add_pos hA hB, fun side S sample x₀ r h ja t hr hrh hja hja1 ht ht1 => ?_⟩
  have hp := ha S sample x₀ r hr
  have hg := (hb x₀ r h hr hrh).smul_le (ja * t) 1 (by
    rw [abs_of_nonneg (mul_nonneg hja ht)]
    exact (mul_le_mul hja1 ht1 ht zero_le_one).trans_eq (one_mul 1))
  simp only [one_mul] at hg
  cases side with
  | false => exact hp.mono (le_add_of_nonneg_right hB.le)
  | true => exact hp.sub hg

theorem physicalRoughCorrection_scale_control (M : ℕ) :
    ∃ C > 0, ∀ (x₀ : d → ℝ) (ℓ h ja : ℝ), 0 < ℓ → ℓ ≤ h → 0 ≤ ja → ja ≤ 1 →
      ScaleControl M ℓ C (physicalRoughCorrection x₀ ℓ h ja) := by
  obtain ⟨A, hA, ha⟩ := coarseSquare_scale_control (d := d) M
  obtain ⟨B, hB, hb⟩ := quarticField_derivative_bound (d := d) M
  refine ⟨(2 : ℝ) ^ M * A * (3 + 2 * B), by positivity,
    fun x₀ ℓ h ja hℓ hℓh hja hja1 => ?_⟩
  have hg := ha x₀ ℓ h hℓ hℓh
  have hq : ScaleControl M ℓ B (quarticField (activeBlocks ℓ h) x₀ ℓ) :=
    ⟨quarticField_smooth _ _ _, hℓ, hB.le, hb _ _ _ hℓ⟩
  have hc := (ScaleControl.const (E := d → ℝ) M ℓ 3 hℓ).sub (hq.smul 2)
  have hc' : ScaleControl M ℓ (3 + 2 * B) (fun x => 3 - 2 * quarticField (activeBlocks ℓ h) x₀ ℓ x) := by
    simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_pos (by norm_num : (0 : ℝ) < 2)] using hc
  have he := (hg.mul hc' hℓ).smul_le (ja ^ 2) 1 (by rw [abs_of_nonneg (sq_nonneg _)]; nlinarith)
  change ScaleControl M ℓ _ (fun x => ja ^ 2 * coarseBump x₀ h x ^ 2 *
    (3 - 2 * quarticField (activeBlocks ℓ h) x₀ ℓ x))
  simpa only [one_mul, physicalRoughCorrection, mul_assoc] using he

theorem normalizedRoughOutcome_scale_control {Q : ℕ}
    (U : Ω → CoefficientExponent d Q → ℝ) (M : ℕ) :
    ∃ C > 0, ∀ (side : Bool) (S : Finset (d → ℤ)) (sample : (d → ℤ) → Ω)
      (x₀ : d → ℝ) (ℓ r h a ja : ℝ), 0 < ℓ → ℓ ≤ r → r ≤ h →
      0 ≤ a → a ≤ 1 → 0 ≤ ja → ja ≤ 1 → ∀ ζ : activeBlocks (d := d) ℓ h → Bool,
      ScaleControl M ℓ C (normalizedRoughOutcome side S (fun k => U (sample k)) x₀ ℓ r h a ja ζ) := by
  obtain ⟨A, hA, ha⟩ := carriedField_scale_control U M
  obtain ⟨B, hB, hb⟩ := physicalRoughField_scale_control (d := d) M
  obtain ⟨D, hD, hd⟩ := coarseSquare_scale_control (d := d) M
  obtain ⟨Eη, hEη, hη⟩ := physicalRoughCorrection_scale_control (d := d) M
  let Epp := (2 : ℝ) ^ M * A * A
  let Ey := (2 : ℝ) ^ M * B * (1 + Eη + Epp)
  let Ez := (2 : ℝ) ^ M * D * (1 + 3 * A)
  refine ⟨Ey + Ez, by dsimp [Ey, Ez, Epp]; positivity,
    fun side S sample x₀ ℓ r h a ja hℓ hℓr hrh ha0 ha1 hja0 hja1 ζ => ?_⟩
  have hr := hℓ.trans_le hℓr
  have hℓh := hℓr.trans hrh
  have hp : ScaleControl M ℓ A (fun x => a * carriedField S (fun k => U (sample k)) x₀ r x) := by
    simpa only [one_mul] using ((ha S sample x₀ r hr).finer hℓ hℓr).smul_le a 1
      (by rwa [abs_of_nonneg ha0])
  have hpp : ScaleControl M ℓ Epp (fun x => (a * carriedField S (fun k => U (sample k)) x₀ r x) ^ 2) := by
    simpa only [Epp, pow_two] using hp.mul hp hℓ
  have hc : ScaleControl M ℓ 1 (fun _ : d → ℝ => (1 : ℝ)) := by
    simpa only [abs_one] using ScaleControl.const (E := d → ℝ) M ℓ 1 hℓ
  have hy := (hb x₀ ℓ h hℓ hℓh ζ).mul ((hc.add (hη x₀ ℓ h ja hℓ hℓh hja0 hja1)).sub hpp) hℓ
  have hz : ScaleControl M ℓ Ez (fun x => ja * (coarseBump x₀ h x ^ 2 *
      (1 + 3 * (a * carriedField S (fun k => U (sample k)) x₀ r x)))) := by
    have hp3 : ScaleControl M ℓ (3 * A) (fun x => 3 * (a * carriedField S (fun k => U (sample k)) x₀ r x)) := by
      simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 3)] using hp.smul 3
    simpa only [one_mul] using ((hd x₀ ℓ h hℓ hℓh).mul (hc.add hp3) hℓ).smul_le ja 1
      (by rwa [abs_of_nonneg hja0])
  cases side with
  | false =>
    have he := hy.mono (le_add_of_nonneg_right (show 0 ≤ Ez by dsimp [Ez]; positivity))
    change ScaleControl M ℓ (Ey + Ez) (fun x => _ - 0)
    simpa only [sub_zero] using he
  | true => exact hy.sub hz

end CausalLowerbound.PartC
