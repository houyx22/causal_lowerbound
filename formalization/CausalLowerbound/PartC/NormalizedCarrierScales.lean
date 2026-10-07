import CausalLowerbound.PartC.PropensityVectorTarget
import CausalLowerbound.PartC.ScaleBudget

/-! The actual degree weight, relaxed taper, and target majorant. The
normalization pays for the assignment multiplier's small power loss, while
the remaining exponent forces the complete finite-shell bound to zero. -/

noncomputable section
set_option autoImplicit false
open Filter
open scoped BigOperators Topology

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry ConfigurationShells

def carrierDegreeWeight (R loss t : ℝ) : ℝ := R * t ^ (-loss)
def carrierTaper (gap t : ℝ) : ℝ := t ^ (1 - gap)

theorem carrierDegreeWeight_lower (R loss t : ℝ) (hR : 0 ≤ R) (hloss : 0 ≤ loss)
    (ht : 0 < t) (ht1 : t ≤ 1) : R ≤ carrierDegreeWeight R loss t := by
  exact le_mul_of_one_le_right hR (Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1 (by linarith))

theorem carrierDegreeWeight_pos (R loss t : ℝ) (hR : 0 < R) (ht : 0 < t) :
    0 < carrierDegreeWeight R loss t := mul_pos hR (Real.rpow_pos_of_pos ht _)

theorem carrierTaper_pos (gap t : ℝ) (ht : 0 < t) : 0 < carrierTaper gap t := Real.rpow_pos_of_pos ht _

theorem carrierTaper_le_one (gap t : ℝ) (hgap : gap ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    carrierTaper gap t ≤ 1 := Real.rpow_le_one ht ht1 (by linarith)

theorem normalizedCarrierRatio_eq (R p gap loss x : ℝ) (hx : 0 < x) :
    (x ^ (-p) * carrierDegreeWeight R loss (x ^ (-p))) / carrierTaper gap (x ^ (-p)) =
      R * x ^ (-(p * (gap - loss))) := by
  unfold carrierDegreeWeight carrierTaper
  simp only [← Real.rpow_mul hx.le]
  calc
    _ = R * ((x ^ (-p) * x ^ (-p * -loss)) / x ^ (-p * (1 - gap))) := by ring
    _ = R * x ^ ((-p + -p * -loss) - (-p * (1 - gap))) := by
      rw [← Real.rpow_add hx, ← Real.rpow_sub hx]
    _ = _ := by congr 1; ring

theorem carrierTaper_power (p gap x : ℝ) (hx : 0 < x) :
    carrierTaper gap (x ^ (-p)) = x ^ (-(p * (1 - gap))) := by
  rw [carrierTaper, ← Real.rpow_mul hx.le]
  congr 1
  ring

theorem carrierTaper_log_bound (p gap x : ℝ) (hp : 0 ≤ p) (hgap : gap ≤ 1) (hx : 1 ≤ x) :
    1 + Real.log (1 / carrierTaper gap (x ^ (-p))) ≤ (1 + p * (1 - gap)) * logScale x := by
  rw [carrierTaper_power p gap x (zero_lt_one.trans_le hx)]
  simpa only [logarithmicThreshold, polynomialAmplitude, Real.rpow_zero, mul_one] using
    threshold_log_bound (p * (1 - gap)) 0 (mul_nonneg hp (by linarith)) (by norm_num) hx

def normalizedCarrierBound (E D : ℕ) (C R p gap loss : ℝ) (n : ℕ) : ℝ :=
  let t := ((n : ℝ) + 1) ^ (-p)
  C * ((levelBudget 2 (carrierTaper gap t) + 1 : ℕ) : ℝ) ^ E *
    ∑ j ∈ Finset.Icc 1 D, ((t * carrierDegreeWeight R loss t) / carrierTaper gap t) ^ j

theorem normalizedCarrierBound_nonneg (E D : ℕ) (C R p gap loss : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) (n : ℕ) :
    0 ≤ normalizedCarrierBound E D C R p gap loss n := by
  unfold normalizedCarrierBound carrierDegreeWeight carrierTaper
  apply mul_nonneg (mul_nonneg hC (by positivity))
  exact Finset.sum_nonneg (fun j _ => pow_nonneg (by positivity) j)

theorem normalizedCarrierRatio_tendsto (R p gap loss : ℝ) (hp : 0 < p) (hlg : loss < gap) :
    Tendsto (fun n : ℕ =>
      (((n : ℝ) + 1) ^ (-p) * carrierDegreeWeight R loss (((n : ℝ) + 1) ^ (-p))) /
        carrierTaper gap (((n : ℝ) + 1) ^ (-p))) atTop (𝓝 0) := by
  have hh := (polynomial_log_tendsto (p * (gap - loss)) 0 (mul_pos hp (sub_pos.mpr hlg))).const_mul R
  have hmain : Tendsto (fun n : ℕ => R * ((n : ℝ) + 1) ^ (-(p * (gap - loss)))) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, Real.rpow_zero, mul_one, mul_zero] using hh
  apply hmain.congr'
  filter_upwards [] with n
  exact (normalizedCarrierRatio_eq R p gap loss _ (by positivity)).symm

theorem normalizedCarrierBound_tendsto (E D : ℕ) (C R p gap loss : ℝ)
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hp : 0 < p) (hgap : gap < 1) (hlg : loss < gap) :
    Tendsto (normalizedCarrierBound E D C R p gap loss) atTop (𝓝 0) := by
  let K := (C * logShellConstant ^ E * D) * ((1 + p * (1 - gap)) ^ E * R)
  have hlim : Tendsto (fun n : ℕ => K *
      (((n : ℝ) + 1) ^ (-(p * (gap - loss))) * logScale (n + 1) ^ E)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, Real.rpow_natCast, mul_zero] using
      (polynomial_log_tendsto (p * (gap - loss)) E (mul_pos hp (sub_pos.mpr hlg))).const_mul K
  have hratio := (normalizedCarrierRatio_tendsto R p gap loss hp hlg)
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  apply squeeze_zero' (Eventually.of_forall (normalizedCarrierBound_nonneg E D C R p gap loss hC hR)) _ hlim
  filter_upwards [hratio] with n hn
  let x : ℝ := (n : ℝ) + 1
  let t : ℝ := x ^ (-p)
  have hx : 1 ≤ x := by dsimp [x]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have ht : 0 < t := Real.rpow_pos_of_pos hx0 _
  have ht1 : t ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
  have hτ := carrierTaper_pos gap t ht
  have hτ1 := carrierTaper_le_one gap t hgap.le ht.le ht1
  have hweight : 0 ≤ carrierDegreeWeight R loss t := mul_nonneg hR (Real.rpow_nonneg ht.le _)
  have hr : 0 ≤ (t * carrierDegreeWeight R loss t) / carrierTaper gap t :=
    div_nonneg (mul_nonneg ht.le hweight) hτ.le
  have hlog : 0 ≤ 1 + Real.log (1 / carrierTaper gap t) := by
    have := Real.log_nonneg ((le_div_iff₀ hτ).mpr (by simpa using hτ1))
    linarith
  have hb := propensity_target_majorant (E := Fin E) C hC D (t * carrierDegreeWeight R loss t)
    (carrierTaper gap t) (mul_nonneg ht.le hweight) hτ hτ1 hn.le
  simp only [Fintype.card_fin] at hb
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog (carrierTaper_log_bound p gap x hp.le hgap.le hx) E)
      (by have := logShellConstant_pos; positivity : 0 ≤ C * logShellConstant ^ E * D)) hr
  apply hh.trans_eq
  rw [normalizedCarrierRatio_eq R p gap loss x hx0, mul_pow]
  dsimp [K]
  ring

end CausalLowerbound.PartC
