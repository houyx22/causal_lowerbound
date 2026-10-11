import CausalLowerbound.PartB.RateRegime

/-! Exact polynomial scales for the uniform-design lower bound.  The strict
low-smoothness condition permits a fixed component cutoff; no epsilon loss is
introduced in the signal exponent. -/
noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology

namespace CausalLowerbound.UniformLowerBound

def fineRatio (A γ : ℝ) : ℝ := γ / A

def rateDenominator (A d γ : ℝ) : ℝ := d + fineRatio A γ * d + 2 * γ

def coarseExponent (A d γ : ℝ) : ℝ := 2 / rateDenominator A d γ

def fineExponent (A d γ : ℝ) : ℝ := coarseExponent A d γ * fineRatio A γ

def rateExponent (A d γ : ℝ) : ℝ := coarseExponent A d γ * γ

def sparseExponent (A d γ : ℝ) : ℝ := fineExponent A d γ * d - 1

def coarseScale (A d γ t x : ℝ) : ℝ := t * x ^ (-coarseExponent A d γ)

def fineScale (A d γ t x : ℝ) : ℝ := coarseScale A d γ t x ^ fineRatio A γ

theorem rateDenominator_pos (A d γ : ℝ) (hA : 0 < A) (hd : 0 < d)
    (hγ : 0 < γ) : 0 < rateDenominator A d γ := by
  unfold rateDenominator fineRatio
  positivity

theorem coarseExponent_pos (A d γ : ℝ) (hA : 0 < A) (hd : 0 < d)
    (hγ : 0 < γ) : 0 < coarseExponent A d γ :=
  div_pos two_pos (rateDenominator_pos A d γ hA hd hγ)

theorem rate_ordering (A d γ : ℝ) (hA : 0 < A) (hd : 0 < d)
    (hγ : 0 < γ) (hreg : A * (2 + d / γ) < d) :
    1 < fineRatio A γ ∧ 0 < sparseExponent A d γ ∧ 0 < rateExponent A d γ := by
  have hD := rateDenominator_pos A d γ hA hd hγ
  have hAg := (PartB.rate_ordering A d γ hA hd hγ hreg).1
  have hreg' : A * (2 * γ + d) < d * γ := by
    have hh := (mul_lt_mul_right hγ).mpr hreg
    field_simp at hh
    nlinarith
  have hratio : d + 2 * γ < fineRatio A γ * d := by
    have hh : d + 2 * γ < γ * d / A := (lt_div_iff₀ hA).mpr (by nlinarith)
    simpa [fineRatio, div_mul_eq_mul_div] using hh
  refine ⟨(one_lt_div hA).mpr hAg, ?_, mul_pos (coarseExponent_pos A d γ hA hd hγ) hγ⟩
  unfold sparseExponent fineExponent coarseExponent
  have hh : rateDenominator A d γ < 2 * (fineRatio A γ * d) := by
    unfold rateDenominator
    linarith
  have hm : (2 / rateDenominator A d γ) * fineRatio A γ * d =
      (2 * (fineRatio A γ * d)) / rateDenominator A d γ := by ring
  rw [hm]
  linarith [(one_lt_div hD).mpr hh]

theorem rateExponent_eq (A d γ : ℝ) (hA : 0 < A) (hd : 0 < d)
    (hγ : 0 < γ) :
    rateExponent A d γ = 1 / (1 + d / (2 * γ) + d / (2 * A)) := by
  have hD := (rateDenominator_pos A d γ hA hd hγ).ne'
  have hE : 1 + d / (2 * γ) + d / (2 * A) ≠ 0 := by positivity
  unfold rateExponent coarseExponent rateDenominator fineRatio at *
  field_simp
  ring

theorem coarseScale_pos (A d γ t x : ℝ) (ht : 0 < t) (hx : 0 < x) :
    0 < coarseScale A d γ t x := mul_pos ht (Real.rpow_pos_of_pos hx _)

theorem scales_valid (A d γ t x : ℝ) (hA : 0 < A) (hd : 0 < d)
    (hγ : 0 < γ) (hreg : A * (2 + d / γ) < d)
    (ht : 0 < t) (ht1 : t ≤ 1) (hx : 1 ≤ x) :
    0 < fineScale A d γ t x ∧ fineScale A d γ t x ≤ coarseScale A d γ t x ∧
      coarseScale A d γ t x ≤ t ∧ coarseScale A d γ t x ≤ 1 ∧
      fineScale A d γ t x ^ A = coarseScale A d γ t x ^ γ := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hh := coarseScale_pos A d γ t x ht hx0
  have hhT : coarseScale A d γ t x ≤ t := by
    unfold coarseScale
    exact mul_le_of_le_one_right ht.le
      (Real.rpow_le_one_of_one_le_of_nonpos hx (neg_nonpos.mpr
        (coarseExponent_pos A d γ hA hd hγ).le))
  have hh1 := hhT.trans ht1
  have hq := (rate_ordering A d γ hA hd hγ hreg).1
  refine ⟨Real.rpow_pos_of_pos hh _, ?_, hhT, hh1, ?_⟩
  · unfold fineScale
    simpa using Real.rpow_le_rpow_of_exponent_ge hh hh1 hq.le
  · unfold fineScale
    rw [← Real.rpow_mul hh.le]
    congr 1
    exact div_mul_cancel₀ γ hA.ne'

theorem signal_ledger (A d γ t x : ℝ) (ht : 0 < t) (hx : 0 < x) :
    coarseScale A d γ t x ^ γ = t ^ γ * x ^ (-rateExponent A d γ) := by
  unfold coarseScale rateExponent
  rw [Real.mul_rpow ht.le (Real.rpow_nonneg hx.le _), ← Real.rpow_mul hx.le]
  congr 2
  ring

theorem scale_monomial (A d γ t x u v w : ℝ) (ht : 0 < t) (hx : 0 < x) :
    x ^ u * coarseScale A d γ t x ^ v * fineScale A d γ t x ^ w =
      t ^ (v + fineRatio A γ * w) *
        x ^ (u - coarseExponent A d γ * (v + fineRatio A γ * w)) := by
  unfold fineScale
  rw [← Real.rpow_mul (coarseScale_pos A d γ t x ht hx).le]
  unfold coarseScale
  simp_rw [Real.mul_rpow ht.le (Real.rpow_nonneg hx.le _), ← Real.rpow_mul hx.le]
  calc
    _ = (t ^ v * t ^ (fineRatio A γ * w)) *
        (x ^ u * x ^ (-coarseExponent A d γ * v) *
          x ^ (-coarseExponent A d γ * (fineRatio A γ * w))) := by ring
    _ = t ^ (v + fineRatio A γ * w) *
        x ^ ((u + -coarseExponent A d γ * v) +
          -coarseExponent A d γ * (fineRatio A γ * w)) := by
      rw [← Real.rpow_add ht, ← Real.rpow_add hx, ← Real.rpow_add hx]
    _ = _ := by congr 2; ring

theorem collision_ledger (A d γ t x : ℝ) (hA : 0 < A) (hd : 0 < d)
    (hγ : 0 < γ) (ht : 0 < t) (hx : 0 < x) :
    x ^ (2 : ℝ) * coarseScale A d γ t x ^ d *
      fineScale A d γ t x ^ (d + 2 * A) = t ^ rateDenominator A d γ := by
  rw [scale_monomial A d γ t x 2 d (d + 2 * A) ht hx]
  have hdexp : d + fineRatio A γ * (d + 2 * A) = rateDenominator A d γ := by
    unfold rateDenominator fineRatio
    field_simp
    ring
  rw [hdexp]
  have he : 2 - coarseExponent A d γ * rateDenominator A d γ = 0 := by
    rw [coarseExponent, div_mul_cancel₀ _ (rateDenominator_pos A d γ hA hd hγ).ne']
    ring
  rw [he, Real.rpow_zero, mul_one]

theorem cluster_ledger (A d γ t x : ℝ) (Q : ℕ) (ht : 0 < t) (hx : 0 < x) :
    x ^ ((Q : ℝ) + 1) * coarseScale A d γ t x ^ d *
      fineScale A d γ t x ^ ((Q : ℝ) * d) =
      t ^ (d + fineRatio A γ * ((Q : ℝ) * d)) *
        x ^ (1 - coarseExponent A d γ * d - (Q : ℝ) * sparseExponent A d γ) := by
  rw [scale_monomial A d γ t x ((Q : ℝ) + 1) d ((Q : ℝ) * d) ht hx]
  congr 2
  unfold sparseExponent fineExponent
  ring

def componentCutoff (A d γ : ℝ) : ℕ :=
  PartB.matchingOrder d 1 (coarseExponent A d γ) (sparseExponent A d γ)

theorem componentCutoff_ge_two (A d γ : ℝ) : 2 ≤ componentCutoff A d γ :=
  PartB.matchingOrder_ge_two _ _ _ _

theorem componentCutoff_exponent_neg (A d γ : ℝ) (hA : 0 < A) (hd : 0 < d)
    (hγ : 0 < γ) (hreg : A * (2 + d / γ) < d) :
    1 - coarseExponent A d γ * d -
      (componentCutoff A d γ : ℝ) * sparseExponent A d γ < 0 := by
  simpa [componentCutoff, mul_comm] using
    PartB.matchingOrder_exponent_neg d 1 (coarseExponent A d γ) (sparseExponent A d γ)
      (rate_ordering A d γ hA hd hγ hreg).2.1

theorem cluster_ledger_le (A d γ t x : ℝ) (hA : 0 < A) (hd : 0 < d)
    (hγ : 0 < γ) (hreg : A * (2 + d / γ) < d) (ht : 0 < t) (hx : 1 ≤ x) :
    x ^ ((componentCutoff A d γ : ℝ) + 1) * coarseScale A d γ t x ^ d *
      fineScale A d γ t x ^ ((componentCutoff A d γ : ℝ) * d) ≤
      t ^ (d + fineRatio A γ * ((componentCutoff A d γ : ℝ) * d)) := by
  rw [cluster_ledger A d γ t x _ ht (lt_of_lt_of_le zero_lt_one hx)]
  exact mul_le_of_le_one_right (Real.rpow_nonneg ht.le _)
    (Real.rpow_le_one_of_one_le_of_nonpos hx
      (componentCutoff_exponent_neg A d γ hA hd hγ hreg).le)

/-- A single positive bandwidth multiplier makes both the collision error and
the exceptional-component error small. The constants may depend on the fixed
cutoff, but not on the sample size. -/
theorem exists_tuning (D E C K cap : ℝ) (hD : 0 < D) (hE : 0 < E)
    (hcap : 0 < cap) :
    ∃ t : ℝ, 0 < t ∧ t ≤ cap ∧ C * t ^ E + Real.sqrt (K * t ^ D) ≤ 1 / 2 := by
  let f : ℝ → ℝ := fun t => C * t ^ E + Real.sqrt (K * t ^ D)
  have hc : Continuous f :=
    (continuous_const.mul (Real.continuous_rpow_const hE.le)).add
      (Real.continuous_sqrt.comp (continuous_const.mul (Real.continuous_rpow_const hD.le)))
  have hz : f 0 = 0 := by simp [f, Real.zero_rpow hD.ne', Real.zero_rpow hE.ne']
  obtain ⟨η, hη, hclose⟩ := Metric.continuousAt_iff.mp hc.continuousAt (1 / 2) (by norm_num)
  let t := min cap η / 2
  have ht : 0 < t := div_pos (lt_min hcap hη) two_pos
  have htcap : t ≤ cap := by dsimp [t]; linarith [min_le_left cap η]
  have htη : t < η := by dsimp [t]; linarith [min_le_right cap η]
  have hb := hclose (show dist t 0 < η by simpa [Real.dist_eq, abs_of_pos ht] using htη)
  rw [hz, Real.dist_eq, sub_zero] at hb
  exact ⟨t, ht, htcap, (le_abs_self (f t)).trans hb.le⟩

end CausalLowerbound.UniformLowerBound
