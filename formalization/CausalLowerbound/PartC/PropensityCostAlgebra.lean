import CausalLowerbound.PartC.MixedScaleBalance

/-! The explicit degree-one information bound reduces to the three
vanishing mixed-rate monomials. In particular the squared geometry
cost is smaller than the singleton budget. -/

noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology
namespace CausalLowerbound.PartC

def propensityScalarCost (D : ℕ) (CF CC B CG ℓ r h n δ τv w : ℝ) : ℝ :=
  CF * δ ^ 2 * ((5 : ℝ) ^ D * ((ℓ / (2 * r)) ^ D) ^ 2 *
    (B * 10 ^ D * (n * h ^ D)) + CG * (n * h ^ D * τv)) +
  CC * δ ^ 2 * (n ^ 2 * B ^ 2 * ((10 * h) ^ D * (4 * ℓ) ^ D) +
    (B * (2 * D * (2 : ℝ) ^ (D - 1) * 7 ^ D)) * (n * h ^ D * w))

theorem propensity_geometry_square_le (D : ℕ) (r t : ℝ)
    (hr : 0 < r) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (((t * r) / (2 * r)) ^ D) ^ 2 ≤ t ^ D := by
  have he : t * r / (2 * r) = t / 2 := by field_simp; ring
  rw [he]
  have hq : 0 ≤ (t / 2) ^ D := pow_nonneg (by positivity) _
  have hq1 : (t / 2) ^ D ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
  have hqt : (t / 2) ^ D ≤ t ^ D := pow_le_pow_left₀ (by positivity) (by linarith) _
  exact (show ((t / 2) ^ D) ^ 2 ≤ (t / 2) ^ D by nlinarith).trans hqt

theorem propensityScalarCost_le_monomials (D : ℕ) (CF CC B CG r h n δ τv w t : ℝ)
    (hCF : 0 ≤ CF) (hCC : 0 ≤ CC) (hB : 0 ≤ B)
    (hr : 0 < r) (hh : 0 ≤ h) (hn : 0 ≤ n) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hw : w ≤ t ^ D) :
    propensityScalarCost D CF CC B CG (t * r) r h n δ τv w ≤
      (CF * (5 ^ D * B * 10 ^ D) + CC * (B * (2 * D * (2 : ℝ) ^ (D - 1) * 7 ^ D))) *
        (n * h ^ D * t ^ D * δ ^ 2) +
      (CF * CG) * (n * h ^ D * τv * δ ^ 2) +
      (CC * (B ^ 2 * 10 ^ D * 4 ^ D)) * (n ^ 2 * h ^ D * (t * r) ^ D * δ ^ 2) := by
  have hg := propensity_geometry_square_le D r t hr ht ht1
  have hf := mul_le_mul_of_nonneg_left hg
    (show 0 ≤ CF * (5 ^ D * B * 10 ^ D) * (n * h ^ D * δ ^ 2) by positivity)
  have hw' := mul_le_mul_of_nonneg_left hw
    (show 0 ≤ CC * (B * (2 * D * (2 : ℝ) ^ (D - 1) * 7 ^ D)) * (n * h ^ D * δ ^ 2) by positivity)
  have he : propensityScalarCost D CF CC B CG (t * r) r h n δ τv w =
      CF * (5 ^ D * B * 10 ^ D) * (n * h ^ D * δ ^ 2) * (((t * r) / (2 * r)) ^ D) ^ 2 +
      CC * (B * (2 * D * (2 : ℝ) ^ (D - 1) * 7 ^ D)) * (n * h ^ D * δ ^ 2) * w +
      (CF * CG) * (n * h ^ D * τv * δ ^ 2) +
      (CC * (B ^ 2 * 10 ^ D * 4 ^ D)) * (n ^ 2 * h ^ D * (t * r) ^ D * δ ^ 2) := by
    simp only [propensityScalarCost, mul_pow]
    ring
  rw [he]
  calc
    _ ≤ CF * (5 ^ D * B * 10 ^ D) * (n * h ^ D * δ ^ 2) * t ^ D +
        CC * (B * (2 * D * (2 : ℝ) ^ (D - 1) * 7 ^ D)) * (n * h ^ D * δ ^ 2) * t ^ D +
        (CF * CG) * (n * h ^ D * τv * δ ^ 2) +
        (CC * (B ^ 2 * 10 ^ D * 4 ^ D)) * (n ^ 2 * h ^ D * (t * r) ^ D * δ ^ 2) :=
      add_le_add_right (add_le_add_right (add_le_add hf hw') _) _
    _ = _ := by ring

theorem carrierScale_sparse (D : ℕ) (hD : 0 < D) (A ε : ℝ)
    (hA : 0 < A) (hε : 0 ≤ ε) (n : ℕ) :
    ((n : ℝ) + 1) * carrierScale A D ε n ^ D ≤ 1 := by
  have hDc : 0 < (D : ℝ) := by exact_mod_cast hD
  have he : 1 - carrierExponent A D ε * D ≤ 0 := by
    have ha : 0 ≤ ε / (2 * A) := div_nonneg hε (by positivity)
    have hd : (1 / (D : ℝ)) * D = 1 := div_mul_cancel₀ _ hDc.ne'
    change 1 - (1 / (D : ℝ) + ε / (2 * A)) * D ≤ 0
    nlinarith
  have hx : 0 < (n : ℝ) + 1 := by positivity
  unfold carrierScale
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  conv_lhs => arg 1; rw [← Real.rpow_one ((n : ℝ) + 1)]
  rw [← Real.rpow_add hx]
  exact Real.rpow_le_one_of_one_le_of_nonpos (le_add_of_nonneg_left (Nat.cast_nonneg n)) (by linarith)

theorem propensityScalarCost_le_rates (D : ℕ) (A γ s ε a CF CC B CG v gap : ℝ)
    (hA : 0 < A) (hD : 0 < (D : ℝ)) (hγ : 0 < γ) (hs : 0 < s)
    (hreg : A * (2 + (D : ℝ) / γ) < D) (hε : 0 < ε)
    (hεsmall : ε < γ / D - rateExponent A D γ s)
    (hCF : 0 ≤ CF) (hCC : 0 ≤ CC) (hB : 0 ≤ B)
    (n : ℕ) (w : ℝ) (hw : w ≤ jitterScale A D γ s ε n ^ D) :
    propensityScalarCost D CF CC B CG (roughScale A D γ s ε n)
      (carrierScale A D ε n) (coarseScale A D γ s ε n) ((n : ℝ) + 1)
      (a * signalScale A D γ s ε n) ((jitterScale A D γ s ε n ^ (1 - gap)) ^ v) w ≤
    a ^ 2 * ((CF * (5 ^ D * B * 10 ^ D) + CC * (B * (2 * D * (2 : ℝ) ^ (D - 1) * 7 ^ D))) *
      singletonMass A D γ s ε ((n : ℝ) + 1) +
      (CF * CG) * relaxedGhostMass A D γ s ε v gap ((n : ℝ) + 1) +
      (CC * (B ^ 2 * 10 ^ D * 4 ^ D)) * collisionMass A D γ s ε ((n : ℝ) + 1)) := by
  have hb := scales_balanced A D γ s ε hA hD hγ hs hreg hε hεsmall n
  have he := propensityScalarCost_le_monomials D CF CC B CG (carrierScale A D ε n)
    (coarseScale A D γ s ε n) ((n : ℝ) + 1) (a * signalScale A D γ s ε n)
    ((jitterScale A D γ s ε n ^ (1 - gap)) ^ v) w (jitterScale A D γ s ε n)
    hCF hCC hB hb.1 (hb.1.trans_le hb.2.1).le (by positivity) hb.2.2.2.1.le hb.2.2.2.2.1 hw
  apply he.trans_eq
  simp only [singletonMass, collisionMass, relaxedGhostMass, coarseScale, carrierScale,
    jitterScale, signalScale, Real.rpow_natCast, mul_pow]
  ring

theorem relaxedGhostMass_tendsto_of_budget (A D γ s ε : ℝ)
    (hA : 0 < A) (hD : 0 < D) (hγ : 0 < γ) (hs : 0 < s) (hε : 0 < ε)
    (b : PowerBudget D (jitterExponent A D γ s ε) (rateMargin D γ s ε)) :
    Tendsto (fun n : ℕ => relaxedGhostMass A D γ s ε b.volumeExponent b.taperGap ((n : ℝ) + 1))
      atTop (𝓝 0) := by
  have he := b.ghost_tendsto (rateMargin_pos D γ s ε hD hγ hs hε) 0
  simp only [Real.rpow_zero, mul_one] at he
  apply he.congr'
  filter_upwards [] with n
  rw [relaxedGhostMass_eq A D γ s ε _ _ _ (by positivity) hA.ne' hD.ne' hγ.ne' hs.ne'
    (rateDenominator_pos D γ s hD hγ hs).ne']

theorem tendsto_zero_of_propensityScalarCost_bound (D : ℕ) (A γ s ε a CF CC B CG : ℝ)
    (hA : 0 < A) (hD : 0 < (D : ℝ)) (hγ : 0 < γ) (hs : 0 < s)
    (hreg : A * (2 + (D : ℝ) / γ) < D) (hε : 0 < ε)
    (hεsmall : ε < γ / D - rateExponent A D γ s)
    (hCF : 0 ≤ CF) (hCC : 0 ≤ CC) (hB : 0 ≤ B)
    (b : PowerBudget D (jitterExponent A D γ s ε) (rateMargin D γ s ε))
    (w f : ℕ → ℝ)
    (hw : ∀ᶠ n in atTop, w n ≤ jitterScale A D γ s ε n ^ D)
    (hf0 : ∀ᶠ n in atTop, 0 ≤ f n)
    (hf : ∀ᶠ n in atTop, f n ≤
      propensityScalarCost D CF CC B CG (roughScale A D γ s ε n)
        (carrierScale A D ε n) (coarseScale A D γ s ε n) ((n : ℝ) + 1)
        (a * signalScale A D γ s ε n)
        ((jitterScale A D γ s ε n ^ (1 - b.taperGap)) ^ b.volumeExponent) (w n)) :
    Tendsto f atTop (𝓝 0) := by
  let C1 := CF * (5 ^ D * B * 10 ^ D) + CC * (B * (2 * D * (2 : ℝ) ^ (D - 1) * 7 ^ D))
  let C2 := CF * CG
  let C3 := CC * (B ^ 2 * 10 ^ D * 4 ^ D)
  have hl := global_rate_ledgers A D γ s ε 0 hA hD hγ hs hε
  simp only [Real.rpow_zero, mul_one] at hl
  have hg := relaxedGhostMass_tendsto_of_budget A D γ s ε hA hD hγ hs hε b
  have hlim := (((hl.1.const_mul C1).add (hg.const_mul C2)).add (hl.2.1.const_mul C3)).const_mul (a ^ 2)
  simp only [mul_zero, add_zero] at hlim
  apply squeeze_zero' hf0 _ hlim
  filter_upwards [hf, hw] with n hn hwn
  exact hn.trans (propensityScalarCost_le_rates D A γ s ε a CF CC B CG b.volumeExponent b.taperGap
    hA hD hγ hs hreg hε hεsmall hCF hCC hB n (w n) hwn)

end CausalLowerbound.PartC
