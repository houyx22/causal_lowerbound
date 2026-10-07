import CausalLowerbound.PartB.OutcomePackets

/-! Uniform legality of both complete parameter fields. All constants are
derived from the actual packet profiles and are independent of the draw. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped ContDiff
namespace CausalLowerbound

structure Regularity where
  order : ℕ
  fraction : ℝ
  nonneg : 0 ≤ fraction
  le_one : fraction ≤ 1

def Regularity.exponent (s : Regularity) : ℝ := s.order + s.fraction
theorem Regularity.exponent_nonneg (s : Regularity) : 0 ≤ s.exponent :=
  add_nonneg (Nat.cast_nonneg _) s.nonneg

structure NuisanceFields (d : Type*) where
  propensity : (d → ℝ) → ℝ
  baseline : (d → ℝ) → ℝ
  effect : (d → ℝ) → ℝ

def NuisanceFields.Legal {d : Type*} [Fintype d] (F : NuisanceFields d)
    (α β γ : Regularity) (Lπ L₀ Lτ κ : ℝ) : Prop :=
  HolderControl α.order α.fraction Lπ F.propensity ∧
  HolderControl β.order β.fraction L₀ F.baseline ∧
  HolderControl γ.order γ.fraction Lτ F.effect ∧
  ∀ x, κ ≤ F.propensity x ∧ F.propensity x ≤ 1 - κ ∧
    κ ≤ F.baseline x ∧ F.baseline x ≤ 1 - κ ∧
    κ ≤ F.baseline x + F.effect x ∧ F.baseline x + F.effect x ≤ 1 - κ

namespace PartB.ShellGeometry
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [Fintype Ω]

def codedOutcome {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h a b t δ : ℝ) (x : d → ℝ) : ℝ :=
  if side then b * normalizedCubic S U x₀ r h a t x -
    targetField x₀ h δ x * (1 + 2 * propensityPerturbation S U x₀ r h a x)
  else b * normalizedCubic S U x₀ r h a t x

def modelFields {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h a b t δ : ℝ) : NuisanceFields d where
  propensity x := (1 + propensityPerturbation S U x₀ r h a x) / 2
  baseline x := (1 + codedOutcome side S U x₀ r h a b t δ x) / 2
  effect x := if side then targetField x₀ h δ x else 0

theorem target_lower_regularity (s : Regularity) (γ : ℝ) (hγ : s.exponent ≤ γ) :
    ∃ C > 0, ∀ (x₀ : d → ℝ) (h c : ℝ), 0 < h → h ≤ 1 → 0 ≤ c →
      HolderControl s.order s.fraction (C * c) (targetField x₀ h (c * h ^ γ)) := by
  obtain ⟨C, hC, hb⟩ := targetField_holder (d := d) s.order s.fraction s.nonneg s.le_one
  refine ⟨C, hC, ?_⟩
  intro x₀ h c hh hh1 hc
  apply (hb x₀ h (c * h ^ γ) hh hh1).mono
  have hp : h ^ (γ - s.exponent) ≤ 1 := Real.rpow_le_one hh.le hh1 (sub_nonneg.mpr hγ)
  calc
    _ = C * c * h ^ (γ - s.exponent) := by
      rw [abs_of_nonneg (mul_nonneg hc (Real.rpow_nonneg hh.le _)), sub_eq_add_neg, Real.rpow_add hh]
      simp only [Regularity.exponent]
      ring
    _ ≤ C * c := mul_le_of_le_one_right (mul_nonneg hC.le hc) hp

theorem outcome_uniform_holder {Q : ℕ} (U : Ω → CoefficientExponent d Q → ℝ)
    (α β γ : Regularity) (hβγ : β.exponent ≤ γ.exponent) :
    ∃ C > 0, ∀ (side : Bool) (S : Finset (d → ℤ)) (sample : (d → ℤ) → Ω)
      (x₀ : d → ℝ) (r h t ca cb : ℝ), 0 < r → r ≤ h → h ≤ 1 →
      0 ≤ t → t ≤ 1 → 0 ≤ ca → ca ≤ 1 → 0 ≤ cb →
      h ^ γ.exponent = r ^ (α.exponent + β.exponent) * t ^ 2 →
      HolderControl β.order β.fraction (C * cb)
        (codedOutcome side S (fun k => U (sample k)) x₀ r h
          (ca * r ^ α.exponent) (cb * r ^ β.exponent) t (ca * cb * h ^ γ.exponent)) := by
  obtain ⟨A, hA, ha⟩ := outcomePacket_scale_control U (β.order + 1)
  obtain ⟨B, hB, hb⟩ := target_lower_regularity (d := d) β γ.exponent hβγ
  refine ⟨2 * A + B, by positivity, ?_⟩
  intro side S sample x₀ r h t ca cb hr hrh hh1 ht ht1 hca hca1 hcb hbal
  have hh := hr.trans_le hrh
  have hr1 := hrh.trans hh1
  have ha0 : 0 ≤ ca * r ^ α.exponent := mul_nonneg hca (Real.rpow_nonneg hr.le _)
  have ha1 : ca * r ^ α.exponent ≤ 1 :=
    (mul_le_of_le_one_right hca (Real.rpow_le_one hr.le hr1 α.exponent_nonneg)).trans hca1
  have hs := ha S sample x₀ r h (ca * r ^ α.exponent) t hr hrh ha0 ha1 ht ht1
  have hQ := hs.1.amplitude_holder β.nonneg β.le_one hr hr1 cb hcb
  have hP := hs.2.amplitude_holder β.nonneg β.le_one hr hr1 cb hcb
  have hd := hb x₀ h (ca * cb) hh hh1 (mul_nonneg hca hcb)
  have hds : ContDiff ℝ ∞ (targetField x₀ h (ca * cb * h ^ γ.exponent)) :=
    contDiff_const.mul ((rescaled_smooth _ quadraticPartition_smooth x₀ h).pow 2)
  have he : ca * cb * h ^ γ.exponent =
      (ca * r ^ α.exponent) * (cb * r ^ β.exponent) * t ^ 2 := by
    rw [hbal, Real.rpow_add hr]; ring
  cases side with
  | false =>
    simpa only [codedOutcome, Bool.false_eq_true, if_false] using
      hQ.mono (by nlinarith [mul_nonneg hB.le hcb])
  | true =>
    have hdneg := hd.const_smul hds (-1)
    have hadd := hP.add hdneg (contDiff_const.mul hs.2.smooth) (contDiff_const.smul hds)
    have hc : 2 * A * cb + |(-1 : ℝ)| * (B * (ca * cb)) ≤ (2 * A + B) * cb := by
      rw [abs_neg, abs_one]
      nlinarith [mul_nonneg hB.le hcb, mul_le_mul_of_nonneg_right hca1 (mul_nonneg hB.le hcb)]
    have hh' := hadd.mono hc
    have heq : codedOutcome true S (fun k => U (sample k)) x₀ r h
        (ca * r ^ α.exponent) (cb * r ^ β.exponent) t (ca * cb * h ^ γ.exponent) =
        fun x => (cb * r ^ β.exponent) * normalizedPOutcome S (fun k => U (sample k)) x₀ r h
          (ca * r ^ α.exponent) t x + (-1 : ℝ) • targetField x₀ h (ca * cb * h ^ γ.exponent) x := by
      funext x
      simp only [codedOutcome, if_true, smul_eq_mul, neg_one_mul, ← sub_eq_add_neg]
      exact (normalizedPOutcome_eq _ _ _ _ _ _ _ _ _ he x).symm
    rwa [heq]

theorem exists_legal_amplitudes {Q : ℕ} (U : Ω → CoefficientExponent d Q → ℝ)
    (α β γ : Regularity) (hβγ : β.exponent ≤ γ.exponent)
    (Lπ L₀ Lτ κ : ℝ) (hLπ : 1 / 2 < Lπ) (hL₀ : 1 / 2 < L₀) (hLτ : 0 < Lτ)
    (hκ : κ < 1 / 4) :
    ∃ ε > 0, ε ≤ 1 ∧ ∀ (ca cb : ℝ), 0 ≤ ca → ca ≤ ε → 0 ≤ cb → cb ≤ ε →
      ∀ (side : Bool) (S : Finset (d → ℤ)) (sample : (d → ℤ) → Ω)
        (x₀ : d → ℝ) (r h t : ℝ), 0 < r → r ≤ h → h ≤ 1 → 0 ≤ t → t ≤ 1 →
        h ^ γ.exponent = r ^ (α.exponent + β.exponent) * t ^ 2 →
        (modelFields side S (fun k => U (sample k)) x₀ r h
          (ca * r ^ α.exponent) (cb * r ^ β.exponent) t (ca * cb * h ^ γ.exponent)).Legal
          α β γ Lπ L₀ Lτ κ := by
  obtain ⟨A, hA, ha⟩ := propensityPerturbation_holder U α.order α.fraction α.nonneg α.le_one
  obtain ⟨B, hB, hb⟩ := outcome_uniform_holder U α β γ hβγ
  obtain ⟨D, hD, hd⟩ := balanced_target_holder (d := d) γ.order γ.fraction γ.nonneg γ.le_one
  let ε := min (1 / 8) (min ((Lπ - 1 / 2) / A)
    (min ((L₀ - 1 / 2) / B) (min (Lτ / D) (min (1 / (4 * A)) (1 / (4 * B))))))
  have hπpos : 0 < Lπ - 1 / 2 := sub_pos.mpr hLπ
  have h₀pos : 0 < L₀ - 1 / 2 := sub_pos.mpr hL₀
  have hepos : 0 < ε := by dsimp [ε]; positivity
  have he8 : ε ≤ 1 / 8 := min_le_left _ _
  have heA : ε * A ≤ Lπ - 1 / 2 := by
    apply (le_div_iff₀ hA).mp
    exact (min_le_right _ _).trans (min_le_left _ _)
  have heB : ε * B ≤ L₀ - 1 / 2 := by
    apply (le_div_iff₀ hB).mp
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have heD : ε * D ≤ Lτ := by
    apply (le_div_iff₀ hD).mp
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have heAs : ε * A ≤ 1 / 4 := by
    have he' : ε ≤ 1 / (4 * A) := (min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    have := (le_div_iff₀ (show 0 < 4 * A by positivity)).mp he'
    linarith
  have heBs : ε * B ≤ 1 / 4 := by
    have he' : ε ≤ 1 / (4 * B) := (min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    have := (le_div_iff₀ (show 0 < 4 * B by positivity)).mp he'
    linarith
  refine ⟨ε, hepos, by linarith, ?_⟩
  intro ca cb hca hcaε hcb hcbε side S sample x₀ r h t hr hrh hh1 ht ht1 hbal
  have hca1 : ca ≤ 1 := by linarith
  have hcb1 : cb ≤ 1 := by linarith
  have hh := hr.trans_le hrh
  have hp := ha S sample x₀ r h ca hr hrh (hrh.trans hh1) hca
  have hy := hb side S sample x₀ r h t ca cb hr hrh hh1 ht ht1 hca hca1 hcb hbal
  have hτ := hd x₀ h (ca * cb) hh hh1 (mul_nonneg hca hcb)
  have hpSmooth : ContDiff ℝ ∞ (propensityPerturbation S (fun k => U (sample k)) x₀ r h (ca * r ^ α.exponent)) :=
    contDiff_const.mul (packetField_smooth _ _ _ _ _)
  have hySmooth : ContDiff ℝ ∞ (codedOutcome side S (fun k => U (sample k)) x₀ r h
      (ca * r ^ α.exponent) (cb * r ^ β.exponent) t (ca * cb * h ^ γ.exponent)) := by
    have hG : ContDiff ℝ ∞ (fun x => coarseBump x₀ h x ^ 2) :=
      (rescaled_smooth _ quadraticPartition_smooth _ _).pow 2
    have hη : ContDiff ℝ ∞ (packetEta S x₀ r h (ca * r ^ α.exponent) t) :=
      contDiff_const.mul (hG.mul (contDiff_const.sub (contDiff_const.mul (quarticField_smooth _ _ _))))
    have hP := packetField_smooth S (fun k => U (sample k)) x₀ r h
    have hK : ContDiff ℝ ∞ (normalizedCubic S (fun k => U (sample k)) x₀ r h (ca * r ^ α.exponent) t) :=
      ((contDiff_const.add hη).mul hP).sub (contDiff_const.mul (hP.pow 3))
    unfold codedOutcome
    split
    · exact (contDiff_const.mul hK).sub ((contDiff_const.mul hG).mul
        (contDiff_const.add (contDiff_const.mul hpSmooth)))
    · exact contDiff_const.mul hK
  have hpC : ca * A ≤ 1 / 4 := (mul_le_mul_of_nonneg_right hcaε hA.le).trans heAs
  have hyC : B * cb ≤ 1 / 4 := by nlinarith [mul_le_mul_of_nonneg_right hcbε hB.le]
  refine ⟨(hp.half_shift hpSmooth).mono (by nlinarith [mul_le_mul_of_nonneg_right hcaε hA.le]),
    (hy.half_shift hySmooth).mono (by nlinarith [mul_le_mul_of_nonneg_right hcbε hB.le]), ?_, ?_⟩
  · cases side with
    | false => exact (HolderControl.const _ _ 0).mono (by simpa using hLτ.le)
    | true =>
      apply hτ.mono
      have hacb : ca * cb ≤ ε := (mul_le_of_le_one_right hca hcb1).trans hcaε
      nlinarith [mul_le_mul_of_nonneg_right hacb hD.le]
  · intro x
    have hpv : |propensityPerturbation S (fun k => U (sample k)) x₀ r h (ca * r ^ α.exponent) x| ≤ 1 / 4 :=
      (hp.value_bound x).trans hpC
    have hyv : |codedOutcome side S (fun k => U (sample k)) x₀ r h
        (ca * r ^ α.exponent) (cb * r ^ β.exponent) t (ca * cb * h ^ γ.exponent) x| ≤ 1 / 4 :=
      (hy.value_bound x).trans hyC
    have htv : |targetField x₀ h (ca * cb * h ^ γ.exponent) x| ≤ 1 / 8 := by
      apply (targetField_abs_le _ _ _ _).trans
      rw [abs_of_nonneg (by positivity)]
      calc
        _ ≤ ca * cb := mul_le_of_le_one_right (mul_nonneg hca hcb)
          (Real.rpow_le_one hh.le hh1 γ.exponent_nonneg)
        _ ≤ ca := mul_le_of_le_one_right hca hcb1
        _ ≤ 1 / 8 := hcaε.trans he8
    have hpp := abs_le.mp hpv
    have hyp := abs_le.mp hyv
    have htp := abs_le.mp htv
    change κ ≤ (1 + _) / 2 ∧ _
    dsimp only [modelFields]
    cases side <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
      constructor <;> (try constructor) <;> (try constructor) <;>
      (try constructor) <;> (try constructor) <;> linarith

theorem modelFields_separation {Q : ℕ} (S : Finset (d → ℤ))
    (UP UQ : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h a b t δ : ℝ) :
    (modelFields true S UP x₀ r h a b t δ).effect x₀ -
      (modelFields false S UQ x₀ r h a b t δ).effect x₀ = δ := by
  simp [modelFields, targetField_center]
end PartB.ShellGeometry
end CausalLowerbound
