import CausalLowerbound.DiscreteProbability
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Exact positive tilting of countable probability laws. The construction
is a genuine probability measure and retains every label in the carrier. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal Classical
open MeasureTheory
namespace CausalLowerbound.DiscreteLaw
variable {Ω Γ : Type*}

@[ext] theorem ext {μ ν : DiscreteLaw Ω} (h : ∀ x, μ.weight x = ν.weight x) : μ = ν := by
  cases μ
  cases ν
  congr
  funext x
  exact h x

theorem expect_bounds (μ : DiscreteLaw Ω) (w : Ω → ℝ) (lo hi : ℝ)
    (hlo : 0 ≤ lo) (hw : ∀ x, lo ≤ w x ∧ w x ≤ hi) :
    lo ≤ μ.expect w ∧ μ.expect w ≤ hi := by
  have hs := μ.summable_expect_of_bounded w hi (fun x => by
    rw [abs_of_nonneg (hlo.trans (hw x).1)]; exact (hw x).2)
  constructor
  · have hh := hasSum_le (fun x => mul_le_mul_of_nonneg_left (hw x).1 (μ.nonneg x))
      (μ.total.mul_right lo) hs.hasSum
    simpa only [one_mul, expect] using hh
  · have hh := hasSum_le (fun x => mul_le_mul_of_nonneg_left (hw x).2 (μ.nonneg x))
      hs.hasSum (μ.total.mul_right hi)
    simpa only [one_mul, expect] using hh

def tilt (μ : DiscreteLaw Ω) (w : Ω → ℝ) (lo hi : ℝ) (hlo : 0 < lo)
    (hw : ∀ x, lo ≤ w x ∧ w x ≤ hi) : DiscreteLaw Ω where
  weight x := μ.weight x * w x / μ.expect w
  nonneg x := div_nonneg (mul_nonneg (μ.nonneg x) (hlo.le.trans (hw x).1))
    (hlo.le.trans (μ.expect_bounds w lo hi hlo.le hw).1)
  total := by
    have hs := μ.summable_expect_of_bounded w hi (fun x => by
      rw [abs_of_nonneg (hlo.le.trans (hw x).1)]; exact (hw x).2)
    have he : 0 < μ.expect w := hlo.trans_le (μ.expect_bounds w lo hi hlo.le hw).1
    have ht : HasSum (fun x => μ.weight x * w x / μ.expect w) (μ.expect w / μ.expect w) :=
      hs.hasSum.div_const (μ.expect w)
    simpa only [div_self he.ne'] using ht

theorem tilt_expect (μ : DiscreteLaw Ω) (w : Ω → ℝ) (lo hi : ℝ) (hlo : 0 < lo)
    (hw : ∀ x, lo ≤ w x ∧ w x ≤ hi) (f : Ω → ℝ) :
    (μ.tilt w lo hi hlo hw).expect f = (μ.expect w)⁻¹ * μ.expect (fun x => w x * f x) := by
  unfold expect
  rw [← tsum_mul_left]
  apply tsum_congr
  intro x
  simp only [tilt, expect]
  ring

variable [Fintype Γ]

theorem joint_expect_label (μ : DiscreteLaw Ω) (kernel : Ω → FiniteLaw Γ)
    (f : Ω → ℝ) (B : ℝ) (hf : ∀ x, |f x| ≤ B) :
    (μ.joint kernel).expect (fun z => f z.1) = μ.expect f := by
  rw [μ.expect_joint kernel _ B (fun z => hf z.1)]
  simp only [FiniteLaw.expect_const]

theorem tilt_joint (μ : DiscreteLaw Ω) (kernel : Ω → FiniteLaw Γ)
    (w : Ω → ℝ) (lo hi : ℝ) (hlo : 0 < lo) (hw : ∀ x, lo ≤ w x ∧ w x ≤ hi) :
    (μ.joint kernel).tilt (fun z => w z.1) lo hi hlo (fun z => hw z.1) =
      (μ.tilt w lo hi hlo hw).joint kernel := by
  have he := μ.joint_expect_label kernel w hi (fun x => by
    rw [abs_of_nonneg (hlo.le.trans (hw x).1)]; exact (hw x).2)
  ext z
  change μ.weight z.1 * (kernel z.1).weight z.2 * w z.1 /
    (μ.joint kernel).expect (fun z => w z.1) =
      (μ.weight z.1 * w z.1 / μ.expect w) * (kernel z.1).weight z.2
  rw [he]
  ring

theorem joint_toPMF_label (μ : DiscreteLaw Ω) (kernel : Ω → FiniteLaw Γ) :
    (μ.joint kernel).toPMF.map Prod.fst = μ.toPMF := by
  apply PMF.ext
  intro x
  rw [PMF.map_apply, ENNReal.tsum_prod']
  simp only [toPMF_apply, joint]
  have he (a : Ω) : (∑' b : Γ, if x = a then ENNReal.ofReal (μ.weight a * (kernel a).weight b) else 0) =
      if x = a then ENNReal.ofReal (μ.weight a) else 0 := by
    split_ifs
    · rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun b _ => mul_nonneg (μ.nonneg a) ((kernel a).nonneg b)),
        ← Finset.mul_sum, FiniteLaw.total, mul_one]
    · simp
  simp only [he]
  exact (tsum_eq_single x (f := fun a => if x = a then ENNReal.ofReal (μ.weight a) else 0)
    (fun a ha => if_neg (Ne.symm ha))).trans (if_pos rfl)

theorem joint_measure_label [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : DiscreteLaw Ω) (kernel : Ω → FiniteLaw Γ) :
    (μ.joint kernel).toMeasure.map Prod.fst = μ.toMeasure := by
  rw [toMeasure, PMF.toMeasure_map _ _ measurable_fst, joint_toPMF_label]
  rfl

theorem tilted_common_label [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : DiscreteLaw Ω) (P Q : Ω → FiniteLaw Γ)
    (w : Ω → ℝ) (lo hi : ℝ) (hlo : 0 < lo) (hw : ∀ x, lo ≤ w x ∧ w x ≤ hi) :
    ((μ.joint P).tilt (fun z => w z.1) lo hi hlo (fun z => hw z.1)).toMeasure.map Prod.fst =
      ((μ.joint Q).tilt (fun z => w z.1) lo hi hlo (fun z => hw z.1)).toMeasure.map Prod.fst := by
  rw [tilt_joint, tilt_joint, joint_measure_label, joint_measure_label]

theorem tilt_measure_withDensity [Countable Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : DiscreteLaw Ω) (w : Ω → ℝ) (lo hi : ℝ) (hlo : 0 < lo)
    (hw : ∀ x, lo ≤ w x ∧ w x ≤ hi) :
    (μ.tilt w lo hi hlo hw).toMeasure =
      μ.toMeasure.withDensity (fun x => ENNReal.ofReal (w x / μ.expect w)) := by
  apply Measure.ext_of_singleton
  intro x
  rw [withDensity_apply _ (measurableSet_singleton x), lintegral_singleton]
  simp only [toMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), toPMF_apply]
  change ENNReal.ofReal (μ.weight x * w x / μ.expect w) = _
  rw [← ENNReal.ofReal_mul (div_nonneg (hlo.le.trans (hw x).1)
    (hlo.le.trans (μ.expect_bounds w lo hi hlo.le hw).1))]
  congr 1
  ring

theorem tilt_likelihood_cancellation (μ : DiscreteLaw Ω) (Z : Ω → ℝ) (n : ℕ)
    (lo hi : ℝ) (hlo : 0 < lo) (hZ : ∀ x, lo ≤ Z x ∧ Z x ≤ hi)
    (F : Ω → Fin n → ℝ) (L : Ω → ℝ) :
    (μ.tilt (fun z => Z z ^ n) (lo ^ n) (hi ^ n) (pow_pos hlo n)
      (fun z => ⟨pow_le_pow_left₀ hlo.le (hZ z).1 n,
        pow_le_pow_left₀ (hlo.le.trans (hZ z).1) (hZ z).2 n⟩)).expect
        (fun z => (∏ i, F z i / Z z) * L z) =
      (μ.expect (fun z => Z z ^ n))⁻¹ * μ.expect (fun z => (∏ i, F z i) * L z) := by
  rw [tilt_expect]
  congr 1
  congr 1
  funext z
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hz : Z z ≠ 0 := (hlo.trans_le (hZ z).1).ne'
  field_simp

section Mixture
variable {X : Type*} [MeasurableSpace X]

def mixMeasures (μ : DiscreteLaw Ω) (K : Ω → Measure X) : Measure X :=
  Measure.sum (fun a => ENNReal.ofReal (μ.weight a) • K a)

instance mixMeasures_probability (μ : DiscreteLaw Ω) (K : Ω → Measure X)
    [∀ a, IsProbabilityMeasure (K a)] : IsProbabilityMeasure (μ.mixMeasures K) := by
  constructor
  rw [mixMeasures, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg μ.nonneg μ.summable_weight, μ.tsum_weight, ENNReal.ofReal_one]

theorem mixMeasures_joint (μ : DiscreteLaw Ω) (kernel : Ω → FiniteLaw Γ) (K : Ω → Measure X) :
    (μ.joint kernel).mixMeasures (fun z => K z.1) = μ.mixMeasures K := by
  ext s hs
  simp only [mixMeasures, Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro a
  rw [tsum_fintype]
  simp only [Prod.fst]
  rw [← Finset.sum_mul]
  congr 1
  simp only [joint]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ => mul_nonneg (μ.nonneg a) ((kernel a).nonneg b)),
    ← Finset.mul_sum, FiniteLaw.total, mul_one]

theorem tilted_common_mixture (μ : DiscreteLaw Ω) (P Q : Ω → FiniteLaw Γ)
    (w : Ω → ℝ) (lo hi : ℝ) (hlo : 0 < lo) (hw : ∀ x, lo ≤ w x ∧ w x ≤ hi)
    (K : Ω → Measure X) :
    ((μ.joint P).tilt (fun z => w z.1) lo hi hlo (fun z => hw z.1)).mixMeasures (fun z => K z.1) =
      ((μ.joint Q).tilt (fun z => w z.1) lo hi hlo (fun z => hw z.1)).mixMeasures (fun z => K z.1) := by
  rw [tilt_joint, tilt_joint, mixMeasures_joint, mixMeasures_joint]
end Mixture

end CausalLowerbound.DiscreteLaw
