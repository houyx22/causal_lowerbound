import CausalLowerbound.PartB.NuisanceLegality

/-! A common legality interface for the two mixed constructions. The small
amplitude is chosen from fixed analytic constants, before any scale or draw. -/
noncomputable section
set_option autoImplicit false
open scoped ContDiff
namespace CausalLowerbound.PartC
variable {d : Type*} [Fintype d]

def codedFields (side : Bool) (p y target : (d → ℝ) → ℝ) : NuisanceFields d where
  propensity x := (1 + p x) / 2
  baseline x := (1 + y x) / 2
  effect x := if side then target x else 0

theorem codedFields_smooth (side : Bool) (p y target : (d → ℝ) → ℝ)
    (hp : ContDiff ℝ ∞ p) (hy : ContDiff ℝ ∞ y) (ht : ContDiff ℝ ∞ target) :
    ContDiff ℝ ∞ (codedFields side p y target).propensity ∧
      ContDiff ℝ ∞ (codedFields side p y target).baseline ∧
      ContDiff ℝ ∞ (codedFields side p y target).effect := by
  refine ⟨(contDiff_const.add hp).div_const 2, (contDiff_const.add hy).div_const 2, ?_⟩
  cases side with
  | false => exact contDiff_const
  | true => exact ht

theorem codedFields_legal (side : Bool) (p y target : (d → ℝ) → ℝ)
    (α β γ : Regularity) (A B D Lπ L₀ Lτ κ : ℝ)
    (hp : HolderControl α.order α.fraction A p)
    (hy : HolderControl β.order β.fraction B y)
    (ht : HolderControl γ.order γ.fraction D target)
    (hps : ContDiff ℝ ∞ p) (hys : ContDiff ℝ ∞ y)
    (hπ : 1 / 2 + A / 2 ≤ Lπ) (hyL : 1 / 2 + B / 2 ≤ L₀)
    (htL : D ≤ Lτ) (hLτ : 0 ≤ Lτ) (hA : A ≤ 1 / 4) (hB : B ≤ 1 / 4)
    (htv : ∀ x, |target x| ≤ 1 / 8) (hκ : κ < 1 / 4) :
    (codedFields side p y target).Legal α β γ Lπ L₀ Lτ κ := by
  refine ⟨(hp.half_shift hps).mono hπ, (hy.half_shift hys).mono hyL, ?_, ?_⟩
  · cases side with
    | false => exact (HolderControl.const _ _ 0).mono (by simpa using hLτ)
    | true => exact ht.mono htL
  · intro x
    have hpx := abs_le.mp ((hp.value_bound x).trans hA)
    have hyx := abs_le.mp ((hy.value_bound x).trans hB)
    have htx := abs_le.mp (htv x)
    dsimp only [codedFields]
    cases side <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
      constructor <;> (try constructor) <;> (try constructor) <;>
      (try constructor) <;> (try constructor) <;> linarith

theorem exists_coded_amplitude (A B D Lπ L₀ Lτ : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hD : 0 < D)
    (hLπ : 1 / 2 < Lπ) (hL₀ : 1 / 2 < L₀) (hLτ : 0 < Lτ) :
    ∃ ε > 0, ε ≤ 1 ∧ ∀ c : ℝ, 0 ≤ c → c ≤ ε →
      1 / 2 + (A * c) / 2 ≤ Lπ ∧ 1 / 2 + (B * c) / 2 ≤ L₀ ∧
      D * (c * c) ≤ Lτ ∧ A * c ≤ 1 / 4 ∧ B * c ≤ 1 / 4 ∧ c * c ≤ 1 / 8 := by
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
  refine ⟨ε, hepos, by linarith, fun c hc hce => ?_⟩
  have hc1 : c ≤ 1 := by linarith
  have hcc : c * c ≤ ε := (mul_le_of_le_one_right hc hc1).trans hce
  have hcA := mul_le_mul_of_nonneg_right hce hA.le
  have hcB := mul_le_mul_of_nonneg_right hce hB.le
  have hcD := mul_le_mul_of_nonneg_right hcc hD.le
  refine ⟨by nlinarith [mul_nonneg hA.le hc], by nlinarith [mul_nonneg hB.le hc],
    by nlinarith, by nlinarith, by nlinarith, hcc.trans he8⟩

end CausalLowerbound.PartC
