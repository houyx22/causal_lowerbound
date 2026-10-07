import CausalLowerbound.PartB.FiniteRademacher
import CausalLowerbound.PartB.CubicBridge
import Mathlib.Tactic.IntervalCases

/-! The two design-weighted single-site bridges of Part C. All increments
are explicit polynomial coefficients; exact Taylor identities connect
them to actual likelihood cells without a differentiation API. -/
noncomputable section
set_option autoImplicit false
namespace CausalLowerbound.PartC
variable {Ω : Type*} [Fintype Ω]

theorem expect_quadratic_centered (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (hmean : μ.expect X = 0) (a b c : ℝ) :
    μ.expect (fun ω => a * X ω ^ 2 + b * X ω + c) =
      a * μ.expect (fun ω => X ω ^ 2) + c := by
  rw [μ.expect_add, μ.expect_add, μ.expect_mul, μ.expect_mul, μ.expect_const, hmean]
  ring

theorem expect_quartic_centered (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (hmean : μ.expect X = 0) (hthird : μ.expect (fun ω => X ω ^ 3) = 0)
    (a b c d e : ℝ) :
    μ.expect (fun ω => a + b * X ω + c * X ω ^ 2 + d * X ω ^ 3 + e * X ω ^ 4) =
      a + c * μ.expect (fun ω => X ω ^ 2) + e * μ.expect (fun ω => X ω ^ 4) := by
  simp only [μ.expect_add, μ.expect_mul, μ.expect_const, hmean, hthird]
  ring

namespace RoughPropensity

def likelihood (R T ja ζ Λ : ℝ) : ℝ := (1 + R * ja * Λ) * (1 + T * ζ)
def realField (R T ja δ Λ : ℝ) : ℝ := δ * ja * Λ * T + δ * R * T
def increment (R T ja jb Λ : ℝ) : ℝ := jb * T * (1 + R * ja * Λ)
def substitution (f : ℕ) (ja v Λ : ℝ) : ℝ := if f = 0 then Λ else ja ^ 2 * v ^ 2

theorem actual_Q (R T ja ζ Λ : ℝ) :
    PartB.codedLikelihood R T (ja * Λ) ζ 0 = likelihood R T ja ζ Λ := by
  unfold PartB.codedLikelihood likelihood
  ring

theorem actual_P (R T ja ζ δ Λ : ℝ) :
    PartB.codedLikelihood R T (ja * Λ) (ζ - δ) δ =
      likelihood R T ja ζ Λ + realField R T ja δ Λ := by
  unfold PartB.codedLikelihood likelihood realField
  ring

theorem exact_shift (R T ja jb ζ Λ : ℝ) :
    likelihood R T ja (ζ + jb * Λ) Λ - likelihood R T ja ζ Λ =
      Λ * increment R T ja jb Λ := by
  unfold likelihood increment
  ring

theorem design_weighted_bridge (μ : FiniteLaw Ω) (X : Ω → ℝ) (R T ja jb v : ℝ)
    (hmean : μ.expect X = 0) (hvar : μ.expect (fun ω => X ω ^ 2) = v)
    (f : ℕ) (hf : f ≤ 1) :
    μ.expect (fun ω => substitution f ja v (X ω) * increment R T ja jb (X ω)) =
      μ.expect (fun ω => X ω ^ f * realField R T ja (ja * jb * v) (X ω)) := by
  interval_cases f
  · calc
      _ = μ.expect (fun ω => (ja * jb * R * T) * X ω ^ 2 + (jb * T) * X ω + 0) := by
        apply μ.expect_congr
        intro ω
        simp [substitution, increment] <;> ring
      _ = ja * jb * R * T * v := by rw [expect_quadratic_centered μ X hmean, hvar]; ring
      _ = μ.expect (fun ω => 0 * X ω ^ 2 + (ja * jb * v * ja * T) * X ω + ja * jb * v * R * T) := by
        rw [expect_quadratic_centered μ X hmean]
        ring
      _ = _ := by apply μ.expect_congr; intro ω; unfold realField; ring
  · calc
      _ = μ.expect (fun ω => 0 * X ω ^ 2 + (ja ^ 3 * v ^ 2 * jb * T * R) * X ω + ja ^ 2 * v ^ 2 * jb * T) := by
        apply μ.expect_congr
        intro ω
        norm_num only [substitution, increment, Nat.one_ne_zero, if_false]
        ring
      _ = ja ^ 2 * v ^ 2 * jb * T := by rw [expect_quadratic_centered μ X hmean]; ring
      _ = μ.expect (fun ω => (ja * jb * v * ja * T) * X ω ^ 2 + (ja * jb * v * R * T) * X ω + 0) := by
        rw [expect_quadratic_centered μ X hmean, hvar]
        ring
      _ = _ := by apply μ.expect_congr; intro ω; unfold realField; ring

end RoughPropensity

namespace RoughOutcome

def outcome (jb η ζ Λ : ℝ) : ℝ := jb * Λ * (1 + η - ζ ^ 2)
def likelihood (R T jb η ζ Λ : ℝ) : ℝ := (1 + R * ζ) * (1 + T * outcome jb η ζ Λ)
def realField (R T ζ δ : ℝ) : ℝ := -2 * δ * ζ * T + δ * (1 - 3 * ζ ^ 2) * R * T
def incrementOne (R T ja jb η ζ Λ : ℝ) : ℝ :=
  ja * (R + R * T * jb * Λ * (1 + η) - 2 * T * jb * Λ * ζ - 3 * R * T * jb * Λ * ζ ^ 2)
def incrementTwo (R T ja jb ζ Λ : ℝ) : ℝ := -ja ^ 2 * T * jb * Λ * (1 + 3 * R * ζ)
def incrementThree (R T ja jb Λ : ℝ) : ℝ := -ja ^ 3 * R * T * jb * Λ
def totalIncrement (R T ja jb η ζ Λ : ℝ) : ℝ :=
  Λ * incrementOne R T ja jb η ζ Λ + Λ ^ 2 * incrementTwo R T ja jb ζ Λ +
    Λ ^ 3 * incrementThree R T ja jb Λ

def substitution (e f : ℕ) (μ : FiniteLaw Ω) (X : Ω → ℝ) (Λ : ℝ) : ℝ :=
  μ.expect (fun ω => X ω ^ f) * Λ ^ e

theorem actual_Q (R T jb η ζ Λ : ℝ) :
    PartB.codedLikelihood R T ζ (outcome jb η ζ Λ) 0 = likelihood R T jb η ζ Λ := by
  unfold PartB.codedLikelihood likelihood
  ring

theorem actual_P (R T jb η ζ δ Λ : ℝ) :
    PartB.codedLikelihood R T ζ (outcome jb η ζ Λ - δ * (1 + 3 * ζ)) δ =
      likelihood R T jb η ζ Λ + realField R T ζ δ := by
  unfold PartB.codedLikelihood likelihood realField
  ring

theorem exact_shift (R T ja jb η ζ Λ : ℝ) :
    likelihood R T jb η (ζ + ja * Λ) Λ - likelihood R T jb η ζ Λ =
      totalIncrement R T ja jb η ζ Λ := by
  unfold likelihood outcome totalIncrement incrementOne incrementTwo incrementThree
  ring

theorem mean_increment (μ : FiniteLaw Ω) (X : Ω → ℝ) (R T ja jb η ζ v : ℝ)
    (hmean : μ.expect X = 0) (hvar : μ.expect (fun ω => X ω ^ 2) = v)
    (hthird : μ.expect (fun ω => X ω ^ 3) = 0)
    (hcorrection : (ja * jb * v) * η = ja ^ 3 * jb * μ.expect (fun ω => X ω ^ 4)) :
    μ.expect (fun ω => totalIncrement R T ja jb η ζ (X ω)) =
      realField R T ζ (ja * jb * v) := by
  calc
    _ = μ.expect (fun ω => 0 + (ja * R) * X ω +
        (ja * jb * T * (R * (1 + η) - 2 * ζ - 3 * R * ζ ^ 2)) * X ω ^ 2 +
        (-ja ^ 2 * jb * T * (1 + 3 * R * ζ)) * X ω ^ 3 +
        (-ja ^ 3 * jb * R * T) * X ω ^ 4) := by
      apply μ.expect_congr
      intro ω
      unfold totalIncrement incrementOne incrementTwo incrementThree
      ring
    _ = realField R T ζ (ja * jb * v) + R * T *
        ((ja * jb * v) * η - ja ^ 3 * jb * μ.expect (fun ω => X ω ^ 4)) := by
      rw [expect_quartic_centered μ X hmean hthird, hvar]
      unfold realField
      ring
    _ = _ := by rw [hcorrection]; ring

/-- All design exponents are allowed in this identity; the carrier only
needs `f ≤ 3`. Its three increments still have site degree at most three. -/
theorem design_weighted_bridge (μ : FiniteLaw Ω) (X : Ω → ℝ) (R T ja jb η ζ v : ℝ)
    (hmean : μ.expect X = 0) (hvar : μ.expect (fun ω => X ω ^ 2) = v)
    (hthird : μ.expect (fun ω => X ω ^ 3) = 0)
    (hcorrection : (ja * jb * v) * η = ja ^ 3 * jb * μ.expect (fun ω => X ω ^ 4)) (f : ℕ) :
    μ.expect (fun ω =>
      substitution 1 f μ X (X ω) * incrementOne R T ja jb η ζ (X ω) +
      substitution 2 f μ X (X ω) * incrementTwo R T ja jb ζ (X ω) +
      substitution 3 f μ X (X ω) * incrementThree R T ja jb (X ω)) =
      μ.expect (fun ω => X ω ^ f * realField R T ζ (ja * jb * v)) := by
  calc
    _ = μ.expect (fun ω => μ.expect (fun ω => X ω ^ f) * totalIncrement R T ja jb η ζ (X ω)) := by
      apply μ.expect_congr
      intro ω
      unfold substitution totalIncrement
      ring
    _ = μ.expect (fun ω => X ω ^ f) * realField R T ζ (ja * jb * v) := by
      rw [μ.expect_mul, mean_increment μ X R T ja jb η ζ v hmean hvar hthird hcorrection]
    _ = _ := (μ.expect_mul_const _ _).symm

end RoughOutcome
end CausalLowerbound.PartC
