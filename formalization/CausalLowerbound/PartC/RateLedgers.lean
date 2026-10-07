import CausalLowerbound.PartC.RateRegime

/-! Actual mixed-smoothness error monomials and their limits. All constants
and the matching order are chosen before taking `n` to infinity. -/
noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology
namespace CausalLowerbound.PartC

def singletonMass (A d γ s ε x : ℝ) : ℝ :=
  x * (x ^ (-((rateExponent A d γ s + ε) / γ))) ^ d *
    (x ^ (-jitterExponent A d γ s ε)) ^ d * (x ^ (-(rateExponent A d γ s + ε))) ^ (2 : ℕ)

def collisionMass (A d γ s ε x : ℝ) : ℝ :=
  x ^ (2 : ℕ) * (x ^ (-((rateExponent A d γ s + ε) / γ))) ^ d *
    (x ^ (-jitterExponent A d γ s ε) * x ^ (-carrierExponent A d ε)) ^ d *
      (x ^ (-(rateExponent A d γ s + ε))) ^ (2 : ℕ)

def matchingOrder (A d γ s ε : ℝ) : ℕ :=
  PartB.matchingOrder d γ (rateExponent A d γ s + ε) (d * ε / (2 * A))

def highComponentMass (A d γ s ε x : ℝ) : ℝ :=
  x ^ (matchingOrder A d γ s ε + 1) *
    (x ^ (-((rateExponent A d γ s + ε) / γ))) ^ d *
    (x ^ (-carrierExponent A d ε)) ^ (d * matchingOrder A d γ s ε)

theorem singletonMass_eq (A d γ s ε x : ℝ) (hx : 0 < x)
    (hA : A ≠ 0) (hd : d ≠ 0) (hγ : γ ≠ 0) (hs : s ≠ 0)
    (hD : rateDenominator d γ s ≠ 0) :
    singletonMass A d γ s ε x = x ^ (-rateMargin d γ s ε) := by
  unfold singletonMass
  rw [← Real.rpow_natCast (n := 2)]
  simp only [← Real.rpow_mul hx.le]
  calc
    _ = x ^ (1 - (rateExponent A d γ s + ε) * d / γ -
        d * jitterExponent A d γ s ε - 2 * (rateExponent A d γ s + ε)) := by
      conv_lhs => arg 1; arg 1; arg 1; rw [← Real.rpow_one x]
      rw [← Real.rpow_add hx, ← Real.rpow_add hx, ← Real.rpow_add hx]
      congr 1
      push_cast
      ring
    _ = _ := by rw [(rate_exponent_ledgers A d γ s ε hA hd hγ hs hD).1]

theorem collisionMass_eq (A d γ s ε x : ℝ) (hx : 0 < x)
    (hA : A ≠ 0) (hd : d ≠ 0) (hγ : γ ≠ 0) (hs : s ≠ 0)
    (hD : rateDenominator d γ s ≠ 0) :
    collisionMass A d γ s ε x = x ^ (-rateMargin d γ s ε - d * ε / (2 * A)) := by
  unfold collisionMass
  rw [← Real.rpow_add hx, ← Real.rpow_natCast (n := 2), ← Real.rpow_natCast (n := 2)]
  simp only [← Real.rpow_mul hx.le]
  rw [← Real.rpow_add hx, ← Real.rpow_add hx, ← Real.rpow_add hx]
  congr 1
  have h := (rate_exponent_ledgers A d γ s ε hA hd hγ hs hD).2
  convert h using 1 <;> push_cast <;> ring

theorem highComponentMass_eq (A d γ s ε x : ℝ) (hx : 0 < x)
    (hA : A ≠ 0) (hd : d ≠ 0) :
    highComponentMass A d γ s ε x =
      x ^ (1 - (rateExponent A d γ s + ε) * d / γ -
        (d * ε / (2 * A)) * matchingOrder A d γ s ε) := by
  unfold highComponentMass
  rw [← Real.rpow_natCast]
  simp only [← Real.rpow_mul hx.le]
  rw [← Real.rpow_add hx, ← Real.rpow_add hx]
  congr 1
  have hξ : d * carrierExponent A d ε = 1 + d * ε / (2 * A) := by
    unfold carrierExponent PartB.carrierExponent
    field_simp
    ring
  push_cast
  linear_combination -(matchingOrder A d γ s ε : ℝ) * hξ

theorem matchingOrder_ge_two (A d γ s ε : ℝ) : 2 ≤ matchingOrder A d γ s ε :=
  PartB.matchingOrder_ge_two _ _ _ _

theorem global_rate_ledgers (A d γ s ε B : ℝ) (hA : 0 < A) (hd : 0 < d)
    (hγ : 0 < γ) (hs : 0 < s) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => singletonMass A d γ s ε (n + 1) * PartB.logScale (n + 1) ^ B)
      atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => collisionMass A d γ s ε (n + 1) * PartB.logScale (n + 1) ^ B)
      atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => highComponentMass A d γ s ε (n + 1) * PartB.logScale (n + 1) ^ B)
      atTop (𝓝 0) := by
  have hD := (rateDenominator_pos d γ s hd hγ hs).ne'
  have hl := rate_ledger_exponents_negative A d γ s ε hA hd hγ hs hε
  have hh := PartB.matchingOrder_exponent_neg d γ (rateExponent A d γ s + ε)
    (d * ε / (2 * A)) (by positivity)
  have ht (e : ℝ) (he : e < 0) :
      Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ e * PartB.logScale (n + 1) ^ B) atTop (𝓝 0) := by
    simpa only [neg_neg, Nat.cast_add, Nat.cast_one] using
      PartB.polynomial_log_tendsto (-e) B (neg_pos.mpr he)
  constructor
  · apply (ht _ hl.1).congr'
    filter_upwards [] with n
    rw [singletonMass_eq A d γ s ε _ (by positivity) hA.ne' hd.ne' hγ.ne' hs.ne' hD]
  constructor
  · apply (ht _ hl.2).congr'
    filter_upwards [] with n
    rw [collisionMass_eq A d γ s ε _ (by positivity) hA.ne' hd.ne' hγ.ne' hs.ne' hD]
  · apply (ht _ hh).congr'
    filter_upwards [] with n
    rw [highComponentMass_eq A d γ s ε _ (by positivity) hA.ne' hd.ne']
    rfl

end CausalLowerbound.PartC
