import CausalLowerbound.PartB.RateRegime

/-! The actual global error monomials, not only their formal exponents,
vanish after multiplication by any fixed logarithmic power. -/
noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology
namespace CausalLowerbound.PartB

def singletonMass (A d γ ε x : ℝ) : ℝ :=
  x * (x ^ (-((rateExponent A d γ + ε) / γ))) ^ d *
    (x ^ (-jitterExponent A d γ ε)) ^ d * (x ^ (-(rateExponent A d γ + ε))) ^ (2 : ℕ)
def collisionMass (A d γ ε x : ℝ) : ℝ :=
  x ^ (2 : ℕ) * (x ^ (-((rateExponent A d γ + ε) / γ))) ^ d *
    (x ^ (-jitterExponent A d γ ε) * x ^ (-carrierExponent A d ε)) ^ d *
      (x ^ (-(rateExponent A d γ + ε))) ^ (2 : ℕ)
def highComponentMass (A d γ ε x : ℝ) : ℝ :=
  let Q := matchingOrder d γ (rateExponent A d γ + ε) (d * ε / (2 * A))
  x ^ (Q + 1) * (x ^ (-((rateExponent A d γ + ε) / γ))) ^ d *
    (x ^ (-carrierExponent A d ε)) ^ (d * Q)

theorem singletonMass_eq (A d γ ε x : ℝ) (hx : 0 < x)
    (hA : A ≠ 0) (hd : d ≠ 0) (hγ : γ ≠ 0) (hD : rateDenominator d γ ≠ 0) :
    singletonMass A d γ ε x = x ^ (-ε * (rateDenominator d γ - d / 2) / 2) := by
  unfold singletonMass
  rw [← Real.rpow_natCast (n := 2)]
  simp only [← Real.rpow_mul hx.le]
  calc
    _ = x ^ (1 - (rateExponent A d γ + ε) * d / γ - d * jitterExponent A d γ ε -
        2 * (rateExponent A d γ + ε)) := by
      conv_lhs => arg 1; arg 1; arg 1; rw [← Real.rpow_one x]
      rw [← Real.rpow_add hx, ← Real.rpow_add hx, ← Real.rpow_add hx]
      congr 1
      push_cast
      ring
    _ = _ := by rw [(rate_exponent_ledgers A d γ ε hA hd hγ hD).1]

theorem collisionMass_eq (A d γ ε x : ℝ) (hx : 0 < x)
    (hA : A ≠ 0) (hd : d ≠ 0) (hγ : γ ≠ 0) (hD : rateDenominator d γ ≠ 0) :
    collisionMass A d γ ε x =
      x ^ (-ε * (rateDenominator d γ - d / 2) / 2 - d * ε / (2 * A)) := by
  unfold collisionMass
  rw [← Real.rpow_add hx, ← Real.rpow_natCast (n := 2), ← Real.rpow_natCast (n := 2)]
  simp only [← Real.rpow_mul hx.le]
  rw [← Real.rpow_add hx, ← Real.rpow_add hx, ← Real.rpow_add hx]
  congr 1
  have h := (rate_exponent_ledgers A d γ ε hA hd hγ hD).2
  convert h using 1 <;> push_cast <;> ring

theorem highComponentMass_eq (A d γ ε x : ℝ) (hx : 0 < x) (hA : A ≠ 0) (hd : d ≠ 0) :
    highComponentMass A d γ ε x = x ^ (1 - (rateExponent A d γ + ε) * d / γ -
      (d * ε / (2 * A)) * matchingOrder d γ (rateExponent A d γ + ε) (d * ε / (2 * A))) := by
  unfold highComponentMass
  dsimp only
  rw [← Real.rpow_natCast]
  simp only [← Real.rpow_mul hx.le]
  rw [← Real.rpow_add hx, ← Real.rpow_add hx]
  congr 1
  have hξ : d * carrierExponent A d ε = 1 + d * ε / (2 * A) := by
    dsimp [carrierExponent]
    field_simp
    ring
  push_cast
  linear_combination -(matchingOrder d γ (rateExponent A d γ + ε) (d * ε / (2 * A)) : ℝ) * hξ

theorem global_rate_ledgers (A d γ ε B : ℝ) (hA : 0 < A) (hd : 0 < d)
    (hγ : 0 < γ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => singletonMass A d γ ε (n + 1) * logScale (n + 1) ^ B) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => collisionMass A d γ ε (n + 1) * logScale (n + 1) ^ B) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => highComponentMass A d γ ε (n + 1) * logScale (n + 1) ^ B) atTop (𝓝 0) := by
  have hD := (rateDenominator_pos d γ hd hγ).ne'
  have hl := rate_ledger_exponents_negative A d γ ε hA hd hγ hε
  have hh := matchingOrder_exponent_neg d γ (rateExponent A d γ + ε)
    (d * ε / (2 * A)) (by positivity)
  have ht (e : ℝ) (he : e < 0) :
      Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ e * logScale (n + 1) ^ B) atTop (𝓝 0) := by
    simpa only [neg_neg, Nat.cast_add, Nat.cast_one] using polynomial_log_tendsto (-e) B (neg_pos.mpr he)
  constructor
  · apply (ht _ hl.1).congr'
    filter_upwards [] with n
    rw [singletonMass_eq A d γ ε _ (by positivity) hA.ne' hd.ne' hγ.ne' hD]
  constructor
  · apply (ht _ hl.2).congr'
    filter_upwards [] with n
    rw [collisionMass_eq A d γ ε _ (by positivity) hA.ne' hd.ne' hγ.ne' hD]
  · apply (ht _ hh).congr'
    filter_upwards [] with n
    rw [highComponentMass_eq A d γ ε _ (by positivity) hA.ne' hd.ne']

end CausalLowerbound.PartB
