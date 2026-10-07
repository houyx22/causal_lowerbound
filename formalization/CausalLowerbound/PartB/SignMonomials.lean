import CausalLowerbound.PartB.Rademacher
import Mathlib.Algebra.Ring.Parity

/-!
# Exact sign cancellation at every polynomial degree

This supplies the parity step for the ideal moment increment, whose degree can
be as large as 4Q. It is not restricted to the first four moments of a sign sum.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartB

theorem rademacher_power (k : ℕ) :
    rademacher.expect (fun b => sign b ^ k) = if Even k then 1 else 0 := by
  rw [rademacher_expect]
  simp only [sign, one_pow, neg_one_pow_eq_ite]
  split_ifs <;> norm_num

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def independentSigns : FiniteLaw (ι → Bool) :=
  FiniteLaw.independent (fun _ : ι => rademacher)

def signMonomial (ν : ι → ℕ) (ω : ι → Bool) : ℝ := ∏ i, sign (ω i) ^ ν i

def EvenExponents (ν : ι → ℕ) : Prop := ∀ i, Even (ν i)

instance (ν : ι → ℕ) : Decidable (EvenExponents ν) := inferInstanceAs (Decidable (∀ i, Even (ν i)))

theorem expect_signMonomial (ν : ι → ℕ) :
    independentSigns.expect (signMonomial ν) = if EvenExponents ν then 1 else 0 := by
  change (FiniteLaw.independent (fun _ : ι => rademacher)).expect
    (fun ω => ∏ i, sign (ω i) ^ ν i) = _
  rw [FiniteLaw.expect_independent_prod (fun _ : ι => rademacher)
    (fun i b => sign b ^ ν i)]
  simp_rw [rademacher_power]
  by_cases h : EvenExponents ν
  · rw [if_pos h]
    simp only [if_pos (h _), Finset.prod_const_one]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, ¬ Even (ν i) := by simpa [EvenExponents] using h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Every nonconstant term that survives averaging has at least two shifts. -/
theorem evenExponents_degree_ge_two (ν : ι → ℕ) (hν : EvenExponents ν) (hne : ν ≠ 0) :
    2 ≤ ∑ i, ν i := by
  obtain ⟨i, hi⟩ : ∃ i, ν i ≠ 0 := by
    by_contra h
    apply hne
    funext i
    exact not_ne_iff.mp (not_exists.mp h i)
  obtain ⟨k, hk⟩ := hν i
  have hs : ν i ≤ ∑ j, ν j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

theorem surviving_signMonomial_degree (ν : ι → ℕ) (hne : ν ≠ 0)
    (hs : independentSigns.expect (signMonomial ν) ≠ 0) : 2 ≤ ∑ i, ν i := by
  apply evenExponents_degree_ge_two ν _ hne
  by_contra h
  exact hs (by rw [expect_signMonomial, if_neg h])

/-- A finite polynomial in independent signs is averaged exactly by discarding
the monomials with an odd site exponent. -/
theorem expect_signPolynomial (s : Finset (ι → ℕ)) (a : (ι → ℕ) → ℝ) :
    independentSigns.expect (fun ω => ∑ ν ∈ s, a ν * signMonomial ν ω) =
      ∑ ν ∈ s.filter EvenExponents, a ν := by
  simp only [FiniteLaw.expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [mul_left_comm _ (a _), ← Finset.mul_sum]
  change (∑ ν ∈ s, a ν * independentSigns.expect (signMonomial ν)) = _
  simp_rw [expect_signMonomial]
  simp [Finset.sum_filter]

end CausalLowerbound.PartB
