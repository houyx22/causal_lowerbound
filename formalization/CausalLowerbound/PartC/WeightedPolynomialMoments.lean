import CausalLowerbound.PartC.CoefficientShiftPolynomial
import CausalLowerbound.PartB.PolynomialMoments
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! Extending density-weighted moment identities to every coefficient
polynomial of the prescribed degree. The target is any genuine linear
functional that annihilates constants; summation over labels is retained. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB.ShellGeometry MvPolynomial
variable {A Ω : Type*} [Fintype A] [DecidableEq A] [Fintype Ω]

def momentPolynomial {D : ℕ} (η : MomentExponent A D) : MvPolynomial A ℝ :=
  ∏ k : MomentPositions η, X k.1

theorem momentPolynomial_eval {D : ℕ} (η : MomentExponent A D) (U : A → ℝ) :
    eval U (momentPolynomial η) = ∏ a, U a ^ (η.val a).val := by
  simp [momentPolynomial, MomentPositions, Fintype.prod_sigma]

theorem momentPolynomial_eq_monomial {D : ℕ} (η : MomentExponent A D) (e : A →₀ ℕ)
    (he : ∀ a, (η.val a).val = e a) : momentPolynomial η = MvPolynomial.monomial e 1 := by
  apply MvPolynomial.funext
  intro z
  rw [momentPolynomial_eval, eval_monomial, one_mul,
    Finsupp.prod_fintype e (fun a n => z a ^ n) (fun a => pow_zero (z a))]
  simp only [he]

theorem polynomial_linear_expansion (L : MvPolynomial A ℝ →ₗ[ℝ] ℝ) (p : MvPolynomial A ℝ) :
    L p = ∑ e ∈ p.support, p.coeff e * L (MvPolynomial.monomial e 1) := by
  calc
    _ = L (∑ e ∈ p.support, MvPolynomial.monomial e (p.coeff e)) := congrArg L p.as_sum
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro e _
      rw [show MvPolynomial.monomial e (p.coeff e) = p.coeff e • MvPolynomial.monomial e 1 by
        simp only [MvPolynomial.smul_eq_C_mul, C_mul_monomial, mul_one], map_smul, smul_eq_mul]

theorem weighted_polynomial_moment_hasSum (D : ℕ) (μ : FiniteLaw Ω)
    (kernel : ℕ → FiniteLaw Ω) (U : Ω → A → ℝ) (weight density : ℕ → ℝ)
    (L : MvPolynomial A ℝ →ₗ[ℝ] ℝ) (hC : ∀ c : ℝ, L (C c) = 0)
    (hm : ∀ η : MomentExponent A D,
      HasSum (fun n => (weight n *
        ((kernel n).expect (monomialFeature U η) - μ.expect (monomialFeature U η))) * density n)
        (L (momentPolynomial η)))
    (p : MvPolynomial A ℝ) (hp : p.totalDegree ≤ D) :
    HasSum (fun n => (weight n *
      ((kernel n).expect (fun ω => eval (U ω) p) - μ.expect (fun ω => eval (U ω) p))) * density n) (L p) := by
  have hmono (e : A →₀ ℕ) (he : e ∈ p.support) :
      HasSum (fun n => (weight n *
        ((kernel n).expect (fun ω => ∏ a, U ω a ^ e a) -
          μ.expect (fun ω => ∏ a, U ω a ^ e a))) * density n)
        (L (MvPolynomial.monomial e 1)) := by
    by_cases hz : e = 0
    · subst e
      simp only [Finsupp.zero_apply, pow_zero, Finset.prod_const_one, FiniteLaw.expect_const,
        sub_self, mul_zero, zero_mul, MvPolynomial.monomial_zero', hC]
      exact hasSum_zero
    · obtain ⟨η, hη⟩ := momentExponent_complete D e hz (polynomial_support_degree_le D p hp e he)
      have hh := hm η
      rw [momentPolynomial_eq_monomial η e hη] at hh
      change HasSum (fun n => (weight n *
        ((kernel n).expect (fun ω => ∏ a, U ω a ^ (η.val a).val) -
          μ.expect (fun ω => ∏ a, U ω a ^ (η.val a).val))) * density n)
        (L (MvPolynomial.monomial e 1)) at hh
      simpa only [monomialFeature, hη] using hh
  have hs := hasSum_sum (s := p.support) (fun e he => (hmono e he).mul_left (p.coeff e))
  have he (n : ℕ) : (∑ e ∈ p.support, p.coeff e * ((weight n *
      ((kernel n).expect (fun ω => ∏ a, U ω a ^ e a) -
        μ.expect (fun ω => ∏ a, U ω a ^ e a))) * density n)) =
      (weight n * ((kernel n).expect (fun ω => eval (U ω) p) -
        μ.expect (fun ω => eval (U ω) p))) * density n := by
    simp only [expect_polynomial_expansion, ← Finset.sum_sub_distrib,
      Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _
    ring
  simpa only [he, ← polynomial_linear_expansion L p] using hs

end CausalLowerbound.PartC
