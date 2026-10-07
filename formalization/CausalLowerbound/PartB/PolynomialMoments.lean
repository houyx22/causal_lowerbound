import CausalLowerbound.PartB.PartBAnalyticComplete
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval

/-! Extension of the complete finite moment vector to every multivariate
polynomial of the prescribed total degree, including the constant term. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace CausalLowerbound

theorem FiniteLaw.expect_finset_sum {Ω I : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (S : Finset I) (f : I → Ω → ℝ) :
    μ.expect (fun ω => ∑ i ∈ S, f i ω) = ∑ i ∈ S, μ.expect (f i) := by
  simp only [FiniteLaw.expect, Finset.mul_sum]
  exact Finset.sum_comm

namespace PartB.ShellGeometry
variable {A Ω Γ Ξ : Type*} [Fintype A] [DecidableEq A]
  [Fintype Ω] [Fintype Γ] [Fintype Ξ]

theorem momentExponent_complete (D : ℕ) (η : A →₀ ℕ) (hη : η ≠ 0)
    (hD : (∑ a, η a) ≤ D) :
    ∃ e : MomentExponent A D, ∀ a, (e.val a).val = η a := by
  have hp : 0 < ∑ a, η a := by
    by_contra h
    apply hη
    apply Finsupp.ext
    intro a
    have ha := Finset.single_le_sum (fun b _ => Nat.zero_le (η b)) (Finset.mem_univ a)
    simp only [Finsupp.zero_apply]
    omega
  let e : A → Fin (D + 1) := fun a => ⟨η a, Nat.lt_succ_of_le
    ((Finset.single_le_sum (fun b _ => Nat.zero_le (η b)) (Finset.mem_univ a)).trans hD)⟩
  exact ⟨⟨e, hp, hD⟩, fun _ => rfl⟩

theorem polynomial_support_degree_le (D : ℕ) (p : MvPolynomial A ℝ)
    (hp : p.totalDegree ≤ D) (η : A →₀ ℕ) (hη : η ∈ p.support) :
    (∑ a, η a) ≤ D := by
  have h := (MvPolynomial.le_totalDegree hη).trans hp
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h
  exact h

theorem expect_polynomial_expansion (μ : FiniteLaw Ω) (U : Ω → A → ℝ)
    (p : MvPolynomial A ℝ) :
    μ.expect (fun ω => MvPolynomial.eval (U ω) p) =
      ∑ η ∈ p.support, p.coeff η * μ.expect (fun ω => ∏ a, U ω a ^ η a) := by
  simp_rw [MvPolynomial.eval_eq']
  rw [μ.expect_finset_sum]
  simp only [μ.expect_mul]

theorem polynomial_moment_interpolation (D : ℕ) (χ : ℝ)
    (μ : FiniteLaw Ω) (ν : FiniteLaw Γ) (σ : FiniteLaw Ξ)
    (U : Ω → A → ℝ) (V : Γ → A → ℝ) (W : Ξ → A → ℝ)
    (hm : ∀ e : MomentExponent A D,
      ν.expect (monomialFeature V e) - μ.expect (monomialFeature U e) =
        χ * (σ.expect (monomialFeature W e) - μ.expect (monomialFeature U e)))
    (p : MvPolynomial A ℝ) (hp : p.totalDegree ≤ D) :
    ν.expect (fun z => MvPolynomial.eval (V z) p) -
      μ.expect (fun z => MvPolynomial.eval (U z) p) =
    χ * (σ.expect (fun z => MvPolynomial.eval (W z) p) -
      μ.expect (fun z => MvPolynomial.eval (U z) p)) := by
  simp only [expect_polynomial_expansion, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro η hη
  by_cases hz : η = 0
  · simp [hz]
  · obtain ⟨e, he⟩ := momentExponent_complete D η hz (polynomial_support_degree_le D p hp η hη)
    have hh := hm e
    change ν.expect (fun ω => ∏ a, V ω a ^ (e.val a).val) -
      μ.expect (fun ω => ∏ a, U ω a ^ (e.val a).val) =
      χ * (σ.expect (fun ω => ∏ a, W ω a ^ (e.val a).val) -
        μ.expect (fun ω => ∏ a, U ω a ^ (e.val a).val)) at hh
    simp_rw [he] at hh
    linear_combination p.coeff η * hh

end PartB.ShellGeometry
end CausalLowerbound
