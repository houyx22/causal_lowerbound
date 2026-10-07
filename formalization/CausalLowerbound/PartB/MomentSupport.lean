import CausalLowerbound.PartB.PaperWiener
import Mathlib.LinearAlgebra.Lagrange

/-!
# Concrete finite support for the moment simplex

A tensor grid inside an arbitrarily small coefficient ball replaces the
minimal unisolvent simplex used in the paper. Coefficients of the univariate
Lagrange basis give an explicit moment right inverse. The number of atoms
depends only on the fixed dimension and moment degree, never on n.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators

namespace CausalLowerbound.PartB.ShellGeometry

attribute [local instance] finOrderedDecEq finOrderedDecLt

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- A column of the inverse univariate Vandermonde matrix. -/
def gridDual {D : ℕ} (nodes : Fin (D + 1) → ℝ) (k j : Fin (D + 1)) : ℝ :=
  (Lagrange.basis Finset.univ nodes j).coeff k.val

theorem gridDual_moment {D : ℕ} (nodes : Fin (D + 1) → ℝ)
    (hnodes : Function.Injective nodes) (k l : Fin (D + 1)) :
    (∑ j, gridDual nodes k j * nodes j ^ l.val) = if k = l then 1 else 0 := by
  have hd : (Polynomial.X ^ l.val : Polynomial ℝ).degree <
      (Finset.univ : Finset (Fin (D + 1))).card := by
    simpa only [Polynomial.degree_X_pow, Finset.card_univ, Fintype.card_fin,
      Nat.cast_lt] using l.isLt
  have h := congrArg (fun p : Polynomial ℝ => p.coeff k.val)
    (Lagrange.eq_interpolate hnodes.injOn hd)
  simp only [Lagrange.interpolate_apply, Polynomial.finset_sum_coeff,
    Polynomial.coeff_C_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.coeff_X_pow] at h
  simpa only [gridDual, Fin.ext_iff, mul_comm] using h.symm

abbrev MomentGrid (A : Type*) (D : ℕ) := A → Fin (D + 1)

def tensorGridDual {D : ℕ} (nodes : A → Fin (D + 1) → ℝ)
    (η ω : MomentGrid A D) : ℝ := ∏ a, gridDual (nodes a) (η a) (ω a)

theorem tensorGridDual_moment {D : ℕ} (nodes : A → Fin (D + 1) → ℝ)
    (hnodes : ∀ a, Function.Injective (nodes a)) (η ξ : MomentGrid A D) :
    (∑ ω : MomentGrid A D, tensorGridDual nodes η ω * ∏ a, nodes a (ω a) ^ (ξ a).val) =
      if η = ξ then 1 else 0 := by
  classical
  simp only [tensorGridDual, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun a j => gridDual (nodes a) (η a) j * nodes a j ^ (ξ a).val)]
  simp only [gridDual_moment _ (hnodes _)]
  by_cases h : η = ξ
  · subst ξ
    simp
  · rw [if_neg h]
    obtain ⟨a, ha⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ a) (if_neg ha)

theorem momentExponent_ne_zero {D : ℕ} (η : MomentExponent A D) : η.val ≠ 0 := by
  intro h
  have hp := η.property.1
  simpa only [h, Pi.zero_apply, Fin.val_zero, Finset.sum_const_zero, lt_self_iff_false] using hp

/-- The augmented moment map is inverted explicitly, including the mass row. -/
def gridMomentRightInverse {D : ℕ} (nodes : A → Fin (D + 1) → ℝ)
    (hnodes : ∀ a, Function.Injective (nodes a)) :
    MomentRightInverse (monomialFeature (D := D) (fun (ω : MomentGrid A D) a => nodes a (ω a))) where
  coeff ω η := tensorGridDual nodes η.val ω
  mass η := by
    have h := tensorGridDual_moment nodes hnodes η.val 0
    simpa only [Pi.zero_apply, Fin.val_zero, pow_zero, Finset.prod_const_one, mul_one,
      if_neg (momentExponent_ne_zero η)] using h
  moment η ξ := by
    simpa only [monomialFeature, Subtype.ext_iff] using
      tensorGridDual_moment nodes hnodes η.val ξ.val

/-- Equally spaced nodes with a strict margin inside the chosen interval. -/
def smallGridNode (D : ℕ) (c ρ : ℝ) (j : Fin (D + 1)) : ℝ :=
  c + ρ * (j.val : ℝ) / (D + 1)

theorem smallGridNode_injective (D : ℕ) (c ρ : ℝ) (hρ : 0 < ρ) :
    Function.Injective (smallGridNode D c ρ) := by
  intro i j hij
  apply Fin.ext
  have hd : (D : ℝ) + 1 ≠ 0 := by positivity
  have he := (div_left_inj' hd).mp (add_left_cancel hij)
  exact_mod_cast (mul_left_cancel₀ hρ.ne' he)

theorem smallGridNode_dist_lt (D : ℕ) (c ρ : ℝ) (hρ : 0 < ρ) (j : Fin (D + 1)) :
    |smallGridNode D c ρ j - c| < ρ := by
  have hd : (0 : ℝ) < (D : ℝ) + 1 := by positivity
  have hj : (j.val : ℝ) < (D : ℝ) + 1 := by exact_mod_cast j.isLt
  have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
  simp only [smallGridNode, add_sub_cancel_left]
  rw [abs_of_nonneg (div_nonneg (mul_nonneg hρ.le hj0) hd.le)]
  exact (div_lt_iff₀ hd).mpr (mul_lt_mul_of_pos_left hj hρ)

def smallGrid (D : ℕ) (c : A → ℝ) (ρ : ℝ) (ω : MomentGrid A D) : A → ℝ :=
  fun a => smallGridNode D (c a) ρ (ω a)

theorem smallGrid_mem_ball (D : ℕ) (c : A → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (ω : MomentGrid A D) : smallGrid D c ρ ω ∈ Metric.ball c ρ := by
  rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hρ]
  intro a
  exact smallGridNode_dist_lt D (c a) ρ hρ (ω a)

theorem smallGrid_injective (D : ℕ) (c : A → ℝ) (ρ : ℝ) (hρ : 0 < ρ) :
    Function.Injective (smallGrid D c ρ) := by
  intro ω ω' h
  funext a
  exact smallGridNode_injective D (c a) ρ hρ (congrFun h a)

def smallGridRightInverse (D : ℕ) (c : A → ℝ) (ρ : ℝ) (hρ : 0 < ρ) :
    MomentRightInverse (monomialFeature (D := D) (smallGrid D c ρ)) :=
  gridMomentRightInverse (fun a => smallGridNode D (c a) ρ)
    (fun a => smallGridNode_injective D (c a) ρ hρ)

/-- The baseline law is uniform on the actual finite grid. -/
def gridLaw (D : ℕ) : FiniteLaw (MomentGrid A D) where
  weight _ := (Fintype.card (MomentGrid A D) : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    have hc : (Fintype.card (MomentGrid A D) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hc

theorem gridLaw_weight_pos (D : ℕ) (ω : MomentGrid A D) : 0 < (gridLaw D).weight ω := by
  exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos)

/-- `lem:moment-simplex`, with no supplied support, rank, or right-inverse assumption. -/
theorem moment_simplex_in_ball (D : ℕ) (c : A → ℝ) (ρ : ℝ) (hρ : 0 < ρ) :
    (∀ ω, smallGrid D c ρ ω ∈ Metric.ball c ρ) ∧
    (∀ ω : MomentGrid A D, 0 < (gridLaw D).weight ω) ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ v : MomentExponent A D → ℝ, (∀ i, |v i| ≤ δ) →
      ∃ ν : FiniteLaw (MomentGrid A D), (∀ ω, 0 < ν.weight ω) ∧
        ∀ j, ν.expect (monomialFeature (smallGrid D c ρ) j) =
          (gridLaw D).expect (monomialFeature (smallGrid D c ρ) j) + v j := by
  exact ⟨smallGrid_mem_ball D c ρ hρ, gridLaw_weight_pos D,
    exists_positive_moment_radius _ (smallGridRightInverse D c ρ hρ)
      (gridLaw D) (gridLaw_weight_pos D)⟩

variable {d : Type*} [Fintype d] [DecidableEq d]

def paperCoefficientAtoms (Q : ℕ) (ρ : ℝ) :
    MomentGrid (CoefficientExponent d Q) (4 * Q) → CoefficientExponent d Q → ℝ :=
  smallGrid (4 * Q) 0 ρ

def paperCoefficientLaw (Q : ℕ) : FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q)) :=
  gridLaw (4 * Q)

/-- The positive carrier now has concrete support and probability weights;
the moment right inverse is no longer an input. -/
theorem paper_positiveCarrier_small_support (Q : ℕ) [NeZero Q] (ρ : ℝ) (hρ : 0 < ρ)
    (p B : ℝ) (hp : 0 < p) (hB : ((Q.choose 2 : ℝ) + 2) / 2 < B) :
    (∀ ω, paperCoefficientAtoms (d := d) Q ρ ω ∈ Metric.ball 0 ρ) ∧
    (∀ ω, 0 < (paperCoefficientLaw (d := d) Q).weight ω) ∧
    (∀ᶠ n in Filter.atTop,
      HasPositiveCarrier 1 (PositiveWiener.naturalAtom (d := d) (ι := Fin Q) (1 / 4))
        (multiplicationIncrement
          (paperIdealVector Q (paperCoefficientLaw Q) (paperCoefficientAtoms Q ρ) p B n))
        (monomialFeature (paperCoefficientAtoms Q ρ)) (paperCoefficientLaw Q)) := by
  refine ⟨smallGrid_mem_ball (4 * Q) 0 ρ hρ, gridLaw_weight_pos (4 * Q), ?_⟩
  exact (paper_item_one Q (paperCoefficientLaw Q) (paperCoefficientAtoms Q ρ) p B hp hB
    (gridLaw_weight_pos (4 * Q)) (smallGridRightInverse (4 * Q) 0 ρ hρ)).2.2

end CausalLowerbound.PartB.ShellGeometry
