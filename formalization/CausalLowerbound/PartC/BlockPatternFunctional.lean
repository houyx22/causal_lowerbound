import CausalLowerbound.PartC.BlockPolynomialFunctional

/-! The product of block site-pattern functionals is one square-free
functional on the combined block/slot variables. This lets an affine
observation choose its perturbation block before the pattern is evaluated. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial
variable {K V : Type*} [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]

def blockSiteSet (S : Finset (K × V)) (k : K) : Finset V :=
  Finset.univ.filter (fun v => (k, v) ∈ S)

@[simp] theorem mem_blockSiteSet (S : Finset (K × V)) (k : K) (v : V) :
    v ∈ blockSiteSet S k ↔ (k, v) ∈ S := by simp [blockSiteSet]

theorem blockExponent_support (m : (K × V) →₀ ℕ) (k : K) :
    (blockExponent m k).support = blockSiteSet m.support k := by
  ext v
  simp only [Finsupp.mem_support_iff, blockExponent_apply, mem_blockSiteSet]

theorem block_site_pattern_product (w : K → Finset V → ℝ) (m : (K × V) →₀ ℕ) :
    (∏ k, sitePatternFunctional (w k) (blockMonomial m k)) =
      if ∀ v, m v ≤ 1 then ∏ k, w k (blockSiteSet m.support k) else 0 := by
  simp only [blockMonomial, sitePatternFunctional_monomial, one_mul,
    blockExponent_apply, blockExponent_support]
  by_cases hm : ∀ v, m v ≤ 1
  · simp only [if_pos hm, show ∀ k v, m (k, v) ≤ 1 from fun k v => hm (k, v),
      implies_true, if_true]
  · rw [if_neg hm]
    obtain ⟨⟨k, v⟩, hv⟩ := not_forall.mp hm
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    have hk : ¬ ∀ v, m (k, v) ≤ 1 := fun h => hv (h v)
    rw [if_neg hk]

theorem blockPolynomialFunctional_site_patterns (w : K → Finset V → ℝ)
    (p : MvPolynomial (K × V) ℝ) :
    blockPolynomialFunctional (fun k => sitePatternFunctional (w k)) p =
      sitePatternFunctional (fun S => ∏ k, w k (blockSiteSet S k)) p := by
  rw [blockPolynomialFunctional_expansion]
  change (∑ m ∈ p.support, p.coeff m * ∏ k, sitePatternFunctional (w k) (blockMonomial m k)) =
    ∑ m ∈ p.support, p.coeff m * (if ∀ v, m v ≤ 1 then ∏ k, w k (blockSiteSet m.support k) else 0)
  simp_rw [block_site_pattern_product]

theorem sitePatternFunctional_block_product (w : K → Finset V → ℝ)
    (p : K → MvPolynomial V ℝ) :
    sitePatternFunctional (fun S => ∏ k, w k (blockSiteSet S k))
      (∏ k, rename (fun v => (k, v)) (p k)) = ∏ k, sitePatternFunctional (w k) (p k) := by
  rw [← blockPolynomialFunctional_site_patterns, blockPolynomialFunctional_separated_product]

end CausalLowerbound.PartC
