import CausalLowerbound.DiscreteGrouping
import CausalLowerbound.DiscreteMixture
import CausalLowerbound.PartC.SharedSignPriors
import CausalLowerbound.PartC.LocalSignResampling

/-! Exact component factorization for countable labels and shared rough
signs. Sign independence is derived from disjoint symbol supports. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.DiscreteLaw

theorem expect_finite_comm {A B : Type*} [Fintype B] (μ : DiscreteLaw A) (ν : FiniteLaw B)
    (f : A → B → ℝ) (M : ℝ) (hf : ∀ a b, |f a b| ≤ M) :
    μ.expect (fun a => ν.expect (f a)) = ν.expect (fun b => μ.expect (fun a => f a b)) := by
  simp only [FiniteLaw.expect]
  rw [μ.expect_fintype_sum (fun b a => ν.weight b * f a b) (fun b => ν.weight b * M)
    (fun b a => by
      rw [abs_mul, abs_of_nonneg (ν.nonneg b)]
      exact mul_le_mul_of_nonneg_left (hf a b) (ν.nonneg b))]
  simp only [expect_const_mul]

end CausalLowerbound.DiscreteLaw

namespace CausalLowerbound.PartC
open PartB
variable {K C J : Type*} [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
  [Fintype J] [DecidableEq J]

theorem independentSigns_expect_prod_local (T : C → Finset J)
    (hT : ∀ a b, a ≠ b → Disjoint (T a) (T b)) (f : C → (J → Bool) → ℝ)
    (hf : ∀ a ζ ζ', (∀ j ∈ T a, ζ j = ζ' j) → f a ζ = f a ζ') :
    independentSigns.expect (fun ζ => ∏ a, f a ζ) = ∏ a, independentSigns.expect (f a) := by
  have he := disjoint_sign_resampling T hT f (fun _ x => ∏ a, x a) hf (fun _ _ _ _ => rfl)
  simpa only [FiniteLaw.expect_independent_prod, FiniteLaw.expect_const] using he

theorem sharedSignPrior_component_factorization (H : K → DiscreteLaw ℕ) (owner : K → C)
    (T : C → Finset J) (hT : ∀ a b, a ≠ b → Disjoint (T a) (T b))
    (f : (a : C) → (J → Bool) → ({k // owner k = a} → ℕ) → ℝ)
    (B : C → ℝ) (hb : ∀ a ζ labels, |f a ζ labels| ≤ B a)
    (hf : ∀ a ζ ζ' labels, (∀ j ∈ T a, ζ j = ζ' j) → f a ζ labels = f a ζ' labels) :
    (sharedSignPrior H).expect (fun z => ∏ a, f a z.2 (fun k => z.1 k.val)) =
      ∏ a, independentSigns.expect (fun ζ =>
        (DiscreteLaw.independent (fun k : {k // owner k = a} => H k.val)).expect (f a ζ)) := by
  have hprod (labels : K → ℕ) (ζ : J → Bool) :
      |∏ a, f a ζ (fun k => labels k.val)| ≤ ∏ a, B a := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun a _ => hb a ζ _)
  rw [sharedSignPrior_expect H _ (∏ a, B a) (fun z => hprod z.1 z.2),
    DiscreteLaw.expect_finite_comm _ independentSigns _ (∏ a, B a) hprod]
  have hgroup (ζ : J → Bool) := DiscreteLaw.expect_independent_component_prod H owner
    (fun a => f a ζ) B (fun a => hb a ζ)
  simp_rw [hgroup]
  apply independentSigns_expect_prod_local T hT
  intro a ζ ζ' he
  unfold DiscreteLaw.expect
  apply tsum_congr
  intro labels
  rw [hf a ζ ζ' labels he]

end CausalLowerbound.PartC
