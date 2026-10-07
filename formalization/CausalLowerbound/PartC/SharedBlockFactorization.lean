import CausalLowerbound.PartC.SharedSignFactorization
import CausalLowerbound.FiniteGrouping

/-! Exact factorization of the full label/sign/coefficient prior. The
locality premise concerns the conditional component value; a component
with no observations is constant even if its unused kernels read signs. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB
variable {K C J Ω : Type*} [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
  [Fintype J] [DecidableEq J] [Fintype Ω]

def signComponentValue (owner : K → C) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω)
    (f : (a : C) → (J → Bool) → ({k // owner k = a} → ℕ) → ({k // owner k = a} → Ω) → ℝ)
    (a : C) (ζ : J → Bool) (labels : {k // owner k = a} → ℕ) : ℝ :=
  (FiniteLaw.independent (fun k : {k // owner k = a} => kernel k.val ζ (labels k))).expect
    (f a ζ labels)

theorem signComponentValue_bound (owner : K → C) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω)
    (f : (a : C) → (J → Bool) → ({k // owner k = a} → ℕ) → ({k // owner k = a} → Ω) → ℝ)
    (a : C) (ζ : J → Bool) (labels : {k // owner k = a} → ℕ) (B : ℝ)
    (hb : ∀ u, |f a ζ labels u| ≤ B) : |signComponentValue owner kernel f a ζ labels| ≤ B :=
  FiniteLaw.abs_expect_le_bound _ _ B hb

theorem signComponentValue_local_congr (owner : K → C)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω)
    (f : (a : C) → (J → Bool) → ({k // owner k = a} → ℕ) → ({k // owner k = a} → Ω) → ℝ)
    (a : C) (ζ ζ' : J → Bool) (labels : {k // owner k = a} → ℕ)
    (hk : ∀ k : {k // owner k = a}, kernel k.val ζ (labels k) = kernel k.val ζ' (labels k))
    (hf : ∀ u, f a ζ labels u = f a ζ' labels u) :
    signComponentValue owner kernel f a ζ labels = signComponentValue owner kernel f a ζ' labels := by
  unfold signComponentValue
  rw [show (fun k : {k // owner k = a} => kernel k.val ζ (labels k)) =
    (fun k : {k // owner k = a} => kernel k.val ζ' (labels k)) from funext hk]
  exact FiniteLaw.expect_congr _ hf

theorem signComponentValue_eq_one (owner : K → C)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω)
    (f : (a : C) → (J → Bool) → ({k // owner k = a} → ℕ) → ({k // owner k = a} → Ω) → ℝ)
    (a : C) (ζ : J → Bool) (labels : {k // owner k = a} → ℕ)
    (hf : ∀ u, f a ζ labels u = 1) : signComponentValue owner kernel f a ζ labels = 1 := by
  unfold signComponentValue
  rw [show f a ζ labels = (fun _ => 1) from funext hf, FiniteLaw.expect_const]

theorem signBlockPrior_component_factorization (H : K → DiscreteLaw ℕ)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (owner : K → C)
    (T : C → Finset J) (hT : ∀ a b, a ≠ b → Disjoint (T a) (T b))
    (f : (a : C) → (J → Bool) → ({k // owner k = a} → ℕ) → ({k // owner k = a} → Ω) → ℝ)
    (B : C → ℝ) (hb : ∀ a ζ labels u, |f a ζ labels u| ≤ B a)
    (hlocal : ∀ a ζ ζ' labels, (∀ j ∈ T a, ζ j = ζ' j) →
      signComponentValue owner kernel f a ζ labels = signComponentValue owner kernel f a ζ' labels) :
    (signBlockPrior H kernel).expect (fun z =>
      ∏ a, f a z.1.2 (fun k => z.1.1 k.val) (fun k => z.2 k.val)) =
      ∏ a, independentSigns.expect (fun ζ =>
        (DiscreteLaw.independent (fun k : {k // owner k = a} => H k.val)).expect
          (signComponentValue owner kernel f a ζ)) := by
  have hprod (z : ((K → ℕ) × (J → Bool)) × (K → Ω)) :
      |∏ a, f a z.1.2 (fun k => z.1.1 k.val) (fun k => z.2 k.val)| ≤ ∏ a, B a := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun a _ => hb a z.1.2 _ _)
  rw [signBlockPrior_expect H kernel _ (∏ a, B a) hprod]
  have he (z : (K → ℕ) × (J → Bool)) :
      (signBlockKernel kernel z).expect (fun u =>
        ∏ a, f a z.2 (fun k => z.1 k.val) (fun k => u k.val)) =
      ∏ a, signComponentValue owner kernel f a z.2 (fun k => z.1 k.val) :=
    FiniteLaw.expect_independent_component_prod (fun k => kernel k z.2 (z.1 k)) owner
      (fun a => f a z.2 (fun k => z.1 k.val))
  simp_rw [he]
  exact sharedSignPrior_component_factorization H owner T hT (signComponentValue owner kernel f) B
    (fun a ζ labels => signComponentValue_bound owner kernel f a ζ labels (B a) (hb a ζ labels)) hlocal

end CausalLowerbound.PartC
