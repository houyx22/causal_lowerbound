import CausalLowerbound.PartB.BlockActivation
import CausalLowerbound.FiniteProductReplacement

/-! Blocks that meet no observation are forced active without changing
any likelihood. Thus the leakage cost is restricted to incident blocks. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace CausalLowerbound.PartB
variable {K : Type*} [Fintype K] [DecidableEq K]

def effectiveActivationWeight (χ : K → ℝ) (relevant : K → Prop) (k : K) : ℝ :=
  if relevant k then χ k else 1

theorem effectiveActivationWeight_bounds (χ : K → ℝ) (relevant : K → Prop)
    (h0 : ∀ k, 0 ≤ χ k) (h1 : ∀ k, χ k ≤ 1) (k : K) :
    0 ≤ effectiveActivationWeight χ relevant k ∧ effectiveActivationWeight χ relevant k ≤ 1 := by
  by_cases hk : relevant k <;> simp [effectiveActivationWeight, hk, h0, h1]

theorem effective_activation_expect (χ : K → ℝ) (relevant : K → Prop)
    (h0 : ∀ k, 0 ≤ χ k) (h1 : ∀ k, χ k ≤ 1) (f : (K → Bool) → ℝ)
    (hignore : ∀ k, ¬relevant k → ∀ active b, f (Function.update active k b) = f active) :
    (activationProduct χ h0 h1).expect f =
      (activationProduct (effectiveActivationWeight χ relevant)
        (fun k => (effectiveActivationWeight_bounds χ relevant h0 h1 k).1)
        (fun k => (effectiveActivationWeight_bounds χ relevant h0 h1 k).2)).expect f := by
  apply FiniteLaw.independent_replace_all
  intro k active
  by_cases hk : relevant k
  · have he : effectiveActivationWeight χ relevant k = χ k := if_pos hk
    simp only [he]
  · simp_rw [hignore k hk, FiniteLaw.expect_const]

theorem effective_activation_sq_error (χ : K → ℝ) (relevant : K → Prop)
    (h0 : ∀ k, 0 ≤ χ k) (h1 : ∀ k, χ k ≤ 1) (f : (K → Bool) → ℝ) (target ε : ℝ)
    (hignore : ∀ k, ¬relevant k → ∀ active b, f (Function.update active k b) = f active)
    (hfull : f (fun _ => true) = target) (herr : ∀ active, |f active - target| ≤ ε) :
    ((activationProduct χ h0 h1).expect f - target) ^ 2 ≤
      ε ^ 2 * ∑ k, if relevant k then 1 - χ k else 0 := by
  rw [effective_activation_expect χ relevant h0 h1 f hignore]
  let χ' := effectiveActivationWeight χ relevant
  have hb (k : K) := effectiveActivationWeight_bounds χ relevant h0 h1 k
  have he := (activationProduct χ' (fun k => (hb k).1) (fun k => (hb k).2)).matched_component_sq_error
    (fun _ => true) f target ε hfull herr
  rw [full_activation_weight] at he
  have hs := one_sub_prod_le_sum χ' (fun k => (hb k).1) (fun k => (hb k).2)
  have hsum : (∑ k, (1 - χ' k)) = ∑ k, if relevant k then 1 - χ k else 0 := by
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : relevant k <;> simp [χ', effectiveActivationWeight, hk]
  rw [hsum] at hs
  exact he.trans (mul_le_mul_of_nonneg_left hs (sq_nonneg ε))

end CausalLowerbound.PartB
