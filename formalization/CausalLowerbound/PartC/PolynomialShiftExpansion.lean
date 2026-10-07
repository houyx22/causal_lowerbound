import CausalLowerbound.PartB.IdealIncrementExpansion

/-! Polynomial shifts before averaging the rough field. The choice
expansion retains its site labels; its nonconstant terms start at degree
one, as required in the mixed-smoothness construction. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC

open PartB

variable {Ω K V : Type*} [Fintype Ω] [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]

def shiftChoiceWeight (μ : FiniteLaw Ω) (U : Ω → K → ℝ) (s : K → Option V) : ℝ :=
  if s = (fun _ => none) then 0 else μ.expect (fun ω => choiceBase (U ω) s)

theorem shiftChoiceWeight_nonzero_degree (μ : FiniteLaw Ω) (U : Ω → K → ℝ)
    (s : K → Option V) (hs : shiftChoiceWeight μ U s ≠ 0) : 1 ≤ choiceDegree s := by
  have hn : s ≠ (fun _ => none) := by intro h; exact hs (by simp [shiftChoiceWeight, h])
  have hp : choiceDegree s ≠ 0 := fun h => hn ((choiceDegree_zero_iff s).mp h)
  omega

theorem choiceValue_with_field (U : K → ℝ) (c : K → V → ℝ) (t : ℝ) (z : V → ℝ) (s : K → Option V) :
    choiceValue U (fun k i => t * c k i * z i) s =
      choiceBase U s * t ^ choiceDegree s * (∏ k : ShiftPositions s, c k.val (choiceSite s k)) *
        (∏ k : ShiftPositions s, z (choiceSite s k)) := by
  rw [choiceValue_split]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, choiceDegree]
  ring

theorem expect_shifted_product (μ : FiniteLaw Ω) (U : Ω → K → ℝ) (c : K → V → ℝ)
    (t : ℝ) (z : V → ℝ) :
    μ.expect (fun ω => ∏ k, (U ω k + ∑ i, t * c k i * z i)) =
      ∑ s : K → Option V, μ.expect (fun ω => choiceBase (U ω) s) * t ^ choiceDegree s *
        (∏ k : ShiftPositions s, c k.val (choiceSite s k)) * (∏ k : ShiftPositions s, z (choiceSite s k)) := by
  simp_rw [shifted_product_expansion, choiceValue_with_field]
  rw [μ.expect_fintype_sum]
  simp only [FiniteLaw.expect_mul_const]

theorem shift_increment_expansion (μ : FiniteLaw Ω) (U : Ω → K → ℝ) (c : K → V → ℝ)
    (t : ℝ) (z : V → ℝ) :
    μ.expect (fun ω => ∏ k, (U ω k + ∑ i, t * c k i * z i)) - μ.expect (fun ω => ∏ k, U ω k) =
      ∑ s : K → Option V, shiftChoiceWeight μ U s * t ^ choiceDegree s *
        (∏ k : ShiftPositions s, c k.val (choiceSite s k)) * (∏ k : ShiftPositions s, z (choiceSite s k)) := by
  let f (s : K → Option V) := μ.expect (fun ω => choiceBase (U ω) s) * t ^ choiceDegree s *
    (∏ k : ShiftPositions s, c k.val (choiceSite s k)) * (∏ k : ShiftPositions s, z (choiceSite s k))
  have hz : f (fun _ => none) = μ.expect (fun ω => ∏ k, U ω k) := by
    have h := μ.expect_congr (fun ω => choiceValue_with_field (U ω) c t z (fun _ => none))
    simpa only [choiceValue, Option.elim_none, FiniteLaw.expect_mul_const, f] using h.symm
  rw [expect_shifted_product, ← hz, finite_sum_sub_single f (fun _ => none)]
  apply Finset.sum_congr rfl
  intro s _
  simp only [f, shiftChoiceWeight, ite_mul, zero_mul]

def choiceSites (s : K → Option V) : Finset V := Finset.univ.image (choiceSite s)

theorem choiceSites_card (s : K → Option V) (hs : Function.Injective (choiceSite s)) :
    (choiceSites s).card = choiceDegree s := by
  rw [choiceSites, Finset.card_image_of_injective _ hs, Finset.card_univ]
  rfl

theorem choiceSites_product (s : K → Option V) (hs : Function.Injective (choiceSite s)) (z : V → ℝ) :
    (∏ k : ShiftPositions s, z (choiceSite s k)) = ∏ i ∈ choiceSites s, z i := by
  rw [choiceSites, Finset.prod_image]
  exact fun a _ b _ h => hs h

end CausalLowerbound.PartC
