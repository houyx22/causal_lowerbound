import CausalLowerbound.PartC.AssignedRowBridge
import CausalLowerbound.PartC.ObservationBlockChoices

/-! Regroup the observation-choice expansion by rows and observations.
The selected block replaces exactly one factor in the carrier-row product;
the resulting one-observation expression is the assigned-row bridge. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB RoughPropensity
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

theorem option_row_weight (a : ℝ) (δ z v : K → ℝ) (s : Option K) :
    s.elim a δ * (∏ k, if s = some k then v k else z k) =
      s.elim (a * ∏ k, z k) (fun k => δ k * v k * ∏ j ∈ Finset.univ.erase k, z j) := by
  cases s with
  | none => simp
  | some k =>
    have hp : (∏ j, if (some k : Option K) = some j then v j else z j) =
        v k * ∏ j ∈ Finset.univ.erase k, z j := by
      rw [← Finset.mul_prod_erase Finset.univ
        (fun j => if (some k : Option K) = some j then v j else z j) (Finset.mem_univ k)]
      simp only [if_true]
      apply congrArg (fun x : ℝ => v k * x)
      apply Finset.prod_congr rfl
      intro j hj
      rw [if_neg (fun he => (Finset.mem_erase.mp hj).1 (Option.some.inj he).symm)]
    rw [hp]
    simp only [Option.elim_some, mul_assoc]

theorem observation_row_product_expansion
    (a : I → ℝ) (δ : I → K → ℝ) (z v : K → I → ℝ) :
    (∑ s : I → Option K, (choiceBase a s * ∏ i : ShiftPositions s, δ i.val (choiceSite s i)) *
      ∏ k, ∏ i, if s i = some k then v k i else z k i) =
      ∏ i, ((a i * ∏ k, z k i) + ∑ k, δ i k * v k i * ∏ j ∈ Finset.univ.erase k, z j i) := by
  rw [shifted_product_expansion]
  apply Finset.sum_congr rfl
  intro s _
  rw [← choiceValue_split]
  change (∏ i, (s i).elim (a i) (δ i)) * (∏ k, ∏ i, if s i = some k then v k i else z k i) = _
  rw [Finset.prod_comm, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact option_row_weight (a i) (δ i) (fun k => z k i) (fun k => v k i) (s i)

theorem assigned_pattern_row_matching
    {Ξ : I → Type*} [∀ i, Fintype (Ξ i)] (μ : ∀ i, FiniteLaw (Ξ i)) (X : ∀ i, Ξ i → ℝ)
    (R T ja v smooth : I → ℝ) (shift scale : I → K → ℝ) (owner : I → K)
    (hscale : ∀ i k, k ≠ owner i → scale i k = 0)
    (e : I → K → ℕ) (he : ∀ i, e i (owner i) ≤ 1)
    (hmean : ∀ i, (μ i).expect (X i) = 0)
    (hvar : ∀ i, (μ i).expect (fun ω => X i ω ^ 2) = v i) :
    (FiniteLaw.independent μ).expect (fun ω => ∑ s : I → Option K,
      (choiceBase (fun i => likelihood (R i) (T i) (ja i) (smooth i) (X i (ω i))) s *
        ∏ i : ShiftPositions s, increment (R i.val) (T i.val) (ja i.val)
          (shift i.val (choiceSite s i)) (X i.val (ω i.val))) *
        ∏ k, ∏ i, if s i = some k then
          normalizedSubstitution (e i k) (scale i k) (ja i) (v i) (X i (ω i))
          else (scale i k * X i (ω i)) ^ e i k) =
      (FiniteLaw.independent μ).expect (fun ω =>
        (∏ k, ∏ i, (scale i k * X i (ω i)) ^ e i k) *
          ∏ i, (likelihood (R i) (T i) (ja i) (smooth i) (X i (ω i)) +
            realField (R i) (T i) (ja i) (ja i * shift i (owner i) * scale i (owner i) * v i) (X i (ω i)))) := by
  calc
    _ = (FiniteLaw.independent μ).expect (fun ω => ∏ i,
      ((∏ k, (scale i k * X i (ω i)) ^ e i k) * likelihood (R i) (T i) (ja i) (smooth i) (X i (ω i)) +
        ∑ k, (normalizedSubstitution (e i k) (scale i k) (ja i) (v i) (X i (ω i)) *
          increment (R i) (T i) (ja i) (shift i k) (X i (ω i))) *
          ∏ j ∈ Finset.univ.erase k, (scale i j * X i (ω i)) ^ e i j)) := by
      apply FiniteLaw.expect_congr
      intro ω
      rw [observation_row_product_expansion
        (fun i => likelihood (R i) (T i) (ja i) (smooth i) (X i (ω i)))
        (fun i k => increment (R i) (T i) (ja i) (shift i k) (X i (ω i)))
        (fun k i => (scale i k * X i (ω i)) ^ e i k)
        (fun k i => normalizedSubstitution (e i k) (scale i k) (ja i) (v i) (X i (ω i)))]
      apply Finset.prod_congr rfl
      intro i _
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro k _
        ring
    _ = _ := by
      rw [assigned_product_bridge μ X R T ja v smooth shift scale owner hscale e he hmean hvar]
      apply FiniteLaw.expect_congr
      intro ω
      rw [Finset.prod_mul_distrib, Finset.prod_comm]

end CausalLowerbound.PartC
