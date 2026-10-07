import CausalLowerbound.PartC.RepresentativeFactors

/-! A symbol in a cross-slot tensor must occur in one of its factors. The
resulting bound depends on the number of slots, never on the number of signs. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal

namespace CausalLowerbound.PartC.Representative

variable {d ι J : Type*} [Fintype d] [Fintype ι] [Fintype J]
  [DecidableEq ι] [DecidableEq J] {D : ℕ}

theorem symbolPart_single (j : J) (r : Row ι J D) (a : Wiener.Fourier (ι × d)) :
    symbolPart j (lp.single 1 r a : Array d ι J D) =
      if j ∈ r.2 then lp.single 1 r a else 0 := by
  unfold symbolPart FiniteL1.project FiniteL1.diagonal
  rw [FiniteL1.transform_single]
  split_ifs <;> simp

theorem factorSymbol_norm (j : J) (a : Factor d J D) :
    ‖factorSymbol j a‖ = ∑ r, if j ∈ r.2 then ‖a r‖ else 0 := FiniteL1.project_norm _ _

theorem tensor_symbol_bound (j : J) (f : ι → Factor d J D) (M σ : ℝ)
    (hM : 0 ≤ M) (hσ : 0 ≤ σ) (hf : ∀ i, ‖f i‖ ≤ M) (hs : ∀ i, ‖factorSymbol j (f i)‖ ≤ σ) :
    ‖symbolPart j (tensor f)‖ ≤ (Fintype.card ι : ℝ) * σ * M ^ (Fintype.card ι - 1) := by
  let G (i k : ι) (r : FactorRow J D) : ℝ :=
    if k = i then (if j ∈ r.2 then ‖f k r‖ else 0) else ‖f k r‖
  have hG (i k : ι) (r : FactorRow J D) : 0 ≤ G i k r := by
    dsimp only [G]
    split_ifs <;> positivity
  have hterm (r : ι → FactorRow J D) :
      ‖symbolPart j (lp.single 1 (tensorRow r) (Wiener.tensor (fun i => f i (r i))) : Array d ι J D)‖ ≤
        ∑ i, ∏ k, G i k (r k) := by
    rw [symbolPart_single]
    by_cases h : j ∈ (tensorRow r).2
    · rw [if_pos h, lp.norm_single (by norm_num : 0 < (1 : ℝ≥0∞))]
      obtain ⟨i, hi⟩ := Walsh.mem_parityUnion (fun k => (r k).2) h
      calc
        _ ≤ ∏ k, ‖f k (r k)‖ := Wiener.tensor_norm _
        _ = ∏ k, G i k (r k) := by
          apply Finset.prod_congr rfl
          intro k _
          by_cases hki : k = i
          · subst k
            simp only [G, if_pos rfl, if_pos hi]
          · simp only [G, if_neg hki]
        _ ≤ _ := Finset.single_le_sum (f := fun i => ∏ k, G i k (r k))
          (fun i _ => Finset.prod_nonneg (fun k _ => hG i k (r k))) (Finset.mem_univ i)
    · rw [if_neg h, norm_zero]
      exact Finset.sum_nonneg (fun i _ => Finset.prod_nonneg (fun k _ => hG i k (r k)))
  have hsum (i k : ι) : (∑ r : FactorRow J D, G i k r) ≤ if k = i then σ else M := by
    by_cases hki : k = i
    · subst k
      simpa only [G, if_pos rfl, ← factorSymbol_norm] using hs i
    · rw [if_neg hki]
      calc
        _ = ‖f k‖ := by simp only [G, if_neg hki]; exact (FiniteL1.norm_eq_sum (f k)).symm
        _ ≤ M := hf k
  have hprod (i : ι) : (∏ k : ι, if k = i then σ else M) = σ * M ^ (Fintype.card ι - 1) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), if_pos rfl]
    congr 1
    calc
      _ = ∏ _k ∈ Finset.univ.erase i, M := by
        apply Finset.prod_congr rfl
        intro k hk
        exact if_neg (Finset.mem_erase.mp hk).1
      _ = M ^ (Fintype.card ι - 1) := by simp
  calc
    _ = ‖∑ r : ι → FactorRow J D,
        symbolPart j (lp.single 1 (tensorRow r) (Wiener.tensor (fun i => f i (r i))) : Array d ι J D)‖ := by
      simp only [tensor, map_sum]
    _ ≤ ∑ r : ι → FactorRow J D,
        ‖symbolPart j (lp.single 1 (tensorRow r) (Wiener.tensor (fun i => f i (r i))) : Array d ι J D)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ r : ι → FactorRow J D, ∑ i, ∏ k, G i k (r k) :=
      Finset.sum_le_sum (fun r _ => hterm r)
    _ = ∑ i, ∏ k, ∑ r : FactorRow J D, G i k r := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      exact (Fintype.prod_sum (fun (k : ι) (r : FactorRow J D) => G i k r)).symm
    _ ≤ ∑ i : ι, ∏ k : ι, if k = i then σ else M := Finset.sum_le_sum (fun i _ =>
      Finset.prod_le_prod (fun k _ => Finset.sum_nonneg (fun r _ => hG i k r)) (fun k _ => hsum i k))
    _ = _ := by simp only [hprod, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end CausalLowerbound.PartC.Representative
