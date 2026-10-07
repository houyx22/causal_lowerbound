import CausalLowerbound.PartC.BlockCubicFunctional

/-! Expand each observation by choosing a Taylor degree from zero to
three and a block for each occurrence. Mixed block monomials stay in
the expansion, and the cubic functional supplies its exact degree filter. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial Representative
variable {I K V : Type*} [Fintype I] [DecidableEq I]
  [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]

abbrev CubicObservationChoice (K : Type*) := Σ n : Fin 4, Fin n.val → K

abbrev CubicObservationPositions (s : I → CubicObservationChoice K) := Σ i : I, Fin (s i).1.val

def cubicObservationChoiceDegree (s : I → CubicObservationChoice K) : ℕ :=
  Fintype.card (CubicObservationPositions s)

def cubicObservationChoiceSlot (slot : K → I → V) (s : I → CubicObservationChoice K)
    (p : CubicObservationPositions s) : K × V :=
  ((s p.1).2 p.2, slot ((s p.1).2 p.2) p.1)

def cubicObservationChoiceWeight (δ : I → K → ℝ) (s : I → CubicObservationChoice K) : ℝ :=
  ∏ p : CubicObservationPositions s, δ p.1 ((s p.1).2 p.2)

def cubicObservationExpansion (w : K → Degree V 3 → ℝ)
    (b : I → Fin 4 → ℝ) (δ : I → K → ℝ) (slot : K → I → V) (amp : ℝ) : ℝ :=
  ∑ s : I → CubicObservationChoice K,
    if hs : ∀ v, siteOccurrenceExponent (cubicObservationChoiceSlot slot s) v ≤ 3 then
      amp ^ cubicObservationChoiceDegree s *
        ((∏ i, b i (s i).1) * cubicObservationChoiceWeight δ s) *
          ∏ k, w k (fun v => cubicSiteDegree (siteOccurrenceExponent (cubicObservationChoiceSlot slot s)) hs (k, v))
    else 0

theorem cubicObservationChoiceDegree_eq (s : I → CubicObservationChoice K) :
    cubicObservationChoiceDegree s = ∑ i, (s i).1.val := by
  simp only [cubicObservationChoiceDegree, Fintype.card_sigma, Fintype.card_fin]

theorem cubic_observation_choice_polynomial (b : I → Fin 4 → ℝ) (δ : I → K → ℝ)
    (slot : K → I → V) :
    (∏ i, ∑ n : Fin 4, C (b i n) * (∑ k, C (δ i k) * X (k, slot k i)) ^ n.val) =
      ∑ s : I → CubicObservationChoice K,
        C ((∏ i, b i (s i).1) * cubicObservationChoiceWeight δ s) *
          ∏ p : CubicObservationPositions s, X (cubicObservationChoiceSlot slot s p) := by
  have hi (i : I) :
      (∑ n : Fin 4, C (b i n) * (∑ k, C (δ i k) * X (k, slot k i)) ^ n.val) =
      ∑ q : CubicObservationChoice K,
        C (b i q.1 * ∏ j : Fin q.1.val, δ i (q.2 j)) *
          ∏ j : Fin q.1.val, (X (q.2 j, slot (q.2 j) i) : MvPolynomial (K × V) ℝ) := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro n _
    rw [show ((∑ k, C (δ i k) * X (k, slot k i)) ^ n.val : MvPolynomial (K × V) ℝ) =
        ∏ _j : Fin n.val, ∑ k, C (δ i k) * X (k, slot k i) by simp,
      Fintype.prod_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.prod_mul_distrib, ← map_prod, map_mul]
    ring
  simp_rw [hi]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.prod_mul_distrib, ← map_prod]
  simp only [Finset.prod_mul_distrib, cubicObservationChoiceWeight,
    cubicObservationChoiceSlot, Fintype.prod_sigma]

theorem block_cubic_observation_expansion (w : K → Degree V 3 → ℝ)
    (b : I → Fin 4 → ℝ) (δ : I → K → ℝ) (slot : K → I → V) :
    blockPolynomialFunctional (fun k => cubicSiteFunctional (w k))
      (∏ i, ∑ n : Fin 4, C (b i n) * (∑ k, C (δ i k) * X (k, slot k i)) ^ n.val) =
      ∑ s : I → CubicObservationChoice K,
        if hs : ∀ v, siteOccurrenceExponent (cubicObservationChoiceSlot slot s) v ≤ 3 then
          ((∏ i, b i (s i).1) * cubicObservationChoiceWeight δ s) *
            ∏ k, w k (fun v => cubicSiteDegree (siteOccurrenceExponent (cubicObservationChoiceSlot slot s)) hs (k, v))
        else 0 := by
  rw [blockPolynomialFunctional_cubic_patterns, cubic_observation_choice_polynomial, map_sum]
  simp only [MvPolynomial.C_mul', map_smul, smul_eq_mul, cubicSiteFunctional_prod_X,
    mul_dite, mul_zero]

theorem cubicObservationChoiceWeight_scale (δ : I → K → ℝ) (amp : ℝ)
    (s : I → CubicObservationChoice K) :
    cubicObservationChoiceWeight (fun i k => amp * δ i k) s =
      amp ^ cubicObservationChoiceDegree s * cubicObservationChoiceWeight δ s := by
  simp only [cubicObservationChoiceWeight, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, cubicObservationChoiceDegree]

theorem block_cubic_observation_scaled_expansion (w : K → Degree V 3 → ℝ)
    (b : I → Fin 4 → ℝ) (δ : I → K → ℝ) (slot : K → I → V) (amp : ℝ) :
    blockPolynomialFunctional (fun k => cubicSiteFunctional (w k))
      (∏ i, ∑ n : Fin 4, C (b i n) * (∑ k, C (amp * δ i k) * X (k, slot k i)) ^ n.val) =
      ∑ s : I → CubicObservationChoice K,
        if hs : ∀ v, siteOccurrenceExponent (cubicObservationChoiceSlot slot s) v ≤ 3 then
          amp ^ cubicObservationChoiceDegree s *
            ((∏ i, b i (s i).1) * cubicObservationChoiceWeight δ s) *
              ∏ k, w k (fun v => cubicSiteDegree (siteOccurrenceExponent (cubicObservationChoiceSlot slot s)) hs (k, v))
        else 0 := by
  rw [block_cubic_observation_expansion]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : ∀ v, siteOccurrenceExponent (cubicObservationChoiceSlot slot s) v ≤ 3
  · rw [dif_pos hs, dif_pos hs, cubicObservationChoiceWeight_scale]
    ring
  · rw [dif_neg hs, dif_neg hs]

theorem cubicObservationChoiceWeight_nonzero (δ : I → K → ℝ)
    (s : I → CubicObservationChoice K) (hs : cubicObservationChoiceWeight δ s ≠ 0)
    (p : CubicObservationPositions s) : δ p.1 ((s p.1).2 p.2) ≠ 0 :=
  Finset.prod_ne_zero_iff.mp hs p (Finset.mem_univ p)

theorem cubicObservationChoice_degree_sum (slot : K → I → V) (s : I → CubicObservationChoice K)
    (hs : ∀ v, siteOccurrenceExponent (cubicObservationChoiceSlot slot s) v ≤ 3) :
    (∑ k, degreeSize (fun v => cubicSiteDegree (siteOccurrenceExponent (cubicObservationChoiceSlot slot s)) hs (k, v))) =
      cubicObservationChoiceDegree s := by
  change (∑ k, ∑ v, siteOccurrenceExponent (cubicObservationChoiceSlot slot s) (k, v)) =
    Fintype.card (CubicObservationPositions s)
  rw [← Fintype.sum_prod_type]
  simp only [siteOccurrenceExponent_apply, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem cubicObservationChoice_supported (δ : I → K → ℝ) (slot : K → I → V)
    (P : K → V → Prop) (hP : ∀ i k, δ i k ≠ 0 → P k (slot k i))
    (s : I → CubicObservationChoice K) (hδ : cubicObservationChoiceWeight δ s ≠ 0)
    (hs : ∀ v, siteOccurrenceExponent (cubicObservationChoiceSlot slot s) v ≤ 3)
    (k : K) (v : V)
    (hv : cubicSiteDegree (siteOccurrenceExponent (cubicObservationChoiceSlot slot s)) hs (k, v) ≠ 0) :
    P k v := by
  have hn : siteOccurrenceExponent (cubicObservationChoiceSlot slot s) (k, v) ≠ 0 := by
    intro hz
    exact hv (Fin.ext hz)
  rw [siteOccurrenceExponent_apply] at hn
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hn)
  have he : cubicObservationChoiceSlot slot s p = (k, v) := (Finset.mem_filter.mp hp).2
  have hk : (s p.1).2 p.2 = k := congrArg Prod.fst he
  have hslot : slot ((s p.1).2 p.2) p.1 = v := congrArg Prod.snd he
  have hh := hP p.1 ((s p.1).2 p.2) (cubicObservationChoiceWeight_nonzero δ s hδ p)
  rw [hslot] at hh
  simpa only [hk] using hh

end CausalLowerbound.PartC
