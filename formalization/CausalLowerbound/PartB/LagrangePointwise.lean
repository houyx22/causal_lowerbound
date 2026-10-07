import CausalLowerbound.PartB.PaperWiener

/-! Pointwise inverse-product-distance bounds for the actual interpolation
coefficients. These estimates also hold on collision configurations after
multiplication by the vertex distance product. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartB.ShellGeometry
open ConfigurationShells

variable {d V : Type*} [Fintype d] [DecidableEq d] [Fintype V] [LinearOrder V]

theorem embedding_abs_le (u : d → ℝ) (a : d × Bool) : |embedding u a| ≤ 1 := by
  unfold embedding
  split_ifs
  · exact Real.abs_sin_le_one _
  · exact Real.abs_cos_le_one _

theorem pairDenominator_eq_sq (u v : d → ℝ) : pairDenominator u v = chordDistance u v ^ 2 := by
  symm
  exact Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem embedding_difference_abs_le (u v : d → ℝ) (a : d × Bool) :
    |embedding u a - embedding v a| ≤ chordDistance u v := by
  have hs : (embedding u a - embedding v a) ^ 2 ≤ pairDenominator u v :=
    Finset.single_le_sum (f := fun b => (embedding u b - embedding v b) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ a)
  rw [pairDenominator_eq_sq] at hs
  nlinarith [sq_abs (embedding u a - embedding v a), chordDistance_nonneg u v,
    abs_nonneg (embedding u a - embedding v a)]

private theorem ratio_cap_bound (N c δ C : ℝ) (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hδc : δ ≤ 2 * c) (hC : 0 ≤ C) (hN : |N| ≤ C * c) :
    |N / c ^ 2| * δ ≤ 2 * C := by
  by_cases hc0 : c = 0
  · simp [hc0, hC]
  have hc' : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  rw [abs_div, abs_of_nonneg (sq_nonneg c), div_mul_eq_mul_div,
    div_le_iff₀ (sq_pos_of_pos hc')]
  have hm := mul_le_mul hN hδc hδ (mul_nonneg hC hc)
  nlinarith

def elementaryBound (d : Type*) [Fintype d] : ℝ := 2 * (Fintype.card (d × Bool) + 1)

theorem elementaryBound_pos : 0 < elementaryBound d := by
  unfold elementaryBound
  positivity

theorem elementaryCoefficient_distance_bound (u v : d → ℝ) (k : Option (d × Bool)) :
    |elementaryCoefficient u v k| * truncatedDistance u v ≤ elementaryBound d := by
  have hc := chordDistance_nonneg u v
  have hδ := (truncatedDistance_range u v).1
  have hδc : truncatedDistance u v ≤ 2 * chordDistance u v := distanceCap_le_twice hc
  cases k with
  | some a =>
    have hb := ratio_cap_bound (embedding u a - embedding v a) (chordDistance u v)
      (truncatedDistance u v) 1 hc hδ hδc zero_le_one (by simpa using embedding_difference_abs_le u v a)
    simp only [elementaryCoefficient, pairDenominator_eq_sq]
    exact hb.trans (by unfold elementaryBound; have := Nat.cast_nonneg (α := ℝ) (Fintype.card (d × Bool)); linarith)
  | none =>
    have hn : |∑ a, embedding v a * (embedding u a - embedding v a)| ≤
        (Fintype.card (d × Bool) : ℝ) * chordDistance u v := by
      calc
        _ ≤ ∑ a, |embedding v a * (embedding u a - embedding v a)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _a : d × Bool, chordDistance u v := Finset.sum_le_sum (fun a _ => by
          rw [abs_mul]
          exact (mul_le_mul (embedding_abs_le v a) (embedding_difference_abs_le u v a)
            (abs_nonneg _) zero_le_one).trans_eq (one_mul _))
        _ = _ := by simp
    have hb := ratio_cap_bound _ _ _ _ hc hδ hδc (Nat.cast_nonneg _) hn
    simp only [elementaryCoefficient, pairDenominator_eq_sq]
    exact hb.trans (by unfold elementaryBound; linarith)

theorem selectionWeight_abs_le {K : Type*} [Fintype K] (ν : d × Bool →₀ ℕ)
    (s : K → Option (d × Bool)) : |selectionWeight ν s| ≤ 1 := by
  unfold selectionWeight
  split_ifs
  · rw [Finset.abs_prod]
    apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
    intro k _
    cases s k <;> norm_num [atomSign]
  · norm_num

def lagrangePointwiseConstant (V d : Type*) [Fintype V] [Fintype d] : ℝ :=
  (Fintype.card (Option (d × Bool)) : ℝ) ^ (Fintype.card V - 1) *
    elementaryBound d ^ (Fintype.card V - 1)

theorem lagrangePointwiseConstant_pos : 0 < lagrangePointwiseConstant V d := by
  unfold lagrangePointwiseConstant
  exact mul_pos (pow_pos (by exact_mod_cast Fintype.card_pos) _) (pow_pos elementaryBound_pos _)

theorem incident_distance_product (i : V) (u : V × d → ℝ) :
    (∏ e : {e : CompleteEdge V // incident edgeLeft edgeRight i e},
      truncatedDistance (configurationSite u i) (configurationSite u (otherVertex i e))) =
      completeVertexProduct i u := by
  exact (incidentNeighborEquiv i).prod_comp (fun j =>
    truncatedDistance (configurationSite u i) (configurationSite u j.val))

theorem incident_card (i : V) :
    Fintype.card {e : CompleteEdge V // incident edgeLeft edgeRight i e} = Fintype.card V - 1 := by
  rw [Fintype.card_congr (incidentNeighborEquiv i)]
  simp [Fintype.card_subtype_compl]

/-- The coordinate bound has a fixed constant depending only on dimension
and the number of sites, with exactly the paper's distance-product loss. -/
theorem lagrangeCoefficient_distance_bound (i : V) (ν : d × Bool →₀ ℕ) (u : V × d → ℝ) :
    |lagrangeCoefficient edgeLeft edgeRight i ν u| * completeVertexProduct i u ≤
      lagrangePointwiseConstant V d := by
  classical
  let K := {e : CompleteEdge V // incident edgeLeft edgeRight i e}
  have hP : 0 ≤ completeVertexProduct i u :=
    Finset.prod_nonneg (fun _ _ => (truncatedDistance_range _ _).1)
  rw [lagrange_coefficient_expansion]
  calc
    _ ≤ (∑ s : K → Option (d × Bool), |selectionWeight ν s *
        ∏ e, graphFactor edgeLeft edgeRight (e.val, incidentOrientation edgeRight i e.val, s e) u|) *
          completeVertexProduct i u := mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hP
    _ = ∑ s : K → Option (d × Bool), |selectionWeight ν s| *
        (∏ e, |elementaryCoefficient (configurationSite u i)
          (configurationSite u (otherVertex i e)) (s e)| *
            truncatedDistance (configurationSite u i) (configurationSite u (otherVertex i e))) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      simp only [abs_mul, Finset.abs_prod, incident_graphFactor,
        ← incident_distance_product i u, ← mul_assoc, Finset.prod_mul_distrib]
      rfl
    _ ≤ ∑ _s : K → Option (d × Bool), elementaryBound d ^ Fintype.card K := by
      apply Finset.sum_le_sum
      intro s _
      have hp : (∏ e : K, |elementaryCoefficient (configurationSite u i)
          (configurationSite u (otherVertex i e)) (s e)| *
            truncatedDistance (configurationSite u i) (configurationSite u (otherVertex i e))) ≤
          elementaryBound d ^ Fintype.card K := by
        simpa only [Finset.prod_const, Finset.card_univ] using
          Finset.prod_le_prod (s := Finset.univ)
            (fun e _ => mul_nonneg (abs_nonneg _) (truncatedDistance_range _ _).1)
            (fun e _ => elementaryCoefficient_distance_bound (configurationSite u i)
              (configurationSite u (otherVertex i e)) (s e))
      exact (mul_le_mul (selectionWeight_abs_le ν s) hp
        (Finset.prod_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (truncatedDistance_range _ _).1))
          zero_le_one).trans_eq (one_mul _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun,
        Nat.cast_pow, lagrangePointwiseConstant, K, incident_card]

theorem lagrangeCoefficient_abs_le (i : V) (ν : d × Bool →₀ ℕ) (u : V × d → ℝ)
    (hP : 0 < completeVertexProduct i u) :
    |lagrangeCoefficient edgeLeft edgeRight i ν u| ≤
      lagrangePointwiseConstant V d / completeVertexProduct i u :=
  (le_div_iff₀ hP).mpr (lagrangeCoefficient_distance_bound i ν u)

end CausalLowerbound.PartB.ShellGeometry
