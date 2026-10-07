import CausalLowerbound.PartC.RetainedPolynomialMap

/-! Pull the completed cubic functional back to the common observation
variables. The zero substitution at nonincident observations is exact;
it agrees with the actual row weights when those rough variables vanish. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial Wiener Representative
variable {I V G d J : Type*} [Fintype I] [DecidableEq I]
  [Fintype V] [DecidableEq V] [Fintype G] [Fintype d] [Fintype J] [DecidableEq J]

def retainedCubicWeight (P : I → Prop) (e : {i // P i} ⊕ G ≃ V)
    (w : Degree V 3 → ℝ) (f : Degree I 3) : ℝ :=
  if ∀ i, ¬P i → f i = 0 then w (completedSites e (fun i => f i.val) (fun _ => 0)) else 0

theorem cubicSiteDegree_incident_iff (P : I → Prop) (m : I →₀ ℕ) (hm : ∀ i, m i ≤ 3) :
    (∀ i, ¬P i → cubicSiteDegree m hm i = 0) ↔ ∀ i, ¬P i → m i = 0 := by
  constructor
  · intro h i hi
    exact congrArg Fin.val (h i hi)
  · intro h i hi
    exact Fin.ext (h i hi)

theorem cubicSiteDegree_retainedExponent (P : I → Prop) (e : {i // P i} ⊕ G ≃ V)
    (m : I →₀ ℕ) (hm : ∀ i, m i ≤ 3) (hv : ∀ v, retainedExponent P e m v ≤ 3) :
    cubicSiteDegree (retainedExponent P e m) hv =
      completedSites e (fun i => cubicSiteDegree m hm i.val) (fun _ => 0) := by
  funext v
  obtain ⟨z, rfl⟩ := e.surjective v
  cases z with
  | inl i =>
    apply Fin.ext
    simp only [cubicSiteDegree, retainedExponent_retained, completedSites_retained]
  | inr j =>
    apply Fin.ext
    simp only [cubicSiteDegree, retainedExponent_ghost, completedSites_ghost, Fin.val_zero]

theorem cubicSiteFunctional_retained_map (P : I → Prop) (e : {i // P i} ⊕ G ≃ V)
    (w : Degree V 3 → ℝ) (p : MvPolynomial I ℝ) :
    cubicSiteFunctional w (retainedPolynomialMap P e p) =
      cubicSiteFunctional (retainedCubicWeight P e w) p := by
  let L := (cubicSiteFunctional w).comp (retainedPolynomialMap P e).toLinearMap
  let R := cubicSiteFunctional (retainedCubicWeight P e w)
  change L p = R p
  rw [polynomial_linear_expansion L p, polynomial_linear_expansion R p]
  apply Finset.sum_congr rfl
  intro m _
  congr 1
  simp only [L, R, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [retainedPolynomialMap_monomial]
  by_cases hm : ∀ i, ¬P i → m i = 0
  · rw [if_pos hm, cubicSiteFunctional_monomial, cubicSiteFunctional_monomial, one_mul, one_mul]
    by_cases hd : ∀ i, m i ≤ 3
    · have hv := (retainedExponent_degree_iff P e m hm).mpr hd
      rw [dif_pos hv, dif_pos hd, retainedCubicWeight,
        if_pos ((cubicSiteDegree_incident_iff P m hd).mpr hm), cubicSiteDegree_retainedExponent P e m hd hv]
    · have hv : ¬∀ v, retainedExponent P e m v ≤ 3 :=
        fun h => hd ((retainedExponent_degree_iff P e m hm).mp h)
      rw [dif_neg hv, dif_neg hd]
  · rw [if_neg hm, map_zero, cubicSiteFunctional_monomial, one_mul]
    by_cases hd : ∀ i, m i ≤ 3
    · rw [dif_pos hd, retainedCubicWeight,
        if_neg (fun h => hm ((cubicSiteDegree_incident_iff P m hd).mp h))]
    · rw [dif_neg hd]

theorem retainedCubicWeight_outcome_rows (P : I → Prop) (e : {i // P i} ⊕ G ≃ V)
    (κ : V → ℝ) (v a : I → ℝ) (hκ : ∀ i : {i // P i}, κ (e (Sum.inl i)) = v i.val)
    (ha : ∀ i, ¬P i → a i = 0) (W : Array d V J 3) (u : V × d → ℝ)
    (ζ : J → Bool) (g : G → ℝ) (f : Degree I 3) :
    retainedCubicWeight P e
      (outcomePatternWeight κ W u (completedSites e (fun i => a i.val) g) ζ) f =
      ∑ r : Row V J 3, completedOutcomeRowCoefficient W u ζ e g r *
        ∏ i, if f i = 0 then a i ^ (retainedOutcomeRowDegree P e r.1 i).val else
          outcomeMoment (v i) (retainedOutcomeRowDegree P e r.1 i) * a i ^ (f i).val := by
  by_cases hf : ∀ i, ¬P i → f i = 0
  · rw [retainedCubicWeight, if_pos hf]
    exact outcomePatternWeight_retained_rows P e κ v a hκ W u ζ g f hf
  · rw [retainedCubicWeight, if_neg hf]
    push_neg at hf
    obtain ⟨i, hi, hfi⟩ := hf
    symm
    apply Finset.sum_eq_zero
    intro r _
    have hfn : (f i).val ≠ 0 := fun h => hfi (Fin.ext h)
    have hz : (∏ j, if f j = 0 then a j ^ (retainedOutcomeRowDegree P e r.1 j).val else
        outcomeMoment (v j) (retainedOutcomeRowDegree P e r.1 j) * a j ^ (f j).val) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp only [if_neg hfi, ha i hi, zero_pow hfn, mul_zero]
    rw [hz, mul_zero]

theorem outcomePolynomialFunctional_retained_map
    (P : I → Prop) (e : {i // P i} ⊕ G ≃ V) (κ : V → ℝ) (v a : I → ℝ)
    (hκ : ∀ i : {i // P i}, κ (e (Sum.inl i)) = v i.val) (ha : ∀ i, ¬P i → a i = 0)
    (W : Array d V J 3) (u : V × d → ℝ) (ζ : J → Bool) (g : G → ℝ) (p : MvPolynomial I ℝ) :
    outcomePolynomialFunctional κ W u (completedSites e (fun i => a i.val) g) ζ
      (retainedPolynomialMap P e p) =
      cubicSiteFunctional (fun f => ∑ r : Row V J 3, completedOutcomeRowCoefficient W u ζ e g r *
        ∏ i, if f i = 0 then a i ^ (retainedOutcomeRowDegree P e r.1 i).val else
          outcomeMoment (v i) (retainedOutcomeRowDegree P e r.1 i) * a i ^ (f i).val) p := by
  rw [outcomePolynomialFunctional, cubicSiteFunctional_retained_map]
  apply congrArg (fun w : Degree I 3 → ℝ => cubicSiteFunctional w p)
  funext f
  exact retainedCubicWeight_outcome_rows P e κ v a hκ ha W u ζ g f

end CausalLowerbound.PartC
