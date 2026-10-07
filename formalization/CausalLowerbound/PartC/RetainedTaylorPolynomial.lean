import CausalLowerbound.PartC.RetainedPolynomialMap
import CausalLowerbound.PartC.BlockPolynomialMap
import CausalLowerbound.PartC.OutcomeLikelihoodPolynomials

/-! Inserting the common observation polynomial into completed carrier
slots gives the full simultaneous cubic Taylor polynomial. A block
contributes only at its incident observations. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial
variable {K I V A B : Type*} [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

@[simp] theorem retainedPolynomialMap_X (P : I → Prop) {G : Type*}
    (e : {i // P i} ⊕ G ≃ V) (i : I) :
    retainedPolynomialMap P e (X i) =
      if hi : P i then X (e (Sum.inl ⟨i, hi⟩)) else 0 := by
  simp only [retainedPolynomialMap, aeval_X]

theorem outcomeTaylorPolynomial_algHom (f : MvPolynomial A ℝ →ₐ[ℝ] MvPolynomial B ℝ)
    (R T shift jb corr smooth rough : ℝ) (p : MvPolynomial A ℝ) :
    f (outcomeTaylorPolynomial R T shift jb corr smooth rough p) =
      outcomeTaylorPolynomial R T shift jb corr smooth rough (f p) := by
  simp only [outcomeTaylorPolynomial, map_add, map_mul, map_pow, algHom_C,
    algebraMap_eq]

theorem blockPolynomialMap_observation_linear
    (P : K → I → Prop) (G : K → Type*) (e : ∀ k, {i // P k i} ⊕ G k ≃ V)
    (slot : K → I → V) (hslot : ∀ k i (hi : P k i), slot k i = e k (Sum.inl ⟨i, hi⟩))
    (shift : I → K → ℝ) (hshift : ∀ i k, shift i k ≠ 0 → P k i) (i : I) :
    blockPolynomialMap (fun k => retainedPolynomialMap (P k) (e k))
      (rename (fun k => (k, i)) (∑ k, C (shift i k) * X k)) =
      ∑ k, C (shift i k) * X (k, slot k i) := by
  simp only [map_sum, map_mul, rename_C, rename_X, algHom_C, algebraMap_eq,
    blockPolynomialMap_X, retainedPolynomialMap_X]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hi : P k i
  · simp only [dif_pos hi, rename_X, hslot k i hi]
  · have hz : shift i k = 0 := by
      by_contra hn
      exact hi (hshift i k hn)
    simp only [dif_neg hi, hz, map_zero, zero_mul]

theorem blockPolynomialMap_observation_taylor
    (P : K → I → Prop) (G : K → Type*) (e : ∀ k, {i // P k i} ⊕ G k ≃ V)
    (slot : K → I → V) (hslot : ∀ k i (hi : P k i), slot k i = e k (Sum.inl ⟨i, hi⟩))
    (R T jb corr smooth rough : I → ℝ) (shift : I → K → ℝ)
    (hshift : ∀ i k, shift i k ≠ 0 → P k i) :
    blockPolynomialMap (fun k => retainedPolynomialMap (P k) (e k))
      (∏ i, rename (fun k => (k, i))
        (outcomeTaylorPolynomial (R i) (T i) 1 (jb i) (corr i) (smooth i) (rough i)
          (∑ k, C (shift i k) * X k))) =
      ∏ i, outcomeTaylorPolynomial (R i) (T i) 1 (jb i) (corr i) (smooth i) (rough i)
        (∑ k, C (shift i k) * X (k, slot k i)) := by
  simp only [map_prod, outcomeTaylorPolynomial_algHom,
    blockPolynomialMap_observation_linear P G e slot hslot shift hshift]

end CausalLowerbound.PartC
