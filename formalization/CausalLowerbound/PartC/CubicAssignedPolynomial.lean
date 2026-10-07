import CausalLowerbound.PartC.CubicSitePolynomial

/-! A cubic polynomial may contain mixed monomials from many blocks.
When every unassigned block has zero positive-degree weight, these
monomials vanish under the actual cubic functional, without discarding
them from the polynomial beforehand. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial Representative
variable {K : Type*} [Fintype K] [DecidableEq K]

theorem cubicOccurrence_le (n : Fin 4) (s : Fin n.val → K) (k : K) :
    siteOccurrenceExponent s k ≤ 3 := by
  rw [siteOccurrenceExponent_apply]
  exact (Finset.card_filter_le _ _).trans (by
    simpa only [Finset.card_univ, Fintype.card_fin] using Nat.le_of_lt_succ n.isLt)

theorem cubicSiteFunctional_linear_pow (w : Degree K 3 → ℝ) (c : K → ℝ) (n : Fin 4) :
    cubicSiteFunctional w ((∑ k, C (c k) * X k) ^ n.val) =
      ∑ s : Fin n.val → K, (∏ j, c (s j)) *
        w (cubicSiteDegree (siteOccurrenceExponent s) (cubicOccurrence_le n s)) := by
  have hp : ((∑ k, C (c k) * X k) ^ n.val : MvPolynomial K ℝ) =
      ∑ s : Fin n.val → K, C (∏ j, c (s j)) * ∏ j, X (s j) := by
    calc
      _ = ∏ _j : Fin n.val, ∑ k, C (c k) * X k := by simp
      _ = ∑ s : Fin n.val → K, ∏ j, C (c (s j)) * X (s j) :=
        Fintype.prod_sum (fun (_ : Fin n.val) (k : K) => C (c k) * X k)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.prod_mul_distrib, ← map_prod]
  rw [hp, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [MvPolynomial.C_mul', map_smul, smul_eq_mul,
    cubicSiteFunctional_prod_X, dif_pos (cubicOccurrence_le n s)]

theorem cubicSiteFunctional_assigned_linear_pow (w : K → Fin 4 → ℝ) (c : K → ℝ)
    (owner : K) (hw : ∀ k, k ≠ owner → ∀ f : Fin 4, f ≠ 0 → w k f = 0) (n : Fin 4) :
    cubicSiteFunctional (fun e => ∏ k, w k (e k)) ((∑ k, C (c k) * X k) ^ n.val) =
      c owner ^ n.val * w owner n * ∏ k ∈ Finset.univ.erase owner, w k 0 := by
  rw [cubicSiteFunctional_linear_pow]
  rw [Finset.sum_eq_single (fun _ : Fin n.val => owner)]
  · have hdeg : cubicSiteDegree (siteOccurrenceExponent (fun _ : Fin n.val => owner))
        (cubicOccurrence_le n (fun _ => owner)) = fun k => if k = owner then n else 0 := by
      funext k
      apply Fin.ext
      by_cases hk : k = owner
      · subst k
        simp [cubicSiteDegree, siteOccurrenceExponent_apply]
      · simp [cubicSiteDegree, siteOccurrenceExponent_apply, hk, Ne.symm hk]
    rw [hdeg]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← Finset.mul_prod_erase Finset.univ (fun k => w k (if k = owner then n else 0))
      (Finset.mem_univ owner), if_pos rfl]
    have hoff : (∏ k ∈ Finset.univ.erase owner, w k (if k = owner then n else 0)) =
        ∏ k ∈ Finset.univ.erase owner, w k 0 := by
      apply Finset.prod_congr rfl
      intro k hk
      rw [if_neg (Finset.mem_erase.mp hk).1]
    rw [hoff]
    ring
  · intro s _ hs
    obtain ⟨j, hj⟩ : ∃ j, s j ≠ owner := by
      by_contra hn
      push_neg at hn
      exact hs (funext hn)
    have hpos : 0 < siteOccurrenceExponent s (s j) := by
      rw [siteOccurrenceExponent_apply, Finset.card_pos]
      exact ⟨j, by simp⟩
    have hnonzero : cubicSiteDegree (siteOccurrenceExponent s) (cubicOccurrence_le n s) (s j) ≠ 0 := by
      intro he
      have hz : siteOccurrenceExponent s (s j) = 0 := congrArg Fin.val he
      omega
    have hz : (∏ k, w k (cubicSiteDegree (siteOccurrenceExponent s) (cubicOccurrence_le n s) k)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ (s j)) (hw (s j) hj _ hnonzero)
    rw [hz, mul_zero]
  · intro hn
    exact False.elim (hn (Finset.mem_univ _))

theorem cubicSiteFunctional_assigned_polynomial (w : K → Fin 4 → ℝ) (c : K → ℝ)
    (owner : K) (hw : ∀ k, k ≠ owner → ∀ f : Fin 4, f ≠ 0 → w k f = 0)
    (a : Fin 4 → ℝ) :
    cubicSiteFunctional (fun e => ∏ k, w k (e k))
      (∑ n : Fin 4, C (a n) * (∑ k, C (c k) * X k) ^ n.val) =
      (∏ k ∈ Finset.univ.erase owner, w k 0) * ∑ n : Fin 4, a n * c owner ^ n.val * w owner n := by
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [MvPolynomial.C_mul', map_smul, smul_eq_mul,
    cubicSiteFunctional_assigned_linear_pow w c owner hw n]
  ring

end CausalLowerbound.PartC
