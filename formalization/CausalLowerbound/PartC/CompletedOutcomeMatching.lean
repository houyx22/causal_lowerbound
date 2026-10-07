import CausalLowerbound.PartC.RetainedBlockFunctional
import CausalLowerbound.PartC.ResampledOutcomeRows

/-! Exact multi-carrier cubic matching with completed ghost sites. The
single shared resampled field drives all Fourier-Walsh coefficients and
ghost values; only the retained rough variables use the original field. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB Wiener Representative MvPolynomial RoughOutcome
variable {K I V d J : Type*} [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
  [Fintype d] [Fintype J] [DecidableEq J]

theorem completed_resampled_outcome_matching
    (P : K → I → Prop) (G : K → Type*) [∀ k, Fintype (G k)]
    (e : ∀ k, {i // P k i} ⊕ G k ≃ V)
    (κ : K → V → ℝ) (W : K → Array d V J 3) (u : K → V × d → ℝ)
    (g : ∀ k, (J → Bool) → G k → ℝ)
    (S : I → Finset J) (hS : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (rough : I → (J → Bool) → ℝ)
    (hrough : ∀ i ζ ζ', (∀ j ∈ S i, ζ j = ζ' j) → rough i ζ = rough i ζ')
    (R T jb corr v smooth : I → ℝ) (shift scale : I → K → ℝ) (owner : I → K)
    (hscale : ∀ i k, k ≠ owner i → scale i k = 0)
    (houtside : ∀ k i, ¬P k i → scale i k = 0)
    (hκ : ∀ k (i : {i // P k i}), κ k (e k (Sum.inl i)) = scale i.val k ^ 2 * v i.val)
    (hmean : ∀ i, independentSigns.expect (rough i) = 0)
    (hvar : ∀ i, independentSigns.expect (fun ζ => rough i ζ ^ 2) = v i)
    (hthird : ∀ i, independentSigns.expect (fun ζ => rough i ζ ^ 3) = 0)
    (hcorrection : ∀ i, ((shift i (owner i) * scale i (owner i)) * jb i * v i) * corr i =
      (shift i (owner i) * scale i (owner i)) ^ 3 * jb i * independentSigns.expect (fun ζ => rough i ζ ^ 4)) :
    independentSigns.expect (fun ζ => Walsh.resampleAverage (Finset.univ.biUnion S) (fun η =>
      blockPolynomialFunctional (fun k => outcomePolynomialFunctional (κ k) (W k) (u k)
        (completedSites (e k) (fun i => scale i.val k * rough i.val ζ) (g k η)) η)
        (blockPolynomialMap (fun k => retainedPolynomialMap (P k) (e k))
          (∏ i, rename (fun k => (k, i))
            (outcomeTaylorPolynomial (R i) (T i) 1 (jb i) (corr i) (smooth i) (rough i ζ)
              (∑ k, C (shift i k) * X k))))) ζ) =
    independentSigns.expect (fun ζ => Walsh.resampleAverage (Finset.univ.biUnion S) (fun η =>
      (∏ k, pointValue (torusProjection (u k))
        (completedSites (e k) (fun i => scale i.val k * rough i.val ζ) (g k η)) η (W k)) *
        ∏ i, (likelihood (R i) (T i) (jb i) (corr i) (smooth i) (rough i ζ) +
          realField (R i) (T i) (smooth i) ((shift i (owner i) * scale i (owner i)) * jb i * v i))) ζ) := by
  have ha (ζ : J → Bool) (k : K) (i : I) (hi : ¬P k i) : scale i k * rough i ζ = 0 := by
    rw [houtside k i hi, zero_mul]
  have hrows (ζ η : J → Bool) (p : MvPolynomial (K × I) ℝ) :=
    blockOutcomeFunctional_retained_map P G e κ (fun k i => scale i k ^ 2 * v i)
      (fun k i => scale i k * rough i ζ) hκ (ha ζ) W u η (fun k => g k η) p
  have hbase (ζ η : J → Bool) (k : K) := pointValue_retained_outcome_rows (P k) (e k)
    (fun i => scale i k * rough i ζ) (W k) (u k) η (g k η)
  simp_rw [hrows, hbase]
  exact resampled_outcome_polynomial_coefficient_matching
    (fun η k r => completedOutcomeRowCoefficient (W k) (u k) η (e k) (g k η) r)
    (fun k r => retainedOutcomeRowDegree (P k) (e k) r.1)
    S hS rough hrough R T jb corr v smooth shift scale owner hscale hmean hvar hthird hcorrection

end CausalLowerbound.PartC
