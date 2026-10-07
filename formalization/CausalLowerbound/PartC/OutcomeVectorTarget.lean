import CausalLowerbound.PartC.OutcomeChoiceTarget
import CausalLowerbound.PartC.RepresentativePermutation

/-! The full vector of cubic targets, with contractive symmetrization.
The constant is chosen before the rough-sign type and all scale choices. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative
variable {d V I J : Type*} [Fintype d] [Fintype V] [DecidableEq V]
  [Fintype I] [Fintype J] [DecidableEq J]

def symmetricOutcomeVectorTarget
    (T : I → Representative.Array d V J 3 →L[ℝ] Representative.Array d V J 3) :
    Representative.Array d V J 3 →L[ℝ] (I → Representative.Array d V J 3) :=
  ContinuousLinearMap.pi (fun i => symmetrize.comp (T i))

@[simp] theorem symmetricOutcomeVectorTarget_apply
    (T : I → Representative.Array d V J 3 →L[ℝ] Representative.Array d V J 3)
    (v : Representative.Array d V J 3) (i : I) :
    symmetricOutcomeVectorTarget T v i = symmetrize (T i v) := rfl

theorem symmetricOutcomeVectorTarget_bound
    (T : I → Representative.Array d V J 3 →L[ℝ] Representative.Array d V J 3)
    (δ : ℝ) (hδ : 0 ≤ δ) (hT : ∀ i v, ‖T i v‖ ≤ δ * ‖v‖) (v : Representative.Array d V J 3) :
    ‖symmetricOutcomeVectorTarget T v‖ ≤ δ * ‖v‖ :=
  (pi_norm_le_iff_of_nonneg (mul_nonneg hδ (norm_nonneg v))).mpr
    (fun i => (symmetrize_bound (T i v)).trans (hT i v))

def symmetricOutcomeChoiceValue {Ω K E : Type*} [Fintype Ω] [Fintype K] [DecidableEq K]
    [Fintype E] [DecidableEq E] [DecidableEq d]
    (a b : E → V) (μ : FiniteLaw Ω) (U : Ω → K → ℝ) (ν : K → d × Bool →₀ ℕ)
    (amp t : ℝ) (k : V → Fourier (V × d)) (v : Representative.Array d V J 3)
    (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) : ℝ :=
  (Fintype.card (Equiv.Perm V) : ℝ)⁻¹ * ∑ σ : Equiv.Perm V,
    outcomeChoiceValue a b μ U ν amp t
      (fun i => (toContinuous (k i) (torusProjection (fun p => u (σ p.1, p.2)))).re)
      v (fun p => u (σ p.1, p.2)) (fun i => z (σ i)) ζ

variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq E] [DecidableEq d]
  {K : I → Type*} [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)]

theorem exists_outcomeVectorTarget (a b : E → V) (μ : FiniteLaw Ω)
    (U : ∀ i, Ω → K i → ℝ) (ν : ∀ i, K i → d × Bool →₀ ℕ)
    (D : ℕ) (hD : ∀ i, Fintype.card (K i) ≤ D) :
    ∃ C ≥ 0, ∀ (J : Type*) [Fintype J] [DecidableEq J],
      ∀ amp ≥ 0, ∀ t > 0, ∀ L ≥ 1, ∀ (k : V → Fourier (V × d)) (hk : ∀ i, ‖k i‖ ≤ L),
      ∃ T : Representative.Array d V J 3 →L[ℝ] (I → Representative.Array d V J 3),
        (∀ v, ‖T v‖ ≤ ((C * ((levelBudget 2 t + 1 : ℕ) : ℝ) ^ Fintype.card E *
          ∑ j ∈ Finset.Icc 1 D, (amp / t) ^ j) * L ^ Fintype.card V) * ‖v‖) ∧
        (∀ v i x z ζ (σ : Equiv.Perm V),
          pointValue (permuteSlots σ x) (fun j => z (σ j)) ζ (T v i) = pointValue x z ζ (T v i)) ∧
        (∀ v i S, remove S (T v i) = T (remove S v) i) ∧
        ∀ v i u z ζ, (∀ u i, (toContinuous (k i) (torusProjection u)).im = 0) →
          pointValue (torusProjection u) z ζ (T v i) =
            symmetricOutcomeChoiceValue a b μ (U i) (ν i) amp t k v u z ζ := by
  choose C hC hchoice using fun i => exists_outcomeChoiceTarget a b μ (U i) (ν i)
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), fun J _ _ amp hamp t ht L hL k hk => ?_⟩
  choose T hT hr hv using fun i => hchoice i J amp hamp t ht L hL k hk
  let B : ℝ := ((levelBudget 2 t + 1 : ℕ) : ℝ) ^ Fintype.card E
  let G : ℝ := ∑ j ∈ Finset.Icc 1 D, (amp / t) ^ j
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hG : 0 ≤ G := Finset.sum_nonneg (fun j _ => pow_nonneg (div_nonneg hamp ht.le) j)
  have hLp : 0 ≤ L ^ Fintype.card V := pow_nonneg (zero_le_one.trans hL) _
  have hi (i : I) : C i * B * (∑ j ∈ Finset.Icc 1 (Fintype.card (K i)), (amp / t) ^ j) ≤
      (∑ i, C i) * B * G := by
    have hsum : (∑ j ∈ Finset.Icc 1 (Fintype.card (K i)), (amp / t) ^ j) ≤ G :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl (hD i))
        (fun j _ _ => pow_nonneg (div_nonneg hamp ht.le) j)
    exact (mul_le_mul_of_nonneg_left hsum (mul_nonneg (hC i) hB)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)) hB) hG)
  refine ⟨symmetricOutcomeVectorTarget T, symmetricOutcomeVectorTarget_bound T _
    (mul_nonneg (mul_nonneg (mul_nonneg (Finset.sum_nonneg (fun i _ => hC i)) hB) hG) hLp)
    (fun i v => (hT i v).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hi i) hLp) (norm_nonneg v))), ?_, ?_, ?_⟩
  · intro v i x z ζ σ
    exact symmetrize_value_symmetric (T i v) x z ζ σ
  · intro v i S
    change remove S (symmetrize (T i v)) = symmetrize (T i (remove S v))
    rw [show remove S (symmetrize (T i v)) = symmetrize (remove S (T i v)) from
      symmetrize_symbolProject (T i v) (fun s => Disjoint s S), hr]
  · intro v i u z ζ hkre
    rw [symmetricOutcomeVectorTarget_apply, symmetrize_value]
    unfold symmetricOutcomeChoiceValue
    congr 1
    apply Finset.sum_congr rfl
    intro σ _
    exact hv i v (fun p => u (σ p.1, p.2)) (fun j => z (σ j)) ζ (hkre _)

end CausalLowerbound.PartC
