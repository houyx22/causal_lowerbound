import CausalLowerbound.PartC.PropensityChoiceTarget
import CausalLowerbound.PartC.RepresentativePermutation
import CausalLowerbound.PartB.IdealIncrementLogBound

/-! A finite vector of actual design-weighted targets, followed by a
contractive symmetrization. Constants are chosen before the rough-sign
type, so the same bound applies when its size grows with sample size. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC

open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative

variable {d V I J : Type*} [Fintype d] [Fintype V] [DecidableEq V]
  [Fintype I] [Fintype J] [DecidableEq J]

def symmetricVectorTarget (T : I → Representative.Array d V J 1 →L[ℝ] Representative.Array d V J 1) :
    Representative.Array d V J 1 →L[ℝ] (I → Representative.Array d V J 1) :=
  ContinuousLinearMap.pi (fun i => symmetrize.comp (T i))

@[simp] theorem symmetricVectorTarget_apply
    (T : I → Representative.Array d V J 1 →L[ℝ] Representative.Array d V J 1)
    (v : Representative.Array d V J 1) (i : I) : symmetricVectorTarget T v i = symmetrize (T i v) := rfl

theorem symmetricVectorTarget_bound
    (T : I → Representative.Array d V J 1 →L[ℝ] Representative.Array d V J 1)
    (δ : ℝ) (hδ : 0 ≤ δ) (hT : ∀ i v, ‖T i v‖ ≤ δ * ‖v‖) (v : Representative.Array d V J 1) :
    ‖symmetricVectorTarget T v‖ ≤ δ * ‖v‖ :=
  (pi_norm_le_iff_of_nonneg (mul_nonneg hδ (norm_nonneg v))).mpr
    (fun i => (symmetrize_bound (T i v)).trans (hT i v))

def symmetricPropensityChoiceValue {Ω K E : Type*} [Fintype Ω] [Fintype K] [DecidableEq K]
    [Fintype E] [DecidableEq E] [DecidableEq d]
    (a b : E → V) (μ : FiniteLaw Ω) (U : Ω → K → ℝ) (ν : K → d × Bool →₀ ℕ)
    (amp t : ℝ) (k : V → Fourier (V × d)) (v : Representative.Array d V J 1)
    (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) : ℝ :=
  (Fintype.card (Equiv.Perm V) : ℝ)⁻¹ * ∑ σ : Equiv.Perm V,
    propensityChoiceValue a b μ U ν amp t
      (fun i => (toContinuous (k i) (torusProjection (fun p => u (σ p.1, p.2)))).re)
      v (fun p => u (σ p.1, p.2)) (fun i => z (σ i)) ζ

variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq E] [DecidableEq d]
  {K : I → Type*} [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)]

theorem exists_propensityVectorTarget (a b : E → V) (μ : FiniteLaw Ω)
    (U : ∀ i, Ω → K i → ℝ) (ν : ∀ i, K i → d × Bool →₀ ℕ)
    (D : ℕ) (hD : ∀ i, Fintype.card (K i) ≤ D) :
    ∃ C ≥ 0, ∀ (J : Type*) [Fintype J] [DecidableEq J],
      ∀ amp ≥ 0, ∀ t > 0, ∀ (k : V → Fourier (V × d)) (hk : ∀ i, ‖k i‖ ≤ 1),
      ∃ T : Representative.Array d V J 1 →L[ℝ] (I → Representative.Array d V J 1),
        (∀ v, ‖T v‖ ≤ (C * ((levelBudget 2 t + 1 : ℕ) : ℝ) ^ Fintype.card E *
          ∑ j ∈ Finset.Icc 1 D, (amp / t) ^ j) * ‖v‖) ∧
        (∀ v i x z ζ (σ : Equiv.Perm V),
          pointValue (permuteSlots σ x) (fun j => z (σ j)) ζ (T v i) = pointValue x z ζ (T v i)) ∧
        (∀ v i S, remove S (T v i) = T (remove S v) i) ∧
        ∀ v i u z ζ, (∀ u i, (toContinuous (k i) (torusProjection u)).im = 0) →
          pointValue (torusProjection u) z ζ (T v i) =
            symmetricPropensityChoiceValue a b μ (U i) (ν i) amp t k v u z ζ := by
  choose C hC hchoice using fun i => exists_propensityChoiceTarget a b μ (U i) (ν i)
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), fun J _ _ amp hamp t ht k hk => ?_⟩
  choose T hT hr hv using fun i => hchoice i J amp hamp t ht k hk
  let L : ℝ := ((levelBudget 2 t + 1 : ℕ) : ℝ) ^ Fintype.card E
  let G : ℝ := ∑ j ∈ Finset.Icc 1 D, (amp / t) ^ j
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hG : 0 ≤ G := Finset.sum_nonneg (fun j _ => pow_nonneg (div_nonneg hamp ht.le) j)
  have hi (i : I) : C i * L * (∑ j ∈ Finset.Icc 1 (Fintype.card (K i)), (amp / t) ^ j) ≤
      (∑ i, C i) * L * G := by
    have hsum : (∑ j ∈ Finset.Icc 1 (Fintype.card (K i)), (amp / t) ^ j) ≤ G :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl (hD i))
        (fun j _ _ => pow_nonneg (div_nonneg hamp ht.le) j)
    exact (mul_le_mul_of_nonneg_left hsum (mul_nonneg (hC i) hL)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)) hL) hG)
  refine ⟨symmetricVectorTarget T, symmetricVectorTarget_bound T _
    (mul_nonneg (mul_nonneg (Finset.sum_nonneg (fun i _ => hC i)) hL) hG)
    (fun i v => (hT i v).trans (mul_le_mul_of_nonneg_right (hi i) (norm_nonneg v))), ?_, ?_, ?_⟩
  · intro v i x z ζ σ
    exact symmetrize_value_symmetric (T i v) x z ζ σ
  · intro v i S
    change remove S (symmetrize (T i v)) = symmetrize (T i (remove S v))
    rw [show remove S (symmetrize (T i v)) = symmetrize (remove S (T i v)) from
      symmetrize_symbolProject (T i v) (fun s => Disjoint s S), hr]
  · intro v i u z ζ hkre
    rw [symmetricVectorTarget_apply, symmetrize_value]
    unfold symmetricPropensityChoiceValue
    congr 1
    apply Finset.sum_congr rfl
    intro σ _
    exact hv i v (fun p => u (σ p.1, p.2)) (fun j => z (σ j)) ζ (hkre _)

theorem positive_power_sum_bound (D : ℕ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    (∑ j ∈ Finset.Icc 1 D, r ^ j) ≤ (D : ℝ) * r := by
  calc
    _ ≤ ∑ _j ∈ Finset.Icc 1 D, r := Finset.sum_le_sum (fun j hj => by
      simpa only [pow_one] using pow_le_pow_of_le_one hr hr1 (Finset.mem_Icc.mp hj).1)
    _ = (D : ℝ) * r := by simp [Nat.card_Icc]

/-- The analytic target is first order in the normalized amplitude/taper
ratio. All dimension dependence is in a fixed logarithmic power. -/
theorem propensity_target_majorant (C : ℝ) (hC : 0 ≤ C) (D : ℕ) (amp t : ℝ)
    (hamp : 0 ≤ amp) (ht : 0 < t) (ht1 : t ≤ 1) (hr : amp / t ≤ 1) :
    C * ((levelBudget 2 t + 1 : ℕ) : ℝ) ^ Fintype.card E *
      (∑ j ∈ Finset.Icc 1 D, (amp / t) ^ j) ≤
        (C * logShellConstant ^ Fintype.card E * D) *
          (1 + Real.log (1 / t)) ^ Fintype.card E * (amp / t) := by
  have hL := pow_le_pow_left₀ (by positivity : 0 ≤ ((levelBudget 2 t + 1 : ℕ) : ℝ))
    (levelBudget_log_bound t ht ht1) (Fintype.card E)
  have hsum := positive_power_sum_bound D (amp / t) (div_nonneg hamp ht.le) hr
  calc
    _ ≤ C * (logShellConstant * (1 + Real.log (1 / t))) ^ Fintype.card E *
        ((D : ℝ) * (amp / t)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hL hC) hsum
        (Finset.sum_nonneg (fun j _ => pow_nonneg (div_nonneg hamp ht.le) j))
        (by
          have := Real.log_nonneg ((le_div_iff₀ ht).mpr (by simpa using ht1))
          have := logShellConstant_pos
          positivity)
    _ = _ := by rw [mul_pow]; ring

end CausalLowerbound.PartC
