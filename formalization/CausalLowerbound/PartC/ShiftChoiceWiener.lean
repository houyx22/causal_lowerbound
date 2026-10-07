import CausalLowerbound.PartC.PolynomialShiftExpansion
import CausalLowerbound.PartB.LagrangeProductWiener

/-! Actual Wiener coefficients of the unaveraged virtual shift. The
estimate starts at degree one and keeps every choice of shift sites, so
degree truncation can be performed after constructing the coefficients. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC

open PartB PartB.ShellGeometry Wiener ConfigurationShells

variable {Ω K V E d : Type*} [Fintype Ω] [Fintype K] [DecidableEq K]
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype d] [DecidableEq d]

def shiftChoiceCoefficient (a b : E → V) (μ : FiniteLaw Ω) (U : Ω → K → ℝ)
    (ν : K → d × Bool →₀ ℕ) (amp t : ℝ) (s : K → Option V) (u : V × d → ℝ) : ℝ :=
  (shiftChoiceWeight μ U s * amp ^ choiceDegree s) *
    taperedLagrangeProduct a b (choiceSite s) (fun k => ν k.val) t u

theorem exists_shiftChoiceWiener (a b : E → V) (μ : FiniteLaw Ω) (U : Ω → K → ℝ)
    (ν : K → d × Bool →₀ ℕ) :
    ∃ C ≥ 0, ∀ amp ≥ 0, ∀ t > 0, ∃ A : (K → Option V) → Fourier (V × d),
      (∀ s u, toContinuous (A s) (torusProjection u) = (shiftChoiceCoefficient a b μ U ν amp t s u : ℂ)) ∧
      (∑ s, ‖A s‖) ≤ C * ((levelBudget 2 t + 1 : ℕ) : ℝ) ^ Fintype.card E *
        ∑ j ∈ Finset.Icc 1 (Fintype.card K), (amp / t) ^ j := by
  choose B hB hb using fun s : K → Option V =>
    tapered_lagrange_product_wiener a b (choiceSite s) (fun k => ν k.val)
  let w : (K → Option V) → ℝ := shiftChoiceWeight μ U
  let c : (K → Option V) → ℝ := fun s => |w s| * B s * ((2 : ℝ) ^ Fintype.card E) ^ choiceDegree s
  let C : ℝ := ∑ s, c s
  have hc (s : K → Option V) : 0 ≤ c s :=
    mul_nonneg (mul_nonneg (abs_nonneg _) (hB s)) (by positivity)
  refine ⟨C, Finset.sum_nonneg (fun s _ => hc s), fun amp hamp t ht => ?_⟩
  choose F hF hn using fun s => hb s t ht
  let A (s : K → Option V) : Fourier (V × d) := (w s * amp ^ choiceDegree s) • F s
  let L : ℝ := ((levelBudget 2 t + 1 : ℕ) : ℝ) ^ Fintype.card E
  let G : ℝ := ∑ j ∈ Finset.Icc 1 (Fintype.card K), (amp / t) ^ j
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hG : 0 ≤ G := Finset.sum_nonneg (fun _ _ => pow_nonneg (div_nonneg hamp ht.le) _)
  have hA (s : K → Option V) : ‖A s‖ ≤ c s * L * (amp / t) ^ choiceDegree s := by
    calc
      ‖A s‖ = |w s * amp ^ choiceDegree s| * ‖F s‖ := by simp only [A, norm_smul, Real.norm_eq_abs]
      _ ≤ |w s * amp ^ choiceDegree s| *
          (B s * L * ((2 : ℝ) ^ Fintype.card E / t) ^ choiceDegree s) :=
        mul_le_mul_of_nonneg_left (hn s) (abs_nonneg _)
      _ = _ := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg hamp _)]
        simp only [c, div_pow]
        ring
  refine ⟨A, fun s u => ?_, ?_⟩
  · simp only [A, shiftChoiceCoefficient, w, toContinuous_real_smul, ContinuousMap.smul_apply,
      hF s u, Complex.real_smul, Complex.ofReal_mul]
  · apply (Finset.sum_le_sum (fun s _ => hA s)).trans
    calc
      (∑ s, c s * L * (amp / t) ^ choiceDegree s) ≤ ∑ s, c s * L * G := by
        apply Finset.sum_le_sum
        intro s _
        by_cases hw : w s = 0
        · simp [c, hw]
        · apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hc s) hL)
          exact Finset.single_le_sum (fun j _ => pow_nonneg (div_nonneg hamp ht.le) j)
            (Finset.mem_Icc.mpr ⟨shiftChoiceWeight_nonzero_degree μ U s hw, choiceDegree_le s⟩)
      _ = C * L * G := by simp only [C, Finset.sum_mul]

end CausalLowerbound.PartC
