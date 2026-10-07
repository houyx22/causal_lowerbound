import CausalLowerbound.PartB.IdealIncrementExpansion
import CausalLowerbound.PartB.LagrangeProductWiener

/-! The actual tapered ideal increment, using the actual Lagrange polynomial
coefficients and independent signs, has the inverse-square Wiener estimate. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartB.ShellGeometry

open Wiener ConfigurationShells
variable {Ω K V E d : Type*} [Fintype Ω] [Fintype K] [DecidableEq K]
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype d] [DecidableEq d]

def idealIncrement (a b : E → V) (μ : FiniteLaw Ω) (U : Ω → K → ℝ) (ν : K → d × Bool →₀ ℕ)
    (amp t : ℝ) (u : V × d → ℝ) : ℝ :=
  graphTaper a b taperCutoff t (graphDistance a b u) *
    (idealMonomialMoment μ U (fun k i => lagrangeCoefficient a b i (ν k) u) amp -
      μ.expect (fun ω => ∏ k, U ω k))

theorem idealIncrement_expansion (a b : E → V) (μ : FiniteLaw Ω) (U : Ω → K → ℝ)
    (ν : K → d × Bool →₀ ℕ) (amp t : ℝ) (u : V × d → ℝ) :
    idealIncrement a b μ U ν amp t u =
      ∑ s : K → Option V, (incrementWeight μ U s * amp ^ choiceDegree s) *
        taperedLagrangeProduct a b (choiceSite s) (fun k => ν k.val) t u := by
  rw [idealIncrement, idealMonomialIncrement_expansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  unfold taperedLagrangeProduct
  ring

/-- The shell count is still written as the exact logarithmic ceiling.
Every term starts at degree two; the coefficient and shell estimates are
proved for the concrete functions, with no analytic input assumptions. -/
theorem ideal_increment_wiener_bound (a b : E → V) (μ : FiniteLaw Ω) (U : Ω → K → ℝ)
    (ν : K → d × Bool →₀ ℕ) :
    ∃ C ≥ 0, ∀ amp ≥ 0, ∀ t > 0, ∃ A : Fourier (V × d),
      (∀ u, toContinuous A (torusProjection u) = (idealIncrement a b μ U ν amp t u : ℝ)) ∧
      ‖A‖ ≤ C * ((levelBudget 2 t + 1 : ℕ) : ℝ) ^ Fintype.card E *
        ∑ j ∈ Finset.Icc 2 (Fintype.card K), (amp / t) ^ j := by
  classical
  choose B hB hb using fun s : K → Option V =>
    tapered_lagrange_product_wiener a b (choiceSite s) (fun k => ν k.val)
  let w : (K → Option V) → ℝ := incrementWeight μ U
  let c : (K → Option V) → ℝ := fun s => |w s| * B s * ((2 : ℝ) ^ Fintype.card E) ^ choiceDegree s
  let C : ℝ := ∑ s, c s
  have hc (s : K → Option V) : 0 ≤ c s :=
    mul_nonneg (mul_nonneg (abs_nonneg _) (hB s)) (by positivity)
  refine ⟨C, Finset.sum_nonneg (fun s _ => hc s), ?_⟩
  intro amp hamp t ht
  let L : ℝ := ((levelBudget 2 t + 1 : ℕ) : ℝ) ^ Fintype.card E
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let G : ℝ := ∑ j ∈ Finset.Icc 2 (Fintype.card K), (amp / t) ^ j
  have hG : 0 ≤ G := Finset.sum_nonneg (fun _ _ => pow_nonneg (div_nonneg hamp ht.le) _)
  obtain ⟨A, hA, hn⟩ := finite_real_combination_wiener (fun s => w s * amp ^ choiceDegree s)
    (fun s => taperedLagrangeProduct a b (choiceSite s) (fun k => ν k.val) t)
    (fun s => B s * L * ((2 : ℝ) ^ Fintype.card E / t) ^ choiceDegree s) (fun s => hb s t ht)
  refine ⟨A, ?_, ?_⟩
  · intro u
    rw [hA, idealIncrement_expansion]
  · have he (s : K → Option V) :
        |w s * amp ^ choiceDegree s| * (B s * L * ((2 : ℝ) ^ Fintype.card E / t) ^ choiceDegree s) =
          c s * L * (amp / t) ^ choiceDegree s := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg hamp _)]
      simp only [c, div_pow]
      ring
    simp only [he] at hn
    apply hn.trans
    calc
      (∑ s, c s * L * (amp / t) ^ choiceDegree s) ≤ ∑ s, c s * L * G := by
        apply Finset.sum_le_sum
        intro s _
        by_cases hw : w s = 0
        · simp [c, hw]
        · apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hc s) hL)
          apply Finset.single_le_sum (fun j _ => pow_nonneg (div_nonneg hamp ht.le) j)
          exact Finset.mem_Icc.mpr ⟨incrementWeight_nonzero_degree μ U s hw, choiceDegree_le s⟩
      _ = C * L * G := by dsimp [C]; rw [Finset.sum_mul, Finset.sum_mul]

end CausalLowerbound.PartB.ShellGeometry
