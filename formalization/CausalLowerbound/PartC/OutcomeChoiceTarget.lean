import CausalLowerbound.PartC.OutcomeSubstitution
import CausalLowerbound.PartC.ShiftChoiceWiener
import CausalLowerbound.PartC.SitePolynomialFunctional

/-! The cubic truncation of the actual virtual-shift expansion. Each
selected site may occur up to three times. The Fourier target acts on
the full degree-three representative array before evaluating signs. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative
variable {Ω K V E d J : Type*} [Fintype Ω] [Fintype K] [DecidableEq K]
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype d] [DecidableEq d]
  [Fintype J] [DecidableEq J]

def outcomeChoiceDegree (s : K → Option V)
    (hs : ∀ i, siteOccurrenceExponent (choiceSite s) i ≤ 3) : Degree V 3 :=
  fun i => ⟨siteOccurrenceExponent (choiceSite s) i, Nat.lt_succ_of_le (hs i)⟩

def outcomeChoiceTarget (k : V → Fourier (V × d)) (L : ℝ) (hL : 1 ≤ L)
    (hk : ∀ i, ‖k i‖ ≤ L) (A : (K → Option V) → Fourier (V × d)) :
    Representative.Array d V J 3 →L[ℝ] Representative.Array d V J 3 :=
  ∑ s : K → Option V, if hs : ∀ i, siteOccurrenceExponent (choiceSite s) i ≤ 3 then
    outcomePattern (outcomeChoiceDegree s hs) k L hL hk (A s) else 0

theorem outcomeChoiceTarget_bound (k : V → Fourier (V × d)) (L : ℝ) (hL : 1 ≤ L)
    (hk : ∀ i, ‖k i‖ ≤ L) (A : (K → Option V) → Fourier (V × d))
    (v : Representative.Array d V J 3) :
    ‖outcomeChoiceTarget k L hL hk A v‖ ≤ ((∑ s, ‖A s‖) * L ^ Fintype.card V) * ‖v‖ := by
  simp only [outcomeChoiceTarget, ContinuousLinearMap.sum_apply]
  apply (norm_sum_le _ _).trans
  simp only [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro s _
  split_ifs with hs
  · exact outcomePattern_bound (outcomeChoiceDegree s hs) k L hL hk (A s) v
  · simp only [ContinuousLinearMap.zero_apply, norm_zero]
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg (zero_le_one.trans hL) _)) (norm_nonneg v)

theorem outcomeChoiceTarget_symbol (k : V → Fourier (V × d)) (L : ℝ) (hL : 1 ≤ L)
    (hk : ∀ i, ‖k i‖ ≤ L) (A : (K → Option V) → Fourier (V × d))
    (v : Representative.Array d V J 3) (j : J) :
    symbolPart j (outcomeChoiceTarget k L hL hk A v) =
      outcomeChoiceTarget k L hL hk A (symbolPart j v) := by
  simp only [outcomeChoiceTarget, ContinuousLinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs
  · exact degreeSubstitution_symbolProject _ _ _ _ (fun S => j ∈ S) v
  · simp

theorem outcomeChoiceTarget_symbol_bound (k : V → Fourier (V × d)) (L : ℝ) (hL : 1 ≤ L)
    (hk : ∀ i, ‖k i‖ ≤ L) (A : (K → Option V) → Fourier (V × d))
    (v : Representative.Array d V J 3) (j : J) :
    ‖symbolPart j (outcomeChoiceTarget k L hL hk A v)‖ ≤
      ((∑ s, ‖A s‖) * L ^ Fintype.card V) * ‖symbolPart j v‖ := by
  rw [outcomeChoiceTarget_symbol]
  exact outcomeChoiceTarget_bound k L hL hk A _

theorem outcomeChoiceTarget_remove (k : V → Fourier (V × d)) (L : ℝ) (hL : 1 ≤ L)
    (hk : ∀ i, ‖k i‖ ≤ L) (A : (K → Option V) → Fourier (V × d))
    (v : Representative.Array d V J 3) (S : Finset J) :
    remove S (outcomeChoiceTarget k L hL hk A v) = outcomeChoiceTarget k L hL hk A (remove S v) := by
  simp only [outcomeChoiceTarget, ContinuousLinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs with hs
  · exact outcomePattern_remove (outcomeChoiceDegree s hs) k L hL hk (A s) v S
  · simp

theorem outcomeChoiceTarget_value (k : V → Fourier (V × d)) (L : ℝ) (hL : 1 ≤ L)
    (hk : ∀ i, ‖k i‖ ≤ L) (A : (K → Option V) → Fourier (V × d))
    (v : Representative.Array d V J 3) (x : Torus (V × d)) (z : V → ℝ) (ζ : J → Bool)
    (hA : ∀ s, (toContinuous (A s) x).im = 0) (hkre : ∀ i, (toContinuous (k i) x).im = 0) :
    pointValue x z ζ (outcomeChoiceTarget k L hL hk A v) =
      ∑ s : K → Option V, if hs : ∀ i, siteOccurrenceExponent (choiceSite s) i ≤ 3 then
        (toContinuous (A s) x).re * ∑ r : Row V J 3,
          Walsh.character r.2 ζ * (toContinuous (v r) x).re *
            ∏ i, outcomeSlotFactor (outcomeChoiceDegree s hs)
              (fun j => (toContinuous (k j) x).re) z r.1 i
        else 0 := by
  simp only [outcomeChoiceTarget, ContinuousLinearMap.sum_apply, pointValue_sum]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs with hs
  · exact outcomePattern_value (outcomeChoiceDegree s hs) k L hL hk (A s) v x z ζ (hA s) hkre
  · exact pointValue_zero x z ζ

def outcomeChoiceValue (a b : E → V) (μ : FiniteLaw Ω) (U : Ω → K → ℝ)
    (ν : K → d × Bool →₀ ℕ) (amp t : ℝ) (κ : V → ℝ) (v : Representative.Array d V J 3)
    (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) : ℝ :=
  ∑ s : K → Option V, if hs : ∀ i, siteOccurrenceExponent (choiceSite s) i ≤ 3 then
    shiftChoiceCoefficient a b μ U ν amp t s u * ∑ r : Row V J 3,
      Walsh.character r.2 ζ * (toContinuous (v r) (torusProjection u)).re *
        ∏ i, outcomeSlotFactor (outcomeChoiceDegree s hs) κ z r.1 i
    else 0

theorem exists_outcomeChoiceTarget (a b : E → V) (μ : FiniteLaw Ω) (U : Ω → K → ℝ)
    (ν : K → d × Bool →₀ ℕ) :
    ∃ C ≥ 0, ∀ (J : Type*) [Fintype J] [DecidableEq J],
      ∀ amp ≥ 0, ∀ t > 0, ∀ L ≥ 1, ∀ (k : V → Fourier (V × d)) (hk : ∀ i, ‖k i‖ ≤ L),
      ∃ T : Representative.Array d V J 3 →L[ℝ] Representative.Array d V J 3,
        (∀ v, ‖T v‖ ≤ ((C * ((levelBudget 2 t + 1 : ℕ) : ℝ) ^ Fintype.card E *
          ∑ j ∈ Finset.Icc 1 (Fintype.card K), (amp / t) ^ j) * L ^ Fintype.card V) * ‖v‖) ∧
        (∀ v S, remove S (T v) = T (remove S v)) ∧
        ∀ v u z ζ, (∀ i, (toContinuous (k i) (torusProjection u)).im = 0) →
          pointValue (torusProjection u) z ζ (T v) =
            outcomeChoiceValue a b μ U ν amp t
              (fun i => (toContinuous (k i) (torusProjection u)).re) v u z ζ := by
  obtain ⟨C, hC, hcoeff⟩ := exists_shiftChoiceWiener a b μ U ν
  refine ⟨C, hC, fun J _ _ amp hamp t ht L hL k hk => ?_⟩
  obtain ⟨A, hA, hn⟩ := hcoeff amp hamp t ht
  refine ⟨outcomeChoiceTarget k L hL hk A, fun v => (outcomeChoiceTarget_bound k L hL hk A v).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn (pow_nonneg (zero_le_one.trans hL) _))
      (norm_nonneg v)), outcomeChoiceTarget_remove k L hL hk A, ?_⟩
  intro v u z ζ hkre
  rw [outcomeChoiceTarget_value k L hL hk A v _ z ζ (fun s => by rw [hA]; rfl) hkre]
  simp only [outcomeChoiceValue, hA, Complex.ofReal_re]

end CausalLowerbound.PartC
