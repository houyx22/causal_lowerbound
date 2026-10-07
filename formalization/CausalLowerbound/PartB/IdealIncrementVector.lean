import CausalLowerbound.PartB.IdealIncrementSymmetry
import CausalLowerbound.PartB.CompleteEdgeCard
import CausalLowerbound.PartB.PositiveWienerComplete

/-! Finite vectors of actual ideal moments. The Wiener estimate and positive
polarization are now linked without a supplied analytic estimate. Only the
finite moment data, which belong to the model construction, remain inputs. -/

noncomputable section
set_option autoImplicit false
open Filter
open scoped BigOperators Topology

namespace CausalLowerbound.PartB.ShellGeometry
open Wiener

variable {Ω I V d : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
  [Fintype V] [LinearOrder V] [Fintype d] [DecidableEq d]
  {K : I → Type*} [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)]

def idealMomentVector (μ : FiniteLaw Ω) (U : ∀ i, Ω → K i → ℝ)
    (ν : ∀ i, K i → d × Bool →₀ ℕ) (p B : ℝ) (n : ℕ) : I → SymmetricReal d V :=
  fun i => symmetricIdealSequence μ (U i) (ν i) p B n

theorem idealMomentVector_log_bound (μ : FiniteLaw Ω) (U : ∀ i, Ω → K i → ℝ)
    (ν : ∀ i, K i → d × Bool →₀ ℕ) (D : ℕ) (hD : ∀ i, Fintype.card (K i) ≤ D) :
    ∃ C ≥ 0, ∀ p B (n : ℕ), logarithmicThreshold p B (n + 1) ≤ 1 →
      ‖idealMomentVector (V := V) μ U ν p B n‖ ≤
        C * (1 + Real.log (1 / logarithmicThreshold p B (n + 1))) ^ Fintype.card (CompleteEdge V) *
          ∑ j ∈ Finset.Icc 2 D, (polynomialAmplitude p (n + 1) / logarithmicThreshold p B (n + 1)) ^ j := by
  choose C hC hb using fun i => idealWiener_log_bound (V := V) edgeLeft edgeRight μ (U i) (ν i)
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro p B n ht1
  have hx : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have ht := logarithmicThreshold_pos p B hx
  have hamp := (polynomialAmplitude_pos p (by positivity : (0 : ℝ) < (n : ℝ) + 1)).le
  let r := polynomialAmplitude p (n + 1) / logarithmicThreshold p B (n + 1)
  let L := (1 + Real.log (1 / logarithmicThreshold p B (n + 1))) ^ Fintype.card (CompleteEdge V)
  let G := ∑ j ∈ Finset.Icc 2 D, r ^ j
  have hr : 0 ≤ r := div_nonneg hamp ht.le
  have hl : 0 ≤ L := by
    have := Real.log_nonneg ((le_div_iff₀ ht).mpr (by simpa using ht1))
    exact pow_nonneg (by linarith) _
  have hg : 0 ≤ G := Finset.sum_nonneg (fun j _ => pow_nonneg hr j)
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg
    (mul_nonneg (Finset.sum_nonneg (fun i _ => hC i)) hl) hg)).mpr
  intro i
  have hs : (∑ j ∈ Finset.Icc 2 (Fintype.card (K i)), r ^ j) ≤ G :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl (hD i))
      (fun j _ _ => pow_nonneg hr j)
  exact (hb i _ hamp _ ht ht1).trans ((mul_le_mul_of_nonneg_left hs (mul_nonneg (hC i) hl)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)) hl) hg))

theorem idealMomentVector_rate (μ : FiniteLaw Ω) (U : ∀ i, Ω → K i → ℝ)
    (ν : ∀ i, K i → d × Bool →₀ ℕ) (p B : ℝ) (hp : 0 < p) (hB : 0 ≤ B) :
    ∃ C ≥ 0, ∀ᶠ n : ℕ in atTop,
      ‖idealMomentVector (V := V) μ U ν p B n‖ ≤
        C * logScale (n + 1) ^ ((Fintype.card (CompleteEdge V) : ℝ) - 2 * B) := by
  choose C hC hb using fun i => idealWienerSequence_rate (V := V) edgeLeft edgeRight μ (U i) (ν i) p B hp hB
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  have hall : ∀ᶠ n : ℕ in atTop, ∀ i, ‖idealWienerSequence (V := V) edgeLeft edgeRight μ (U i) (ν i) p B n‖ ≤
      C i * logScale (n + 1) ^ ((Fintype.card (CompleteEdge V) : ℝ) - 2 * B) :=
    (eventually_all).mpr hb
  filter_upwards [hall] with n hn
  have hΛ := (logScale_pos (le_add_of_nonneg_left (Nat.cast_nonneg n) : (1 : ℝ) ≤ (n : ℝ) + 1)).le
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Finset.sum_nonneg (fun i _ => hC i))
    (Real.rpow_nonneg hΛ _))).mpr
  intro i
  exact (hn i).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)) (Real.rpow_nonneg hΛ _))

theorem idealMomentVector_norm_tendsto (μ : FiniteLaw Ω) (U : ∀ i, Ω → K i → ℝ)
    (ν : ∀ i, K i → d × Bool →₀ ℕ) (p B : ℝ) (hp : 0 < p)
    (hB : (Fintype.card (CompleteEdge V) : ℝ) < 2 * B) :
    Tendsto (fun n => ‖idealMomentVector (V := V) μ U ν p B n‖) atTop (𝓝 0) := by
  have hB0 : 0 ≤ B := by have := Nat.cast_nonneg (α := ℝ) (Fintype.card (CompleteEdge V)); linarith
  obtain ⟨C, _, hb⟩ := idealMomentVector_rate (V := V) μ U ν p B hp hB0
  have hx : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith) tendsto_natCast_atTop_atTop
  have hlim := ((logarithmic_majorant_tendsto (Fintype.card (CompleteEdge V)) B hB).comp hx).const_mul C
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hb
  simpa using hlim

/-- Both analytic inputs from the earlier conditional carrier theorem have
been discharged: the ideal increment is concrete, and the polarization is
the explicit positive Wiener dictionary. -/
theorem actual_ideal_eventually_positiveCarrier [Nonempty V]
    (μ : FiniteLaw Ω) (U : ∀ i, Ω → K i → ℝ) (ν : ∀ i, K i → d × Bool →₀ ℕ)
    (p B : ℝ) (hp : 0 < p) (hB : (Fintype.card (CompleteEdge V) : ℝ) < 2 * B)
    (feature : I → Ω → ℝ) (hμ : ∀ ω, 0 < μ.weight ω) (R : MomentRightInverse feature) :
    ∀ᶠ n in atTop, HasPositiveCarrier 1 (PositiveWiener.naturalAtom (d := d) (ι := V) (1 / 4))
      (multiplicationIncrement (idealMomentVector (V := V) μ U ν p B n)) feature μ :=
  PositiveWiener.eventually_hasPositiveWienerCarrier
    (idealMomentVector (V := V) μ U ν p B) (fun n => ‖idealMomentVector (V := V) μ U ν p B n‖)
    (fun _ => norm_nonneg _) (idealMomentVector_norm_tendsto μ U ν p B hp hB)
    (fun _ => le_rfl) feature μ hμ R

end CausalLowerbound.PartB.ShellGeometry
