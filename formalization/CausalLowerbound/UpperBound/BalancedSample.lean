import CausalLowerbound.UpperBound.EmpiricalStatistics

/-! Disjoint equal-sized role groups selected from the original n iid
observations.  At most one incomplete block is discarded.  Selection has
exactly the product law used by the tuple-statistic variance proof. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.UpperBound

def balancedGroupSize (I : Type*) [Fintype I] (n : ℕ) : ℕ := n / Fintype.card I

variable (I : Type*) [Fintype I]

theorem balancedSample_card_le (n : ℕ) :
    Fintype.card (Σ _ : I, Fin (balancedGroupSize I n)) ≤ n := by
  simpa [Fintype.card_sigma, balancedGroupSize, Nat.mul_comm] using
    Nat.div_mul_le_self n (Fintype.card I)

def balancedSampleIndex (n : ℕ) : (Σ _ : I, Fin (balancedGroupSize I n)) ↪ Fin n :=
  (Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb (balancedSample_card_le I n))

def balancedSample {Z : Type*} (n : ℕ) (z : Fin n → Z) :
    (Σ _ : I, Fin (balancedGroupSize I n)) → Z := z ∘ balancedSampleIndex I n

theorem balancedSample_measurePreserving {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving (balancedSample I (Z := Z) n) (Measure.pi (fun _ : Fin n => μ))
      (Measure.pi (fun _ : Σ _ : I, Fin (balancedGroupSize I n) => μ)) :=
  measurePreserving_coordinateSelection μ (balancedSampleIndex I n) (balancedSampleIndex I n).injective

theorem balancedSample_measurable {Z : Type*} [MeasurableSpace Z] (n : ℕ) :
    Measurable (balancedSample I (Z := Z) n) :=
  measurable_pi_lambda _ (fun i => measurable_pi_apply (balancedSampleIndex I n i))

theorem integral_balancedSample {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ)
    {f : ((Σ _ : I, Fin (balancedGroupSize I n)) → Z) → ℝ}
    (hf : AEStronglyMeasurable f (Measure.pi (fun _ : Σ _ : I, Fin (balancedGroupSize I n) => μ))) :
    (∫ z, f (balancedSample I n z) ∂Measure.pi (fun _ : Fin n => μ)) =
      ∫ z, f z ∂Measure.pi (fun _ : Σ _ : I, Fin (balancedGroupSize I n) => μ) :=
  integral_comp_measurePreserving (balancedSample_measurePreserving I μ n) hf

variable [Nonempty I]

theorem balancedGroupSize_pos {n : ℕ} (hn : Fintype.card I ≤ n) :
    0 < balancedGroupSize I n := Nat.div_pos hn Fintype.card_pos

theorem balancedGroupSize_lower {n : ℕ} (hn : Fintype.card I ≤ n) :
    n ≤ 2 * Fintype.card I * balancedGroupSize I n := by
  have hm := balancedGroupSize_pos I hn
  have he := Nat.lt_div_mul_add (a := n) (b := Fintype.card I) Fintype.card_pos
  have hk : Fintype.card I ≤ balancedGroupSize I n * Fintype.card I := by
    simpa using Nat.mul_le_mul_right (Fintype.card I) hm
  change n < balancedGroupSize I n * Fintype.card I + Fintype.card I at he
  nlinarith

theorem balancedGroupSize_inv_le {n : ℕ} (hn : Fintype.card I ≤ n) :
    (Fintype.card (Fin (balancedGroupSize I n)) : ℝ)⁻¹ ≤ 2 * Fintype.card I / n := by
  have hm : (0 : ℝ) < balancedGroupSize I n := by exact_mod_cast balancedGroupSize_pos I hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (Fintype.card_pos.trans_le hn)
  rw [Fintype.card_fin, ← one_div]
  apply (div_le_div_iff₀ hm hn').mpr
  simp only [one_mul]
  exact_mod_cast balancedGroupSize_lower I hn

end CausalLowerbound.UpperBound
