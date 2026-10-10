import CausalLowerbound.UpperBound.CompletionProbability

/-! Summing all nonempty overlap patterns.  If the reciprocal role-group size
is controlled by the coarse cell volume, the extra fixed auxiliary roles
only enter a finite constant; the two leading terms are linear and quadratic
in the reciprocal group size. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators Classical

namespace CausalLowerbound.UpperBound

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {J : I → Type*} [∀ i, Fintype (J i)] [∀ i, Nonempty (J i)]

theorem overlapWeight_le_product (S : Finset I) :
    overlapWeight J S ≤ ∏ i ∈ S, (Fintype.card (J i) : ℝ)⁻¹ := by
  rw [overlapWeight_eq_product]
  calc
    _ ≤ ∏ i : I, if i ∈ S then (Fintype.card (J i) : ℝ)⁻¹ else 1 := by
      apply Finset.prod_le_prod
      · intro i _
        have hc : (1 : ℝ) ≤ Fintype.card (J i) := by exact_mod_cast Fintype.card_pos (α := J i)
        have hi : (Fintype.card (J i) : ℝ)⁻¹ ≤ 1 := by simpa using inv_anti₀ zero_lt_one hc
        split
        · positivity
        · exact sub_nonneg.mpr hi
      · intro i _
        split <;> simp only [le_refl, sub_le_self_iff, inv_nonneg, Nat.cast_nonneg]
    _ = _ := by simp

theorem overlapWeight_le_pow (S : Finset I) {η : ℝ}
    (hη : ∀ i, (Fintype.card (J i) : ℝ)⁻¹ ≤ η) :
    overlapWeight J S ≤ η ^ S.card := by
  apply (overlapWeight_le_product (J := J) S).trans
  calc
    _ ≤ ∏ _i ∈ S, η := Finset.prod_le_prod (fun _ _ => by positivity) (fun i _ => hη i)
    _ = _ := by simp

theorem overlap_power_bound (j m t k : ℕ) (hkj : k ≤ j)
    {η U C B : ℝ} (hη : 0 ≤ η) (hU : 0 ≤ U) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hηC : η ≤ B * C) (hUB : U ≤ B) :
    η ^ j * U ^ m * C ^ t ≤ η ^ k * B ^ (j - k + m) * C ^ (j - k + t) := by
  have hsplit : j = k + (j - k) := (Nat.add_sub_of_le hkj).symm
  calc
    _ = η ^ k * (η ^ (j - k) * U ^ m) * C ^ t := by
      conv_lhs => rw [hsplit, pow_add]
      ring
    _ ≤ η ^ k * ((B * C) ^ (j - k) * B ^ m) * C ^ t := by gcongr
    _ = _ := by rw [pow_add, pow_add, mul_pow]; ring

variable {d : Type*} [Fintype d]

theorem stencilCompletionProbabilityBound_eq (upper : ℝ) (hU : 0 ≤ upper)
    (p : ℕ) (T : StencilTemplate d p) (ℓ r : ℝ) (S : Finset (StencilRole d p)) :
    stencilCompletionProbabilityBound upper p T ℓ r S =
      upper ^ Fintype.card {i // i ∉ S} *
        (if some none ∈ S ∧ none ∈ S then
          (coarseCellVolume p T r).toReal ^ Fintype.card {i // i ∉ S}
        else (fineCellVolume d ℓ).toReal *
          (coarseCellVolume p T r).toReal ^ (Fintype.card {i // i ∉ S} - 1)) := by
  rw [stencilCompletionProbabilityBound, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hU]
  unfold stencilCompletionVolumeBound
  split <;> simp only [ENNReal.toReal_mul, ENNReal.toReal_pow]

theorem stencilOverlap_term_le (p : ℕ) (T : StencilTemplate d p) (ℓ r : ℝ)
    {upper η B : ℝ} (hU : 0 ≤ upper) (hη : 0 ≤ η) (hB : 1 ≤ B)
    (hUB : upper ≤ B) (hηC : η ≤ B * (coarseCellVolume p T r).toReal)
    (S : Finset (StencilRole d p)) (hS : S.Nonempty) :
    η ^ S.card * stencilCompletionProbabilityBound upper p T ℓ r S ≤
      B ^ Fintype.card (StencilRole d p) *
        (coarseCellVolume p T r).toReal ^ (Fintype.card (StencilRole d p) - 2) *
        (η * (fineCellVolume d ℓ).toReal + η ^ 2) := by
  let N := Fintype.card (StencilRole d p)
  let m := Fintype.card {i // i ∉ S}
  let C := (coarseCellVolume p T r).toReal
  let L := (fineCellVolume d ℓ).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have hB₀ : 0 ≤ B := zero_le_one.trans hB
  have hm : S.card + m = N := by
    dsimp [m, N]
    simp only [Fintype.card_subtype_compl, Fintype.card_coe]
    exact Nat.add_sub_of_le (Finset.card_le_univ S)
  rw [stencilCompletionProbabilityBound_eq upper hU]
  by_cases hab : some none ∈ S ∧ none ∈ S
  · rw [if_pos hab]
    have hj : 2 ≤ S.card := by
      have hp : ({some none, none} : Finset (StencilRole d p)) ⊆ S := by
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hab.1
        · exact (Finset.mem_singleton.mp hi) ▸ hab.2
      simpa using Finset.card_le_card hp
    have he : S.card - 2 + m = N - 2 := by omega
    have ht := overlap_power_bound S.card m m 2 hj hη hU hC hB₀ hηC hUB
    rw [he] at ht
    change η ^ S.card * (upper ^ m * C ^ m) ≤ B ^ N * C ^ (N - 2) * (η * L + η ^ 2)
    calc
      _ = η ^ S.card * upper ^ m * C ^ m := by ring
      _ ≤ η ^ 2 * B ^ (N - 2) * C ^ (N - 2) := ht
      _ ≤ η ^ 2 * B ^ N * C ^ (N - 2) := by
        gcongr
        · exact hB
        · exact Nat.sub_le _ _
      _ = B ^ N * C ^ (N - 2) * η ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (mul_nonneg hη hL))
        (mul_nonneg (pow_nonneg hB₀ _) (pow_nonneg hC _))
  · rw [if_neg hab]
    have hj : 1 ≤ S.card := hS.card_pos
    have hmpos : 1 ≤ m := by
      have hx : ∃ i : StencilRole d p, i ∉ S := by
        by_cases ha : some none ∈ S
        · exact ⟨none, fun hb => hab ⟨ha, hb⟩⟩
        · exact ⟨some none, ha⟩
      obtain ⟨i, hi⟩ := hx
      exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
    have heB : S.card - 1 + m = N - 1 := by omega
    have heC : S.card - 1 + (m - 1) = N - 2 := by omega
    have ht := overlap_power_bound S.card m (m - 1) 1 hj hη hU hC hB₀ hηC hUB
    rw [heB, heC, pow_one] at ht
    change η ^ S.card * (upper ^ m * (L * C ^ (m - 1))) ≤
      B ^ N * C ^ (N - 2) * (η * L + η ^ 2)
    calc
      _ = L * (η ^ S.card * upper ^ m * C ^ (m - 1)) := by ring
      _ ≤ L * (η * B ^ (N - 1) * C ^ (N - 2)) := mul_le_mul_of_nonneg_left ht hL
      _ ≤ L * (η * B ^ N * C ^ (N - 2)) := by
        gcongr
        · exact hB
        · exact Nat.sub_le _ _
      _ = B ^ N * C ^ (N - 2) * (η * L) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg η))
        (mul_nonneg (pow_nonneg hB₀ _) (pow_nonneg hC _))

theorem stencilOverlap_sum_le (p : ℕ) (T : StencilTemplate d p) (ℓ r : ℝ)
    (J : StencilRole d p → Type*) [∀ i, Fintype (J i)] [∀ i, Nonempty (J i)]
    {upper η B : ℝ} (hU : 0 ≤ upper) (hη : 0 ≤ η) (hB : 1 ≤ B)
    (hUB : upper ≤ B) (hηC : η ≤ B * (coarseCellVolume p T r).toReal)
    (hJ : ∀ i, (Fintype.card (J i) : ℝ)⁻¹ ≤ η) :
    (∑ S ∈ Finset.univ.erase (∅ : Finset (StencilRole d p)),
      overlapWeight J S * stencilCompletionProbabilityBound upper p T ℓ r S) ≤
      (2 : ℝ) ^ Fintype.card (StencilRole d p) * B ^ Fintype.card (StencilRole d p) *
        (coarseCellVolume p T r).toReal ^ (Fintype.card (StencilRole d p) - 2) *
        (η * (fineCellVolume d ℓ).toReal + η ^ 2) := by
  let A := B ^ Fintype.card (StencilRole d p) *
    (coarseCellVolume p T r).toReal ^ (Fintype.card (StencilRole d p) - 2) *
    (η * (fineCellVolume d ℓ).toReal + η ^ 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  calc
    _ ≤ ∑ S ∈ Finset.univ.erase (∅ : Finset (StencilRole d p)), A := by
      apply Finset.sum_le_sum
      intro S hS
      apply (mul_le_mul_of_nonneg_right (overlapWeight_le_pow S hJ)
        (stencilCompletionProbabilityBound_nonneg upper p T ℓ r S)).trans
      exact stencilOverlap_term_le p T ℓ r hU hη hB hUB hηC S
        (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hS).1)
    _ ≤ ∑ _S : Finset (StencilRole d p), A :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ => hA)
    _ = _ := by simp [A, mul_assoc, Fintype.card_finset]

namespace RealOutcomeModel

variable {ε lower upper M₂ : ℝ} (M : RealOutcomeModel d ε lower upper M₂)

theorem stencil_variance_le_overlap_sum (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (hr : 0 < r)
    (J : StencilRole d p → Type*) [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]
    [∀ i, Nonempty (J i)] {K : (StencilRole d p → (d → ℝ) × (Bool × ℝ)) → ℝ}
    (hK : MemLp K 2 (M.sampleLaw (StencilRole d p)))
    (hs : ∀ z, z ∉ acceptedObservationStencil p T x₀ h ℓ r → K z = 0) :
    variance (Measure.pi (fun _ : Σ i, J i => M.observationLaw))
        (tupleAverage (fun a => K ∘ tupleObservation a)) ≤
      (∑ S ∈ Finset.univ.erase (∅ : Finset (StencilRole d p)),
        overlapWeight J S * stencilCompletionProbabilityBound upper p T ℓ r S) *
      ∫ z, K z ^ 2 ∂M.sampleLaw (StencilRole d p) := by
  apply (variance_splitSample_le_projection_moments M.observationLaw hK).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro S hS
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (M.stencilProjection_secondMoment_le p T x₀ hh hℓ hr hK hs S
      (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hS).1)) (overlapWeight_nonneg S)

theorem stencil_variance_le_two_terms (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (hr : 0 < r)
    (J : StencilRole d p → Type*) [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]
    [∀ i, Nonempty (J i)] {K : (StencilRole d p → (d → ℝ) × (Bool × ℝ)) → ℝ}
    (hK : MemLp K 2 (M.sampleLaw (StencilRole d p)))
    (hs : ∀ z, z ∉ acceptedObservationStencil p T x₀ h ℓ r → K z = 0)
    {η B : ℝ} (hU : 0 ≤ upper) (hη : 0 ≤ η) (hB : 1 ≤ B)
    (hUB : upper ≤ B) (hηC : η ≤ B * (coarseCellVolume p T r).toReal)
    (hJ : ∀ i, (Fintype.card (J i) : ℝ)⁻¹ ≤ η) :
    variance (Measure.pi (fun _ : Σ i, J i => M.observationLaw))
        (tupleAverage (fun a => K ∘ tupleObservation a)) ≤
      ((2 : ℝ) ^ Fintype.card (StencilRole d p) * B ^ Fintype.card (StencilRole d p) *
        (coarseCellVolume p T r).toReal ^ (Fintype.card (StencilRole d p) - 2) *
        (η * (fineCellVolume d ℓ).toReal + η ^ 2)) *
      ∫ z, K z ^ 2 ∂M.sampleLaw (StencilRole d p) :=
  (M.stencil_variance_le_overlap_sum p T x₀ hh hℓ hr J hK hs).trans
    (mul_le_mul_of_nonneg_right (stencilOverlap_sum_le p T ℓ r J hU hη hB hUB hηC hJ)
      (integral_nonneg (fun z => sq_nonneg (K z))))

end RealOutcomeModel
end CausalLowerbound.UpperBound
