import CausalLowerbound.PartB.OutcomePackets
import CausalLowerbound.PartB.PositiveWienerComplete
import CausalLowerbound.PeriodizedFourier
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Physical carrier factors, finite overlap, and normalization with respect
to actual Lebesgue measure on the unit cube. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Topology Classical
open MeasureTheory
namespace CausalLowerbound.PartB.ShellGeometry
open Wiener
variable {d : Type*} [Fintype d] [DecidableEq d]

def labeledDensity (Q : ℕ) (θ : ℝ) (H : ℕ) (u : Torus d) : ℝ :=
  match H with
  | 0 => 1
  | n + 1 => (toContinuous (PositiveWiener.naturalDensity (ι := Fin Q) θ n) u).re

theorem labeledDensity_continuous (Q : ℕ) (θ : ℝ) (H : ℕ) :
    Continuous (labeledDensity (d := d) Q θ H) := by
  cases H with
  | zero => exact continuous_const
  | succ n => exact Complex.continuous_re.comp (ContinuousMap.continuous _)

theorem labeledDensity_bounds (Q : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (H : ℕ) (u : Torus d) :
    1 - θ ≤ labeledDensity Q θ H u ∧ labeledDensity Q θ H u ≤ 1 + θ := by
  cases H with
  | zero => change 1 - θ ≤ 1 ∧ 1 ≤ 1 + θ; constructor <;> linarith
  | succ n => exact PositiveWiener.naturalDensity_bounds θ hθ n u

def localCoordinate (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ) (x : d → ℝ) : d → ℝ :=
  fun i => (x i - x₀ i) / r - k i

theorem localCoordinate_continuous (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ) :
    Continuous (localCoordinate x₀ r k) := by
  unfold localCoordinate
  fun_prop

def carrierBox (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ) : Set (d → ℝ) :=
  localCoordinate x₀ r k ⁻¹' Set.Icc (fun _ => -2) (fun _ => 2)

theorem carrierBox_measurable (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ) : MeasurableSet (carrierBox x₀ r k) :=
  (isClosed_Icc.preimage (localCoordinate_continuous x₀ r k)).measurableSet

def carrierNeighbors (z : d → ℝ) : Finset (d → ℤ) :=
  Fintype.piFinset (fun i => Finset.Icc (⌊z i⌋ - 2) (⌊z i⌋ + 2))

theorem carrierNeighbors_card (z : d → ℝ) : (carrierNeighbors z).card = 5 ^ Fintype.card d := by
  have he (i : d) : ⌊z i⌋ + 2 + 1 - (⌊z i⌋ - 2) = 5 := by omega
  simp [carrierNeighbors, Fintype.card_piFinset, Int.card_Icc, he]

theorem carrierBox_overlap (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ) (x : d → ℝ)
    (hx : x ∈ carrierBox x₀ r k) : k ∈ carrierNeighbors (fun i => (x i - x₀ i) / r) := by
  apply Fintype.mem_piFinset.mpr
  intro i
  let z := (x i - x₀ i) / r
  have hlo : (-2 : ℝ) ≤ z - k i := hx.1 i
  have hhi : z - k i ≤ (2 : ℝ) := hx.2 i
  have h₁ : (⌊z⌋ : ℝ) - 2 ≤ (k i : ℝ) := by linarith [Int.floor_le z]
  have h₂ : (k i : ℝ) < (⌊z⌋ : ℝ) + 3 := by linarith [Int.lt_floor_add_one z]
  have h₁' : ⌊z⌋ - 2 ≤ k i := by exact_mod_cast h₁
  have h₂' : k i < ⌊z⌋ + 3 := by exact_mod_cast h₂
  change k i ∈ Finset.Icc (⌊z⌋ - 2) (⌊z⌋ + 2)
  exact Finset.mem_Icc.mpr ⟨h₁', by omega⟩

def physicalFactor (Q : ℕ) (θ : ℝ) (H : ℕ) (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ) (x : d → ℝ) : ℝ :=
  if x ∈ carrierBox x₀ r k then
    labeledDensity Q θ H (torusProjection (carrierCoordinate (localCoordinate x₀ r k x))) else 1

theorem physicalFactor_measurable (Q : ℕ) (θ : ℝ) (H : ℕ) (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ) :
    Measurable (physicalFactor Q θ H x₀ r k) := by
  apply Measurable.ite (carrierBox_measurable x₀ r k) _ measurable_const
  exact ((labeledDensity_continuous Q θ H).comp
    (torusProjection_quotient.continuous.comp (carrierCoordinate_smooth.continuous.comp
      (localCoordinate_continuous x₀ r k)))).measurable

theorem physicalFactor_bounds (Q : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (H : ℕ)
    (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ) (x : d → ℝ) :
    1 - θ ≤ physicalFactor Q θ H x₀ r k x ∧ physicalFactor Q θ H x₀ r k x ≤ 1 + θ := by
  unfold physicalFactor
  split
  · exact labeledDensity_bounds Q θ hθ H _
  · constructor <;> linarith

def unnormalizedDesign (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ)
    (H : (d → ℤ) → ℕ) (x₀ : d → ℝ) (r : ℝ) (x : d → ℝ) : ℝ :=
  ∏ k ∈ S, physicalFactor Q θ (H k) x₀ r k x

theorem unnormalizedDesign_measurable (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ)
    (H : (d → ℤ) → ℕ) (x₀ : d → ℝ) (r : ℝ) : Measurable (unnormalizedDesign Q S θ H x₀ r) :=
  Finset.measurable_prod _ (fun k _ => physicalFactor_measurable Q θ (H k) x₀ r k)

theorem unnormalizedDesign_bounds (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (H : (d → ℤ) → ℕ) (x₀ : d → ℝ) (r : ℝ) (x : d → ℝ) :
    (1 - θ) ^ (5 ^ Fintype.card d) ≤ unnormalizedDesign Q S θ H x₀ r x ∧
      unnormalizedDesign Q S θ H x₀ r x ≤ (1 + θ) ^ (5 ^ Fintype.card d) := by
  classical
  let T := S ∩ carrierNeighbors (fun i => (x i - x₀ i) / r)
  have hTS : T ⊆ S := Finset.inter_subset_left
  have hcard : T.card ≤ 5 ^ Fintype.card d :=
    (Finset.card_le_card Finset.inter_subset_right).trans_eq (carrierNeighbors_card _)
  have he : unnormalizedDesign Q S θ H x₀ r x = ∏ k ∈ T, physicalFactor Q θ (H k) x₀ r k x := by
    symm
    apply Finset.prod_subset hTS
    intro k hk hkT
    have hn : x ∉ carrierBox x₀ r k := fun hx => hkT (Finset.mem_inter.mpr ⟨hk, carrierBox_overlap _ _ _ _ hx⟩)
    simp only [physicalFactor, if_neg hn]
  rw [he]
  have hlo : 0 ≤ 1 - θ := by linarith
  constructor
  · calc
      _ ≤ (1 - θ) ^ T.card := pow_le_pow_of_le_one hlo (by linarith) hcard
      _ = ∏ _k ∈ T, (1 - θ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => hlo) (fun k _ => (physicalFactor_bounds Q θ hθ _ _ _ k x).1)
  · calc
      _ ≤ ∏ _k ∈ T, (1 + θ) := Finset.prod_le_prod
        (fun k _ => hlo.trans (physicalFactor_bounds Q θ hθ _ _ _ k x).1)
        (fun k _ => (physicalFactor_bounds Q θ hθ _ _ _ k x).2)
      _ = (1 + θ) ^ T.card := by simp
      _ ≤ _ := pow_le_pow_right₀ (by linarith) hcard

def cubeMeasure (d : Type*) [Fintype d] : Measure (d → ℝ) :=
  volume.restrict (Set.Icc (0 : d → ℝ) 1)

instance cubeMeasure_probability : IsProbabilityMeasure (cubeMeasure d) := by
  constructor
  simp [cubeMeasure, Real.volume_Icc_pi]

def designNormalizer (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ)
    (H : (d → ℤ) → ℕ) (x₀ : d → ℝ) (r : ℝ) : ℝ :=
  ∫ x, unnormalizedDesign Q S θ H x₀ r x ∂cubeMeasure d

def normalizedDesign (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ)
    (H : (d → ℤ) → ℕ) (x₀ : d → ℝ) (r : ℝ) (x : d → ℝ) : ℝ :=
  unnormalizedDesign Q S θ H x₀ r x / designNormalizer Q S θ H x₀ r

theorem design_integrable (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (H : (d → ℤ) → ℕ) (x₀ : d → ℝ) (r : ℝ) :
    Integrable (unnormalizedDesign Q S θ H x₀ r) (cubeMeasure d) := by
  refine ⟨(unnormalizedDesign_measurable Q S θ H x₀ r).aestronglyMeasurable,
    hasFiniteIntegral_of_bounded (C := (1 + θ) ^ (5 ^ Fintype.card d)) (ae_of_all _ ?_)⟩
  intro x
  have hb := unnormalizedDesign_bounds Q S θ hθ hθ1 H x₀ r x
  have hl : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1.le
  rw [Real.norm_eq_abs, abs_of_nonneg ((pow_nonneg hl _).trans hb.1)]
  exact hb.2

theorem designNormalizer_bounds (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (H : (d → ℤ) → ℕ) (x₀ : d → ℝ) (r : ℝ) :
    (1 - θ) ^ (5 ^ Fintype.card d) ≤ designNormalizer Q S θ H x₀ r ∧
      designNormalizer Q S θ H x₀ r ≤ (1 + θ) ^ (5 ^ Fintype.card d) := by
  have hi := design_integrable Q S θ hθ hθ1 H x₀ r
  constructor
  · simpa only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using
      integral_mono (integrable_const ((1 - θ) ^ (5 ^ Fintype.card d))) hi
        (fun x => (unnormalizedDesign_bounds Q S θ hθ hθ1 H x₀ r x).1)
  · simpa only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using
      integral_mono hi (integrable_const ((1 + θ) ^ (5 ^ Fintype.card d)))
        (fun x => (unnormalizedDesign_bounds Q S θ hθ hθ1 H x₀ r x).2)

theorem normalizedDesign_legal (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (H : (d → ℤ) → ℕ) (x₀ : d → ℝ) (r : ℝ) :
    Measurable (normalizedDesign Q S θ H x₀ r) ∧
    (∫ x, normalizedDesign Q S θ H x₀ r x ∂cubeMeasure d) = 1 ∧
    ∀ x, (1 - θ) ^ (5 ^ Fintype.card d) / (1 + θ) ^ (5 ^ Fintype.card d) ≤ normalizedDesign Q S θ H x₀ r x ∧
      normalizedDesign Q S θ H x₀ r x ≤ (1 + θ) ^ (5 ^ Fintype.card d) / (1 - θ) ^ (5 ^ Fintype.card d) := by
  have hz := designNormalizer_bounds Q S θ hθ hθ1 H x₀ r
  have hl : 0 < (1 - θ) ^ (5 ^ Fintype.card d) := pow_pos (sub_pos.mpr hθ1) _
  have hZ : 0 < designNormalizer Q S θ H x₀ r := hl.trans_le hz.1
  refine ⟨(unnormalizedDesign_measurable Q S θ H x₀ r).div_const _, ?_, ?_⟩
  · simp only [normalizedDesign, integral_div]
    exact div_self hZ.ne'
  · intro x
    have hx := unnormalizedDesign_bounds Q S θ hθ hθ1 H x₀ r x
    exact ⟨div_le_div₀ (hl.le.trans hx.1) hx.1 hZ hz.2,
      div_le_div₀ (by positivity) hx.2 hl hz.1⟩

theorem exists_design_contrast (N : ℕ) (lower upper : ℝ) (hl : lower < 1) (hu : 1 < upper) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ lower ≤ (1 - θ) ^ N / (1 + θ) ^ N ∧
      (1 + θ) ^ N / (1 - θ) ^ N ≤ upper := by
  have hc₁ : ContinuousAt (fun θ : ℝ => (1 - θ) ^ N / (1 + θ) ^ N) 0 := by
    fun_prop (disch := norm_num)
  have hc₂ : ContinuousAt (fun θ : ℝ => (1 + θ) ^ N / (1 - θ) ^ N) 0 := by
    fun_prop (disch := norm_num)
  have he : ∀ᶠ θ : ℝ in 𝓝 0, lower < (1 - θ) ^ N / (1 + θ) ^ N ∧
      (1 + θ) ^ N / (1 - θ) ^ N < upper ∧ θ < 1 := by
    filter_upwards [hc₁.eventually (lt_mem_nhds (by simpa using hl)),
      hc₂.eventually (gt_mem_nhds (by simpa using hu)),
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))] with θ h₁ h₂ h₃
    exact ⟨h₁, h₂, h₃⟩
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp he
  have hm : dist (δ / 2) (0 : ℝ) < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith
  have hd := hb hm
  exact ⟨δ / 2, by positivity, hd.2.2, hd.1.le, hd.2.1.le⟩
end CausalLowerbound.PartB.ShellGeometry
