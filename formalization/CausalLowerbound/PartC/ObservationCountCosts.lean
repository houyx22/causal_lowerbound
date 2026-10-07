import CausalLowerbound.PartC.SharedComponentCosts
import CausalLowerbound.PartC.CarrierDesignMarginals
import CausalLowerbound.PartC.AssignmentTransition

/-! Measurable observation counts dominate the incident-block count and
the assignment-transition exception. Their expectations use only the
one-coordinate density ceiling of the actual mixed design. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt incidenceComponentFintype
variable {d I K J Ω : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]
  [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J] [Fintype Ω] {θ : ℝ}

theorem mixedCarrierDesign_eval_integrable
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (H : K → DiscreteLaw ℕ)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ) (i : Fin n)
    (f : (d → ℝ) → ℝ) (hfi : Integrable f volume) :
    Integrable (fun x => f (x i)) (mixedCarrierDesign F hθ hθ1 S x₀ r H kernel n) := by
  let e := MeasurableEquiv.funUnique Unit (d → ℝ)
  have hp := volume_preserving_funUnique Unit (d → ℝ)
  have hi : Integrable (f ∘ e) volume := (hp.integrable_comp_emb e.measurableEmbedding).mpr hfi
  exact mixedCarrierDesign_coordinate_integrable F hθ hθ1 S x₀ r H kernel n
    (fun _ : Unit => i) (fun _ _ _ => Subsingleton.elim _ _) (f ∘ e) hi

theorem mixedCarrierDesign_eval_integral_le
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (H : K → DiscreteLaw ℕ)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ) (i : Fin n)
    (f : (d → ℝ) → ℝ) (hfm : Measurable f) (hf0 : ∀ z, 0 ≤ f z) (hfi : Integrable f volume) :
    (∫ x, f (x i) ∂mixedCarrierDesign F hθ hθ1 S x₀ r H kernel n) ≤
      (designDensityCeiling d θ : ℝ) * ∫ z, f z := by
  let e := MeasurableEquiv.funUnique Unit (d → ℝ)
  have hp := volume_preserving_funUnique Unit (d → ℝ)
  have hi : Integrable (f ∘ e) volume := (hp.integrable_comp_emb e.measurableEmbedding).mpr hfi
  have hb := mixedCarrierDesign_coordinate_integral_le F hθ hθ1 S x₀ r H kernel n
    (fun _ : Unit => i) (fun _ _ _ => Subsingleton.elim _ _) (f ∘ e)
    (hfm.comp e.measurable) (fun z => hf0 (e z)) hi
  have he : (∫ z : Unit → d → ℝ, (f ∘ e) z) = ∫ z, f z := hp.integral_comp' f
  rw [he] at hb
  simpa only [Fintype.card_unique, pow_one] using hb

def observationSetCount (A : Set (d → ℝ)) (x : I → d → ℝ) : ℝ :=
  ∑ i, A.indicator (fun _ => (1 : ℝ)) (x i)

theorem observationSetCount_nonneg (A : Set (d → ℝ)) (x : I → d → ℝ) :
    0 ≤ observationSetCount A x :=
  Finset.sum_nonneg (fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)

theorem observationSetCount_measurable (A : Set (d → ℝ)) (hA : MeasurableSet A) :
    Measurable (observationSetCount (I := I) A) :=
  Finset.measurable_sum _ (fun i _ => (measurable_const.indicator hA).comp (measurable_pi_apply i))

theorem mixedCarrierDesign_observationSetCount_integrable
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (H : K → DiscreteLaw ℕ)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ)
    (A : Set (d → ℝ)) (hA : MeasurableSet A) (hv : volume A < ⊤) :
    Integrable (observationSetCount (I := Fin n) A) (mixedCarrierDesign F hθ hθ1 S x₀ r H kernel n) := by
  have hi : Integrable (A.indicator (fun _ => (1 : ℝ))) volume :=
    (integrable_indicator_iff hA).mpr (integrableOn_const.mpr (Or.inr hv))
  exact integrable_finset_sum _ (fun i _ =>
    mixedCarrierDesign_eval_integrable F hθ hθ1 S x₀ r H kernel n i _ hi)

theorem mixedCarrierDesign_observationSetCount_integral_le
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (H : K → DiscreteLaw ℕ)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ)
    (A : Set (d → ℝ)) (hA : MeasurableSet A) (hv : volume A < ⊤) :
    (∫ x, observationSetCount A x ∂mixedCarrierDesign F hθ hθ1 S x₀ r H kernel n) ≤
      (n : ℝ) * (designDensityCeiling d θ : ℝ) * volume.real A := by
  have hi : Integrable (A.indicator (fun _ => (1 : ℝ))) volume :=
    (integrable_indicator_iff hA).mpr (integrableOn_const.mpr (Or.inr hv))
  unfold observationSetCount
  rw [integral_finset_sum _ (fun i _ =>
    mixedCarrierDesign_eval_integrable F hθ hθ1 S x₀ r H kernel n i _ hi)]
  calc
    _ ≤ ∑ _i : Fin n, (designDensityCeiling d θ : ℝ) * ∫ z, A.indicator (fun _ => (1 : ℝ)) z :=
      Finset.sum_le_sum (fun i _ => mixedCarrierDesign_eval_integral_le F hθ hθ1 S x₀ r H kernel n i _
        (measurable_const.indicator hA) (fun z => Set.indicator_nonneg (fun _ _ => zero_le_one) z) hi)
    _ = _ := by simp only [integral_indicator_const (1 : ℝ) hA, smul_eq_mul, mul_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem configurationBlocks_card_le_coarse_count
    (x₀ : d → ℝ) (r h : ℝ) (hr : 0 < r) (hrh : r ≤ h) (x : I → d → ℝ) :
    ((configurationBlocks (activeBlocks r h) x₀ r x).card : ℝ) ≤
      (5 : ℝ) ^ Fintype.card d * observationSetCount (coordinateBox x₀ (5 * h)) x := by
  have hi (i : I) : ((incidentBlocks (activeBlocks r h) x₀ r (x i)).card : ℝ) ≤
      (coordinateBox x₀ (5 * h)).indicator (fun _ => (5 : ℝ) ^ Fintype.card d) (x i) := by
    by_cases hx : x i ∈ coordinateBox x₀ (5 * h)
    · rw [Set.indicator_of_mem hx]
      exact_mod_cast incidentBlocks_card_le (activeBlocks r h) x₀ r (x i)
    · rw [Set.indicator_of_not_mem hx]
      have he : incidentBlocks (activeBlocks r h) x₀ r (x i) = ∅ := by
        apply Finset.eq_empty_iff_forall_not_mem.mpr
        intro k hk
        have hk' := Finset.mem_filter.mp hk
        exact hx ((mem_coordinateBox x₀ (5 * h) (x i)).mpr
          (active_carrier_distance x₀ r h hr hrh k hk'.1 (x i) hk'.2))
      simp only [he, Finset.card_empty, Nat.cast_zero, le_refl]
  have hcard : ((configurationBlocks (activeBlocks r h) x₀ r x).card : ℝ) ≤
      ∑ i, ((incidentBlocks (activeBlocks r h) x₀ r (x i)).card : ℝ) := by
    exact_mod_cast (Finset.card_biUnion_le :
      (configurationBlocks (activeBlocks r h) x₀ r x).card ≤
        ∑ i, (incidentBlocks (activeBlocks r h) x₀ r (x i)).card)
  apply (hcard.trans (Finset.sum_le_sum (fun i _ => hi i))).trans_eq
  unfold observationSetCount
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hx : x i ∈ coordinateBox x₀ (5 * h) <;> simp [hx]

theorem shared_component_block_card_sum_le_coarse_count
    (x₀ : d → ℝ) (ℓ r h : ℝ) (hr : 0 < r) (hrh : r ≤ h) (x : I → d → ℝ) :
    (∑ c : Option (incidenceGraph (physicalSharedIncidence (activeBlocks r h) x₀ ℓ r h x)).ConnectedComponent,
      ((configurationBlocks (activeBlocks r h) x₀ r
        (fun i : {i // siteComponent (physicalSharedIncidence (activeBlocks r h) x₀ ℓ r h x) i = c} => x i.val)).card : ℝ)) ≤
      (5 : ℝ) ^ Fintype.card d * observationSetCount (coordinateBox x₀ (5 * h)) x := by
  let S := activeBlocks (d := d) r h
  let T := configurationBlocks S x₀ r x
  let f := fun k : d → ℤ => if k ∈ T then (1 : ℝ) else 0
  have hf (k : d → ℤ) : 0 ≤ f k := by dsimp [f]; split_ifs <;> norm_num
  have he (c : Option (incidenceGraph (physicalSharedIncidence S x₀ ℓ r h x)).ConnectedComponent) :
      ((configurationBlocks S x₀ r
        (fun i : {i // siteComponent (physicalSharedIncidence S x₀ ℓ r h x) i = c} => x i.val)).card : ℝ) =
      ∑ k : configurationBlocks S x₀ r
        (fun i : {i // siteComponent (physicalSharedIncidence S x₀ ℓ r h x) i = c} => x i.val), f k.val := by
    have hh (k : configurationBlocks S x₀ r
        (fun i : {i // siteComponent (physicalSharedIncidence S x₀ ℓ r h x) i = c} => x i.val)) : f k.val = 1 := by
      obtain ⟨hk, i, hi⟩ := (mem_configurationBlocks S x₀ r _ k.val).mp k.property
      exact if_pos ((mem_configurationBlocks S x₀ r x k.val).mpr ⟨hk, i.val, hi⟩)
    simp only [hh, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, mul_one]
  have hfilter : S.filter (fun k => k ∈ T) = T := by
    ext k
    simp only [Finset.mem_filter, and_iff_right_iff_imp]
    exact fun hk => configurationBlocks_subset S x₀ r x hk
  have htotal : (∑ k : S, f k.val) = (T.card : ℝ) := by
    rw [Finset.sum_coe_sort]
    change (∑ k ∈ S, if k ∈ T then (1 : ℝ) else 0) = _
    rw [← Finset.sum_filter, hfilter]
    simp
  calc
    _ = ∑ c : Option (incidenceGraph (physicalSharedIncidence S x₀ ℓ r h x)).ConnectedComponent,
        ∑ k : configurationBlocks S x₀ r
          (fun i : {i // siteComponent (physicalSharedIncidence S x₀ ℓ r h x) i = c} => x i.val), f k.val :=
      Finset.sum_congr rfl (fun c _ => he c)
    _ ≤ ∑ k : S, f k.val := shared_component_block_sum_le S x₀ ℓ r h x f (fun k _ => hf k)
    _ = (T.card : ℝ) := htotal
    _ ≤ _ := configurationBlocks_card_le_coarse_count x₀ r h hr hrh x

theorem mixedCarrierDesign_observationSetCount_integral_of_volume
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (H : K → DiscreteLaw ℕ)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ)
    (A : Set (d → ℝ)) (hA : MeasurableSet A) (V : ℝ) (hV : 0 ≤ V)
    (hvol : volume A ≤ ENNReal.ofReal V) :
    (∫ x, observationSetCount A x ∂mixedCarrierDesign F hθ hθ1 S x₀ r H kernel n) ≤
      (n : ℝ) * (designDensityCeiling d θ : ℝ) * V := by
  have hv : volume A < ⊤ := hvol.trans_lt (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
  rw [ENNReal.toReal_ofReal hV] at hr
  exact (mixedCarrierDesign_observationSetCount_integral_le F hθ hθ1 S x₀ r H kernel n A hA hv).trans
    (mul_le_mul_of_nonneg_left hr (by positivity))

theorem mixedCarrierDesign_coarse_count_integral_le
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r h : ℝ) (hh : 0 ≤ h) (H : K → DiscreteLaw ℕ)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ) :
    (∫ x, observationSetCount (coordinateBox x₀ (5 * h)) x
      ∂mixedCarrierDesign F hθ hθ1 S x₀ r H kernel n) ≤
      (designDensityCeiling d θ : ℝ) * 10 ^ Fintype.card d * ((n : ℝ) * h ^ Fintype.card d) := by
  have hv : volume (coordinateBox x₀ (5 * h)) ≤ ENNReal.ofReal ((10 * h) ^ Fintype.card d) := by
    rw [coordinateBox_volume, show 2 * (5 * h) = 10 * h by ring,
      ENNReal.ofReal_pow (by positivity)]
  apply (mixedCarrierDesign_observationSetCount_integral_of_volume F hθ hθ1 S x₀ r H kernel n
    (coordinateBox x₀ (5 * h)) measurableSet_Icc ((10 * h) ^ Fintype.card d) (by positivity) hv).trans_eq
  rw [mul_pow]
  ring

theorem mixedCarrierDesign_transition_count_integral_le
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (x₀ : d → ℝ) (r h w : ℝ) (hr : 0 < r) (hrh : r ≤ h) (hw : 0 < w) (hw1 : w ≤ 1)
    (H : K → DiscreteLaw ℕ) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (n : ℕ) :
    (∫ x, observationSetCount (assignmentTransitionUnion (activeBlocks r h) w x₀ r) x
      ∂mixedCarrierDesign F hθ hθ1 (activeBlocks r h) x₀ r H kernel n) ≤
      ((designDensityCeiling d θ : ℝ) *
        (2 * Fintype.card d * (2 : ℝ) ^ (Fintype.card d - 1) * 7 ^ Fintype.card d)) *
          ((n : ℝ) * h ^ Fintype.card d * w) := by
  have hh := hr.trans_le hrh
  have hb := mixedCarrierDesign_observationSetCount_integral_of_volume F hθ hθ1 (activeBlocks r h)
    x₀ r H kernel n (assignmentTransitionUnion (activeBlocks r h) w x₀ r)
    (assignmentTransitionUnion_measurable _ w x₀ r) _ (by positivity)
    (active_assignmentTransition_volume w x₀ r h hw hw1 hr hrh)
  exact hb.trans_eq (by ring)

end CausalLowerbound.PartC
