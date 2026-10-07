import CausalLowerbound.PartC.PhysicalPatternContinuity

/-! Resampling a sign after actual ghost integration of a selected pattern.
Only retained slots may be selected. A bounded measurable taper can be
included, and the ghost term retains the centered carrier norm. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB.ShellGeometry Wiener Representative
variable {d V I G : Type*} [Fintype d] [DecidableEq d] [Fintype V] [DecidableEq V]
  [Fintype I] [Fintype G]

def ghostPatternIntegral (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N ja : ℝ)
    (B : Array d V (activeBlocks (d := d) ℓ h) 1)
    (e : I ⊕ G ≃ V) (u : I → d → ℝ) (a : I → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (S : Finset V) (χ : (G → d → ℝ) → ℝ) : ℝ :=
  ∫ g : G → d → ℝ, χ g * partialPhysicalPatternWeight x₀ ℓ r h k c w N ja B e u a ζ S g
    ∂Measure.pi (fun _ : G => cubeMeasure d)

theorem ghostPatternIntegral_one_sign_bound
    (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (hℓ : 0 < ℓ) (hr : 0 < r)
    (c w N N₀ ja : ℝ) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀) (hja : ja ^ 2 ≤ 1)
    (B : Array d V (activeBlocks (d := d) ℓ h) 1)
    (e : I ⊕ G ≃ V) (u : I → d → ℝ) (a : I → ℝ) (ha : ∀ i, |a i| ≤ 1)
    (C : ℝ) (hC : 1 ≤ C) (hCz : N₀ / c ≤ C) (hCκ : 1 / (c * N₀) ≤ C)
    (hNa : ∀ i, |N * a i| ≤ C) (S : Finset V)
    (hS : ∀ v ∈ S, ∃ i : I, e (Sum.inl i) = v) (χ : (G → d → ℝ) → ℝ)
    (hχ : AEStronglyMeasurable χ (Measure.pi (fun _ : G => cubeMeasure d)))
    (hχb : ∀ g, |χ g| ≤ 1)
    (j : activeBlocks (d := d) ℓ h) (ζ ζ' : activeBlocks (d := d) ℓ h → Bool)
    (he : ∀ i, i ≠ j → ζ i = ζ' i) :
    |ghostPatternIntegral x₀ ℓ r h k c w N ja B e u a ζ S χ -
      ghostPatternIntegral x₀ ℓ r h k c w N ja B e u a ζ' S χ| ≤
        C ^ Fintype.card V * (2 * ‖symbolPart j B‖ + ‖B - unit‖ *
          ((Fintype.card G : ℝ) * ((2 / (c * N)) * (ℓ / (2 * r)) ^ Fintype.card d))) := by
  let μ := Measure.pi (fun _ : G => cubeMeasure d)
  let z := fun η (g : G → d → ℝ) =>
    completedSites e a (fun s => normalizedRoughChart x₀ ℓ r h k c w N η (g s))
  let p := partialPhysicalPatternWeight x₀ ℓ r h k c w N ja B e u a
  let f := fun η (g : G → d → ℝ) => χ g * p η S g
  let diff := fun (s : G) (g : G → d → ℝ) =>
    |normalizedRoughChart x₀ ℓ r h k c w N ζ (g s) - normalizedRoughChart x₀ ℓ r h k c w N ζ' (g s)|
  have hz η (g : G → d → ℝ) (v : V) : |z η g v| ≤ 1 := by
    cases hv : e.symm v with
    | inl i => simpa only [z, completedSites, Function.comp_apply, hv, Sum.elim_inl] using ha i
    | inr i => simpa only [z, completedSites, Function.comp_apply, hv, Sum.elim_inr] using
        normalizedRoughChart_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough η (g i)
  have hNz η (g : G → d → ℝ) (v : V) : |N * z η g v| ≤ C := by
    cases hv : e.symm v with
    | inl i => simpa only [z, completedSites, Function.comp_apply, hv, Sum.elim_inl] using hNa i
    | inr i => simpa only [z, completedSites, Function.comp_apply, hv, Sum.elim_inr] using
        (normalizedRoughChart_scaled_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough η (g i)).trans hCz
  have hf η : Integrable (f η) μ := by
    apply (integrable_const (C ^ Fintype.card V * ‖B‖)).mono'
      (hχ.mul (partialPhysicalPatternWeight_continuous x₀ ℓ r h k c w N ja hc B e u a η S).aestronglyMeasurable)
    filter_upwards [] with g
    change |χ g * p η S g| ≤ C ^ Fintype.card V * ‖B‖
    rw [abs_mul]
    calc
      _ ≤ 1 * |p η S g| := mul_le_mul_of_nonneg_right (hχb g) (abs_nonneg _)
      _ = |p η S g| := one_mul _
      _ ≤ C ^ Fintype.card V * ‖B‖ :=
        partialPhysicalPatternWeight_bound x₀ ℓ r h k c w N N₀ ja hc hN₀ hN hm hrough hja
          B e u a ha C hC hCz hCκ hNa η S g
  have hd (s : G) : Integrable (diff s) μ := by
    have hc' : Continuous (diff s) :=
      (((normalizedRoughChart_continuous x₀ ℓ r h k c w N hc ζ).comp
        (continuous_apply s : Continuous (fun g : G → d → ℝ => g s))).sub
        ((normalizedRoughChart_continuous x₀ ℓ r h k c w N hc ζ').comp
          (continuous_apply s : Continuous (fun g : G → d → ℝ => g s)))).abs
    apply (integrable_const (2 : ℝ)).mono' hc'.aestronglyMeasurable
    filter_upwards [] with g
    simp only [diff, Real.norm_eq_abs, abs_abs]
    calc
      _ ≤ 1 + 1 := (abs_sub _ _).trans (add_le_add
        (normalizedRoughChart_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough ζ (g s))
        (normalizedRoughChart_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough ζ' (g s)))
      _ = _ := by norm_num
  have hs (g : G → d → ℝ) : (∑ v, |z ζ g v - z ζ' g v|) = ∑ s, diff s g := by
    rw [← Equiv.sum_comp e (fun v => |z ζ g v - z ζ' g v|)]
    simp only [Fintype.sum_sum_type, z, completedSites_retained, completedSites_ghost,
      sub_self, abs_zero, Finset.sum_const_zero, zero_add, diff]
  have hb (g : G → d → ℝ) : |f ζ g - f ζ' g| ≤
      C ^ Fintype.card V * (2 * ‖symbolPart j B‖ + ‖B - unit‖ * ∑ s, diff s g) := by
    have hret (v : V) (hv : v ∈ S) : z ζ g v = z ζ' g v := by
      obtain ⟨i, rfl⟩ := hS v hv
      simp only [z, completedSites_retained]
    have hκ (v : V) : |N * physicalPropensitySlotCorrection x₀ r h k c w N ja
        (completedConfiguration e u g) v| ≤ C :=
      (physicalPropensityCorrection_scaled_bound x₀ r h k c w N N₀ ja hc hN₀ hN hm hja _ v).trans hCκ
    have hh := weightedPropensityPatternWeight_resample_sub_bound {j} N
      (physicalPropensitySlotCorrection x₀ r h k c w N ja (completedConfiguration e u g))
      B (completedConfiguration e u g) (z ζ g) (z ζ' g) ζ ζ'
      (fun i hi => he i (by simpa only [Finset.mem_singleton] using hi)) S hret C hC
      (hz ζ g) (hz ζ' g) (hNz ζ g) (hNz ζ' g) hκ
    have hh' : |p ζ S g - p ζ' S g| ≤
        C ^ Fintype.card V * (2 * ‖symbolPart j B‖ + ‖B - unit‖ * ∑ s, diff s g) := by
      simpa only [Finset.sum_singleton, hs, p, partialPhysicalPatternWeight] using hh
    calc
      _ = |χ g| * |p ζ S g - p ζ' S g| := by simp only [f, ← mul_sub, abs_mul]
      _ ≤ 1 * |p ζ S g - p ζ' S g| := mul_le_mul_of_nonneg_right (hχb g) (abs_nonneg _)
      _ ≤ _ := by simpa only [one_mul] using hh'
  have hsum : Integrable (fun g => ∑ s, diff s g) μ := integrable_finset_sum _ (fun s _ => hd s)
  have hbound := integral_mono ((hf ζ).sub (hf ζ')).abs
    (((integrable_const (2 * ‖symbolPart j B‖)).add (hsum.const_mul ‖B - unit‖)).const_mul
      (C ^ Fintype.card V)) hb
  simp only [Pi.sub_apply, Pi.add_apply] at hbound
  rw [integral_const_mul, integral_add (integrable_const (2 * ‖symbolPart j B‖))
    (hsum.const_mul ‖B - unit‖)] at hbound
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul,
    integral_const_mul] at hbound
  rw [integral_finset_sum Finset.univ (fun s _ => hd s)] at hbound
  have hsum_bound : (∑ s, ∫ g, diff s g ∂μ) ≤ (Fintype.card G : ℝ) *
      ((2 / (c * N)) * (ℓ / (2 * r)) ^ Fintype.card d) := by
    calc
      _ ≤ ∑ _s : G, ((2 / (c * N)) * (ℓ / (2 * r)) ^ Fintype.card d) := by
        apply Finset.sum_le_sum
        intro s _
        rw [show (∫ g, diff s g ∂μ) = ∫ v, |normalizedRoughChart x₀ ℓ r h k c w N ζ v -
          normalizedRoughChart x₀ ℓ r h k c w N ζ' v| ∂cubeMeasure d from
            integral_cube_coordinate (d := d) s (fun v => |normalizedRoughChart x₀ ℓ r h k c w N ζ v -
              normalizedRoughChart x₀ ℓ r h k c w N ζ' v|)]
        exact normalizedRoughChart_one_sign_integral x₀ ℓ r h k hℓ hr c w N hc
          ((div_pos hN₀ hc).trans_le hN) hm j ζ ζ' he
      _ = _ := by simp
  change |(∫ g, f ζ g ∂μ) - ∫ g, f ζ' g ∂μ| ≤ _
  rw [← integral_sub (hf ζ) (hf ζ')]
  exact abs_integral_le_integral_abs.trans (hbound.trans
    (mul_le_mul_of_nonneg_left
      (add_le_add_left (mul_le_mul_of_nonneg_left hsum_bound (norm_nonneg _)) _)
      (pow_nonneg (by linarith) _)))

end CausalLowerbound.PartC
