import CausalLowerbound.PartC.PhysicalOutcomePatternContinuity
import CausalLowerbound.PartC.GhostSignResampling

/-! Resampling bounds for cubic patterns after integration over actual
ghost sites. Selected slots are retained sites, so changes in the ghost
values are charged only to the centered carrier, with cubic degree cost. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB.ShellGeometry Wiener Representative
variable {d V I G : Type*} [Fintype d] [DecidableEq d] [Fintype V] [DecidableEq V]
  [Fintype I] [Fintype G]

def ghostOutcomePatternIntegral (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N : ℝ)
    (B : Array d V (activeBlocks (d := d) ℓ h) 3)
    (e : I ⊕ G ≃ V) (u : I → d → ℝ) (a : I → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (D : Degree V 3)
    (χ : (G → d → ℝ) → ℝ) : ℝ :=
  ∫ g : G → d → ℝ, χ g * partialPhysicalOutcomePatternWeight x₀ ℓ r h k c w N B e u a ζ D g
    ∂Measure.pi (fun _ : G => cubeMeasure d)

theorem ghostOutcomePatternIntegral_one_sign_bound
    (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (hℓ : 0 < ℓ) (hr : 0 < r)
    (c w N N₀ : ℝ) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀)
    (B : Array d V (activeBlocks (d := d) ℓ h) 3)
    (e : I ⊕ G ≃ V) (u : I → d → ℝ) (a : I → ℝ) (ha : ∀ i, |a i| ≤ 1)
    (C : ℝ) (hC : 1 ≤ C) (hCz : N₀ / c ≤ C) (hCκ : 1 / N₀ ^ 2 ≤ C)
    (hNa : ∀ i, |N * a i| ≤ C) (D : Degree V 3)
    (hD : ∀ v, D v ≠ 0 → ∃ i : I, e (Sum.inl i) = v) (χ : (G → d → ℝ) → ℝ)
    (hχ : AEStronglyMeasurable χ (Measure.pi (fun _ : G => cubeMeasure d)))
    (hχb : ∀ g, |χ g| ≤ 1)
    (j : activeBlocks (d := d) ℓ h) (ζ ζ' : activeBlocks (d := d) ℓ h → Bool)
    (he : ∀ i, i ≠ j → ζ i = ζ' i) :
    |ghostOutcomePatternIntegral x₀ ℓ r h k c w N B e u a ζ D χ -
      ghostOutcomePatternIntegral x₀ ℓ r h k c w N B e u a ζ' D χ| ≤
        (C ^ 4) ^ Fintype.card V * (2 * ‖symbolPart j B‖ + (3 * ‖B - unit‖) *
          ((Fintype.card G : ℝ) * ((2 / (c * N)) * (ℓ / (2 * r)) ^ Fintype.card d))) := by
  let μ := Measure.pi (fun _ : G => cubeMeasure d)
  let z := fun η (g : G → d → ℝ) =>
    completedSites e a (fun s => normalizedRoughChart x₀ ℓ r h k c w N η (g s))
  let p := partialPhysicalOutcomePatternWeight x₀ ℓ r h k c w N B e u a
  let f := fun η (g : G → d → ℝ) => χ g * p η D g
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
    apply (integrable_const ((C ^ 4) ^ Fintype.card V * ‖B‖)).mono'
      (hχ.mul (partialPhysicalOutcomePatternWeight_continuous x₀ ℓ r h k c w N hc B e u a η D).aestronglyMeasurable)
    filter_upwards [] with g
    change |χ g * p η D g| ≤ (C ^ 4) ^ Fintype.card V * ‖B‖
    rw [abs_mul]
    calc
      _ ≤ 1 * |p η D g| := mul_le_mul_of_nonneg_right (hχb g) (abs_nonneg _)
      _ = |p η D g| := one_mul _
      _ ≤ (C ^ 4) ^ Fintype.card V * ‖B‖ :=
        partialPhysicalOutcomePatternWeight_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough
          B e u a ha C hC hCz hCκ hNa η D g
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
      (C ^ 4) ^ Fintype.card V * (2 * ‖symbolPart j B‖ + (3 * ‖B - unit‖) * ∑ s, diff s g) := by
    have hret (v : V) (hv : D v ≠ 0) : z ζ g v = z ζ' g v := by
      obtain ⟨i, rfl⟩ := hD v hv
      simp only [z, completedSites_retained]
    have hκ (v : V) : |normalizedRoughVariance x₀ r h k c w N
        (configurationSite (completedConfiguration e u g) v)| ≤ C :=
      (normalizedRoughVariance_bound x₀ r h k c w N N₀ hc hN₀ hN hm _).trans hCκ
    have hh := weightedOutcomePatternWeight_resample_sub_bound {j} N
      (fun v => normalizedRoughVariance x₀ r h k c w N
        (configurationSite (completedConfiguration e u g) v))
      B (completedConfiguration e u g) (z ζ g) (z ζ' g) ζ ζ'
      (fun i hi => he i (by simpa only [Finset.mem_singleton] using hi)) D hret C hC
      (hz ζ g) (hz ζ' g) (hNz ζ g) (hNz ζ' g) hκ
    have hh' : |p ζ D g - p ζ' D g| ≤
        (C ^ 4) ^ Fintype.card V * (2 * ‖symbolPart j B‖ + (3 * ‖B - unit‖) * ∑ s, diff s g) := by
      simpa only [Finset.sum_singleton, hs, p, partialPhysicalOutcomePatternWeight,
        mul_left_comm, mul_assoc] using hh
    calc
      _ = |χ g| * |p ζ D g - p ζ' D g| := by simp only [f, ← mul_sub, abs_mul]
      _ ≤ 1 * |p ζ D g - p ζ' D g| := mul_le_mul_of_nonneg_right (hχb g) (abs_nonneg _)
      _ ≤ _ := by simpa only [one_mul] using hh'
  have hsum : Integrable (fun g => ∑ s, diff s g) μ := integrable_finset_sum _ (fun s _ => hd s)
  have hbound := integral_mono ((hf ζ).sub (hf ζ')).abs
    (((integrable_const (2 * ‖symbolPart j B‖)).add (hsum.const_mul (3 * ‖B - unit‖))).const_mul
      ((C ^ 4) ^ Fintype.card V)) hb
  simp only [Pi.sub_apply, Pi.add_apply] at hbound
  rw [integral_const_mul, integral_add (integrable_const (2 * ‖symbolPart j B‖))
    (hsum.const_mul (3 * ‖B - unit‖))] at hbound
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
      (add_le_add_left (mul_le_mul_of_nonneg_left hsum_bound (mul_nonneg (by norm_num) (norm_nonneg _))) _)
      (pow_nonneg (pow_nonneg (by linarith) _) _)))

end CausalLowerbound.PartC
