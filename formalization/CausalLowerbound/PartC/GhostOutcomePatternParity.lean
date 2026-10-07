import CausalLowerbound.PartC.GhostOutcomePatternResampling
import CausalLowerbound.PartC.ResamplingParity
import CausalLowerbound.PartC.PhysicalRepresentativeReflection

/-! Cubic ghost patterns retain their total-degree parity under simultaneous
reflection of retained rough values and ghost signs. Finite-set resampling
is controlled by the sum of the individual sign costs. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener Representative
variable {d V I G : Type*} [Fintype d] [DecidableEq d] [Fintype V] [DecidableEq V]
  [Fintype I] [Fintype G]

theorem partialPhysicalOutcomePatternWeight_flip (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N : ℝ) (B : Array d V (activeBlocks (d := d) ℓ h) 3)
    (hB : reflection B = B) (e : I ⊕ G ≃ V) (u : I → d → ℝ) (a : I → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (D : Degree V 3) (g : G → d → ℝ) :
    partialPhysicalOutcomePatternWeight x₀ ℓ r h k c w N B e u (fun i => -a i) (Walsh.flip ζ) D g =
      (-1) ^ degreeSize D * partialPhysicalOutcomePatternWeight x₀ ℓ r h k c w N B e u a ζ D g := by
  have hz : completedSites e (fun i => -a i)
      (fun j => normalizedRoughChart x₀ ℓ r h k c w N (Walsh.flip ζ) (g j)) =
      fun v => -completedSites e a (fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (g j)) v := by
    funext v
    cases hv : e.symm v <;> simp only [completedSites, Function.comp_apply, hv,
      Sum.elim_inl, Sum.elim_inr, normalizedRoughChart_flip]
  simp only [partialPhysicalOutcomePatternWeight, hz, weightedOutcomePatternWeight,
    outcomePatternWeight_flip, hB]
  ring

theorem ghostOutcomePatternIntegral_flip (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N : ℝ) (B : Array d V (activeBlocks (d := d) ℓ h) 3)
    (hB : reflection B = B) (e : I ⊕ G ≃ V) (u : I → d → ℝ) (a : I → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (D : Degree V 3) (χ : (G → d → ℝ) → ℝ) :
    ghostOutcomePatternIntegral x₀ ℓ r h k c w N B e u (fun i => -a i) (Walsh.flip ζ) D χ =
      (-1) ^ degreeSize D * ghostOutcomePatternIntegral x₀ ℓ r h k c w N B e u a ζ D χ := by
  unfold ghostOutcomePatternIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with g
  rw [partialPhysicalOutcomePatternWeight_flip x₀ ℓ r h k c w N B hB]
  ring

theorem ghostOutcomePatternIntegral_simultaneous_parity (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N : ℝ) (B : Array d V (activeBlocks (d := d) ℓ h) 3)
    (hB : reflection B = B) (e : I ⊕ G ≃ V) (u : I → d → ℝ)
    (a : (activeBlocks (d := d) ℓ h → Bool) → I → ℝ)
    (ha : ∀ ζ i, a (Walsh.flip ζ) i = -a ζ i)
    (ζ η : activeBlocks (d := d) ℓ h → Bool) (D : Degree V 3) (χ : (G → d → ℝ) → ℝ) :
    ghostOutcomePatternIntegral x₀ ℓ r h k c w N B e u (a (Walsh.flip ζ)) (Walsh.flip η) D χ =
      (-1) ^ degreeSize D * ghostOutcomePatternIntegral x₀ ℓ r h k c w N B e u (a ζ) η D χ := by
  rw [show a (Walsh.flip ζ) = fun i => -a ζ i from funext (ha ζ)]
  exact ghostOutcomePatternIntegral_flip x₀ ℓ r h k c w N B hB e u (a ζ) η D χ

theorem ghostOutcomePatternIntegral_bound (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N N₀ : ℝ) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀)
    (B : Array d V (activeBlocks (d := d) ℓ h) 3)
    (e : I ⊕ G ≃ V) (u : I → d → ℝ) (a : I → ℝ) (ha : ∀ i, |a i| ≤ 1)
    (C : ℝ) (hC : 1 ≤ C) (hCz : N₀ / c ≤ C) (hCκ : 1 / N₀ ^ 2 ≤ C)
    (hNa : ∀ i, |N * a i| ≤ C) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (D : Degree V 3) (χ : (G → d → ℝ) → ℝ) (hχ : ∀ g, |χ g| ≤ 1) :
    |ghostOutcomePatternIntegral x₀ ℓ r h k c w N B e u a ζ D χ| ≤ (C ^ 4) ^ Fintype.card V * ‖B‖ := by
  have hb (g : G → d → ℝ) :
      ‖χ g * partialPhysicalOutcomePatternWeight x₀ ℓ r h k c w N B e u a ζ D g‖ ≤
        (C ^ 4) ^ Fintype.card V * ‖B‖ := by
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_right (hχ g) (abs_nonneg _)).trans
      (by simpa only [one_mul] using partialPhysicalOutcomePatternWeight_bound x₀ ℓ r h k c w N N₀
            hc hN₀ hN hm hrough B e u a ha C hC hCz hCκ hNa ζ D g)
  simpa only [ghostOutcomePatternIntegral, Real.norm_eq_abs, measureReal_univ_eq_one, mul_one] using
    norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : G => cubeMeasure d))
      (Filter.Eventually.of_forall hb)

theorem ghostOutcomePatternIntegral_resample_bound
    (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (hℓ : 0 < ℓ) (hr : 0 < r)
    (c w N N₀ : ℝ) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀)
    (B : Array d V (activeBlocks (d := d) ℓ h) 3)
    (e : I ⊕ G ≃ V) (u : I → d → ℝ) (a : I → ℝ) (ha : ∀ i, |a i| ≤ 1)
    (C : ℝ) (hC : 1 ≤ C) (hCz : N₀ / c ≤ C) (hCκ : 1 / N₀ ^ 2 ≤ C)
    (hNa : ∀ i, |N * a i| ≤ C) (D : Degree V 3)
    (hD : ∀ v, D v ≠ 0 → ∃ i : I, e (Sum.inl i) = v) (χ : (G → d → ℝ) → ℝ)
    (hχ : AEStronglyMeasurable χ (Measure.pi (fun _ : G => cubeMeasure d))) (hχb : ∀ g, |χ g| ≤ 1)
    (T : Finset (activeBlocks (d := d) ℓ h)) (ζ : activeBlocks (d := d) ℓ h → Bool) :
    |ghostOutcomePatternIntegral x₀ ℓ r h k c w N B e u a ζ D χ -
      Walsh.resampleAverage T (fun η => ghostOutcomePatternIntegral x₀ ℓ r h k c w N B e u a η D χ) ζ| ≤
        ∑ j ∈ T, (C ^ 4) ^ Fintype.card V * (2 * ‖symbolPart j B‖ + (3 * ‖B - unit‖) *
          ((Fintype.card G : ℝ) * ((2 / (c * N)) * (ℓ / (2 * r)) ^ Fintype.card d))) := by
  exact Walsh.averaged_resample_function_bound
    (fun η => ghostOutcomePatternIntegral x₀ ℓ r h k c w N B e u a η D χ)
    (fun j => (C ^ 4) ^ Fintype.card V * (2 * ‖symbolPart j B‖ + (3 * ‖B - unit‖) *
      ((Fintype.card G : ℝ) * ((2 / (c * N)) * (ℓ / (2 * r)) ^ Fintype.card d))))
    (fun j η η' he => ghostOutcomePatternIntegral_one_sign_bound x₀ ℓ r h k hℓ hr c w N N₀
      hc hN₀ hN hm hrough B e u a ha C hC hCz hCκ hNa D hD χ hχ hχb j η η' he) T ζ

end CausalLowerbound.PartC
