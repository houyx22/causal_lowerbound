import CausalLowerbound.PartC.GhostPatternResampling
import CausalLowerbound.PartC.ResamplingParity
import CausalLowerbound.PartC.PhysicalRepresentativeReflection

/-! Actual integrated patterns retain their selected-degree parity when
retained variables and ghost signs are flipped together. Conditional
averaging over any finite sign set has the quantitative resampling bound. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener Representative
variable {d V I G : Type*} [Fintype d] [DecidableEq d] [Fintype V] [DecidableEq V]
  [Fintype I] [Fintype G]

theorem partialPhysicalPatternWeight_flip (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N ja : ℝ) (B : Array d V (activeBlocks (d := d) ℓ h) 1)
    (hB : reflection B = B) (e : I ⊕ G ≃ V) (u : I → d → ℝ) (a : I → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (S : Finset V) (g : G → d → ℝ) :
    partialPhysicalPatternWeight x₀ ℓ r h k c w N ja B e u (fun i => -a i) (Walsh.flip ζ) S g =
      (-1) ^ S.card * partialPhysicalPatternWeight x₀ ℓ r h k c w N ja B e u a ζ S g := by
  have hz : completedSites e (fun i => -a i)
      (fun j => normalizedRoughChart x₀ ℓ r h k c w N (Walsh.flip ζ) (g j)) =
      fun v => -completedSites e a (fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (g j)) v := by
    funext v
    cases hv : e.symm v <;> simp only [completedSites, Function.comp_apply, hv,
      Sum.elim_inl, Sum.elim_inr, normalizedRoughChart_flip]
  simp only [partialPhysicalPatternWeight, hz, weightedPropensityPatternWeight,
    propensityPatternWeight_flip, hB]
  ring

theorem ghostPatternIntegral_flip (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N ja : ℝ) (B : Array d V (activeBlocks (d := d) ℓ h) 1)
    (hB : reflection B = B) (e : I ⊕ G ≃ V) (u : I → d → ℝ) (a : I → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (S : Finset V) (χ : (G → d → ℝ) → ℝ) :
    ghostPatternIntegral x₀ ℓ r h k c w N ja B e u (fun i => -a i) (Walsh.flip ζ) S χ =
      (-1) ^ S.card * ghostPatternIntegral x₀ ℓ r h k c w N ja B e u a ζ S χ := by
  unfold ghostPatternIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with g
  rw [partialPhysicalPatternWeight_flip x₀ ℓ r h k c w N ja B hB]
  ring

theorem ghostPatternIntegral_simultaneous_parity (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N ja : ℝ) (B : Array d V (activeBlocks (d := d) ℓ h) 1)
    (hB : reflection B = B) (e : I ⊕ G ≃ V) (u : I → d → ℝ)
    (a : (activeBlocks (d := d) ℓ h → Bool) → I → ℝ)
    (ha : ∀ ζ i, a (Walsh.flip ζ) i = -a ζ i)
    (ζ η : activeBlocks (d := d) ℓ h → Bool) (S : Finset V) (χ : (G → d → ℝ) → ℝ) :
    ghostPatternIntegral x₀ ℓ r h k c w N ja B e u (a (Walsh.flip ζ)) (Walsh.flip η) S χ =
      (-1) ^ S.card * ghostPatternIntegral x₀ ℓ r h k c w N ja B e u (a ζ) η S χ := by
  rw [show a (Walsh.flip ζ) = fun i => -a ζ i from funext (ha ζ)]
  exact ghostPatternIntegral_flip x₀ ℓ r h k c w N ja B hB e u (a ζ) η S χ

theorem ghostPatternIntegral_bound (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N N₀ ja : ℝ) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀) (hja : ja ^ 2 ≤ 1)
    (B : Array d V (activeBlocks (d := d) ℓ h) 1)
    (e : I ⊕ G ≃ V) (u : I → d → ℝ) (a : I → ℝ) (ha : ∀ i, |a i| ≤ 1)
    (C : ℝ) (hC : 1 ≤ C) (hCz : N₀ / c ≤ C) (hCκ : 1 / (c * N₀) ≤ C)
    (hNa : ∀ i, |N * a i| ≤ C) (ζ : activeBlocks (d := d) ℓ h → Bool)
    (S : Finset V) (χ : (G → d → ℝ) → ℝ) (hχ : ∀ g, |χ g| ≤ 1) :
    |ghostPatternIntegral x₀ ℓ r h k c w N ja B e u a ζ S χ| ≤ C ^ Fintype.card V * ‖B‖ := by
  have hb (g : G → d → ℝ) :
      ‖χ g * partialPhysicalPatternWeight x₀ ℓ r h k c w N ja B e u a ζ S g‖ ≤
        C ^ Fintype.card V * ‖B‖ := by
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_right (hχ g) (abs_nonneg _)).trans
      (by simpa only [one_mul] using partialPhysicalPatternWeight_bound x₀ ℓ r h k c w N N₀ ja
            hc hN₀ hN hm hrough hja B e u a ha C hC hCz hCκ hNa ζ S g)
  simpa only [ghostPatternIntegral, Real.norm_eq_abs, measureReal_univ_eq_one, mul_one] using
    norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : G => cubeMeasure d))
      (Filter.Eventually.of_forall hb)

theorem ghostPatternIntegral_resample_bound
    (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (hℓ : 0 < ℓ) (hr : 0 < r)
    (c w N N₀ ja : ℝ) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀) (hja : ja ^ 2 ≤ 1)
    (B : Array d V (activeBlocks (d := d) ℓ h) 1)
    (e : I ⊕ G ≃ V) (u : I → d → ℝ) (a : I → ℝ) (ha : ∀ i, |a i| ≤ 1)
    (C : ℝ) (hC : 1 ≤ C) (hCz : N₀ / c ≤ C) (hCκ : 1 / (c * N₀) ≤ C)
    (hNa : ∀ i, |N * a i| ≤ C) (S : Finset V)
    (hS : ∀ v ∈ S, ∃ i : I, e (Sum.inl i) = v) (χ : (G → d → ℝ) → ℝ)
    (hχ : AEStronglyMeasurable χ (Measure.pi (fun _ : G => cubeMeasure d))) (hχb : ∀ g, |χ g| ≤ 1)
    (T : Finset (activeBlocks (d := d) ℓ h)) (ζ : activeBlocks (d := d) ℓ h → Bool) :
    |ghostPatternIntegral x₀ ℓ r h k c w N ja B e u a ζ S χ -
      Walsh.resampleAverage T (fun η => ghostPatternIntegral x₀ ℓ r h k c w N ja B e u a η S χ) ζ| ≤
        ∑ j ∈ T, C ^ Fintype.card V * (2 * ‖symbolPart j B‖ + ‖B - unit‖ *
          ((Fintype.card G : ℝ) * ((2 / (c * N)) * (ℓ / (2 * r)) ^ Fintype.card d))) := by
  exact Walsh.averaged_resample_function_bound
    (fun η => ghostPatternIntegral x₀ ℓ r h k c w N ja B e u a η S χ)
    (fun j => C ^ Fintype.card V * (2 * ‖symbolPart j B‖ + ‖B - unit‖ *
      ((Fintype.card G : ℝ) * ((2 / (c * N)) * (ℓ / (2 * r)) ^ Fintype.card d))))
    (fun j η η' he => ghostPatternIntegral_one_sign_bound x₀ ℓ r h k hℓ hr c w N N₀ ja
      hc hN₀ hN hm hrough hja B e u a ha C hC hCz hCκ hNa S hS χ hχ hχb j η η' he) T ζ

end CausalLowerbound.PartC
