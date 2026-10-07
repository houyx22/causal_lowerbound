import CausalLowerbound.PartB.ComponentActivation
import CausalLowerbound.PartB.PhysicalComponentFactorization

/-! Multiblock activation for the actual physical packet model and its
normalized-design Bayes posterior. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Filter
open scoped BigOperators Classical
namespace CausalLowerbound.PartB.ShellGeometry
open Wiener
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d]

def siteCompletion {I : Type*} [Fintype I] (Q : ℕ) (S : Finset I) (hS : S.card ≤ Q) :
    S ⊕ Fin (Q - S.card) ≃ Fin Q :=
  Fintype.equivOfCardEq (by simp only [Fintype.card_sum, Fintype.card_coe, Fintype.card_fin]; omega)

def physicalBlockCoordinates {m : ℕ} (x₀ : d → ℝ) (r : ℝ)
    (x : Fin m → d → ℝ) (k : d → ℤ) (i : Fin m) : d → ℝ :=
  carrierCoordinate (localCoordinate x₀ r k (x i))

def physicalBlockPackets {m : ℕ} (x₀ : d → ℝ) (r h : ℝ)
    (x : Fin m → d → ℝ) (k : d → ℤ) (i : Fin m) : ℝ :=
  packet (coarseBump x₀ h) x₀ r k (x i)

theorem physicalBlockPackets_zero {m : ℕ} (x₀ : d → ℝ) (r h : ℝ)
    (x : Fin m → d → ℝ) (k : d → ℤ) (i : Fin m) (hi : i ∉ carrierSites x₀ r k x) :
    physicalBlockPackets x₀ r h x k i = 0 := by
  apply packet_zero_outside_carrier
  simpa only [carrierSites, Finset.mem_filter, Finset.mem_univ, true_and] using hi

theorem physical_baseline_field (Q : ℕ) (ρ : ℝ) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (r h : ℝ) (hr : 0 < r) {m : ℕ} (x : Fin m → d → ℝ)
    (z : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) (i : Fin m) :
    packetField S (fun k => paperCoefficientAtoms Q ρ (extendBlockSample S z k)) x₀ r h (x i) =
      ∑ k : S, baselineBlockField Q ρ (physicalBlockCoordinates x₀ r x k.val)
        (physicalBlockPackets x₀ r h x k.val) (z k) i := by
  rw [packetField_eq_physical _ _ _ _ _ hr, ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro k _
  simp only [baselineBlockField, physicalBlockPackets, physicalBlockCoordinates,
    extendBlockSample, dif_pos k.property, localCoordinate]
  rfl

def physicalPartialCell (Q : ℕ) (ρ : ℝ) (side : Bool) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (r h a b t δ : ℝ) {m : ℕ} (x : Fin m → d → ℝ)
    (hq : ∀ k : S, (carrierSites x₀ r k.val x).card ≤ Q)
    (w : Fin m → Bool × Bool) (active : S → Bool)
    (z : S → MomentGrid (CoefficientExponent d Q) (4 * Q) × (Fin Q → Bool)) : ℝ :=
  jointFieldLikelihood side (fun i => sign (w i).1) (fun i => sign (w i).2) a b
    (fun i => packetEta S x₀ r h a t (x i)) (fun i => targetField x₀ h δ (x i))
    (fun i => ∑ k : S, activatedBlockField Q ρ t (carrierSites x₀ r k.val x)
      (siteCompletion Q _ (hq k)) (physicalBlockCoordinates x₀ r x k.val)
        (physicalBlockPackets x₀ r h x k.val) (active k, z k) i) / 4 ^ m

/-- Both the normalizer and the countable block labels are removed by proved
Bayes identities before applying the multiblock interpolation. -/
theorem physical_posterior_activation (Q : ℕ) (ρ : ℝ) (H : DiscreteLaw ℕ)
    (kernel : ℕ → FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q)))
    (θ ε : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (side : Bool) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (r h a b t δ : ℝ) (hr : 0 < r) {m : ℕ} (x : Fin m → d → ℝ)
    (hq : ∀ k : S, (carrierSites x₀ r k.val x).card ≤ Q)
    (hm : ComponentActivationIdentity Q H kernel ρ θ ε t hθ hθ1
      (fun k : S => carrierSites x₀ r k.val x) (fun k => siteCompletion Q _ (hq k))
      (fun k => physicalBlockCoordinates x₀ r x k.val) (fun k => physicalBlockPackets x₀ r h x k.val))
    (w : Fin m → Bool × Bool) :
    (tiltedBlockPrior Q S θ hθ hθ1 H kernel x₀ r m).expect
      (fun z => (∏ i, normalizedDesign Q S θ (extendLabels S z.1) x₀ r (x i)) *
        ∏ i, modelCellMass side S (paperCoefficientAtoms Q ρ) x₀ r h a b t δ (x i) (w i) z.2) /
      (tiltedBlockPrior Q S θ hθ hθ1 H kernel x₀ r m).expect
        (fun z => ∏ i, normalizedDesign Q S θ (extendLabels S z.1) x₀ r (x i)) =
    (FiniteLaw.independent (fun k : S => evaluatedBlockActivation H Q θ ε hθ hθ1
      (carrierSites x₀ r k.val x) (siteCompletion Q _ (hq k))
        (physicalBlockCoordinates x₀ r x k.val))).expect
      (fun active => (FiniteLaw.independent (fun _ : S =>
        (paperCoefficientLaw Q).prod (independentSigns (ι := Fin Q)))).expect
          (physicalPartialCell Q ρ side S x₀ r h a b t δ x hq w active)) := by
  rw [designPosterior_Bayes]
  rw [designPosterior_coefficient_expect H kernel Q S θ hθ hθ1 x₀ r x
    (fun z => ∏ i, modelCellMass side S (paperCoefficientAtoms Q ρ) x₀ r h a b t δ (x i) (w i) z)]
  have he := hm side (fun i => sign (w i).1) (fun i => sign (w i).2) a b
    (fun i => packetEta S x₀ r h a t (x i)) (fun i => targetField x₀ h δ (x i))
  have hf (z : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) :
      (∏ i, modelCellMass side S (paperCoefficientAtoms Q ρ) x₀ r h a b t δ (x i) (w i) z) =
        jointFieldLikelihood side (fun i => sign (w i).1) (fun i => sign (w i).2) a b
          (fun i => packetEta S x₀ r h a t (x i)) (fun i => targetField x₀ h δ (x i))
          (fun i => ∑ k : S, baselineBlockField Q ρ (physicalBlockCoordinates x₀ r x k.val)
            (physicalBlockPackets x₀ r h x k.val) (z k) i) / 4 ^ m := by
    simp only [modelCellMass, physical_baseline_field Q ρ S x₀ r h hr x z,
      Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      jointFieldLikelihood]
  unfold physicalPartialCell
  simp_rw [hf, div_eq_mul_inv, FiniteLaw.expect_mul_const]
  exact congrArg (fun v : ℝ => v / 4 ^ m) he

/-- A single constructed positive carrier gives the physical activation
formula simultaneously at every sample configuration with at most Q
observations in each carrier. No likelihood identity is assumed. -/
theorem paper_physical_posterior_activation (Q : ℕ) [NeZero Q] (ρ θ p B : ℝ)
    (hρ : 0 < ρ) (hθ : 0 < θ) (hθ1 : θ < 1) (hp : 0 < p)
    (hB : ((Q.choose 2 : ℝ) + 2) / 2 < B) :
    ∀ᶠ n : ℕ in atTop, ∃ (H : DiscreteLaw ℕ)
      (kernel : ℕ → FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q))),
      0 < H.weight 0 ∧ (∀ label z, 0 < (kernel label).weight z) ∧
      ∀ (m : ℕ) (side : Bool) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r h a b δ : ℝ), 0 < r →
        ∀ (x : Fin m → d → ℝ) (hq : ∀ k : S, (carrierSites x₀ r k.val x).card ≤ Q)
          (w : Fin m → Bool × Bool),
        let t := polynomialAmplitude p (n + 1)
        let ε := logarithmicThreshold p B (n + 1)
        (tiltedBlockPrior Q S θ hθ.le hθ1 H kernel x₀ r m).expect
          (fun z => (∏ i, normalizedDesign Q S θ (extendLabels S z.1) x₀ r (x i)) *
            ∏ i, modelCellMass side S (paperCoefficientAtoms Q ρ) x₀ r h a b t δ (x i) (w i) z.2) /
          (tiltedBlockPrior Q S θ hθ.le hθ1 H kernel x₀ r m).expect
            (fun z => ∏ i, normalizedDesign Q S θ (extendLabels S z.1) x₀ r (x i)) =
        (FiniteLaw.independent (fun k : S => evaluatedBlockActivation H Q θ ε hθ.le hθ1
          (carrierSites x₀ r k.val x) (siteCompletion Q _ (hq k))
            (physicalBlockCoordinates x₀ r x k.val))).expect
          (fun active => (FiniteLaw.independent (fun _ : S =>
            (paperCoefficientLaw Q).prod (independentSigns (ι := Fin Q)))).expect
              (physicalPartialCell Q ρ side S x₀ r h a b t δ x hq w active)) := by
  filter_upwards [paper_component_activation (d := d) Q ρ θ p B hρ hθ hθ1 hp hB] with n hn
  obtain ⟨H, kernel, h0, hk, hm⟩ := hn
  refine ⟨H, kernel, h0, hk, ?_⟩
  intro m side S x₀ r h a b δ hr x hq w
  apply physical_posterior_activation Q ρ H kernel θ _ hθ.le hθ1 side S x₀ r h a b _ δ hr x hq _ w
  exact hm (Fin m) S (fun k => carrierSites x₀ r k.val x)
    (fun k => Fin (Q - (carrierSites x₀ r k.val x).card))
    (fun k => siteCompletion Q _ (hq k)) (fun k => physicalBlockCoordinates x₀ r x k.val)
    (fun k => physicalBlockPackets x₀ r h x k.val) (fun k => physicalBlockPackets_zero x₀ r h x k.val)

end CausalLowerbound.PartB.ShellGeometry
