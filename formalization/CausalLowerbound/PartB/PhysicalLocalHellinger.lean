import CausalLowerbound.PartB.PhysicalRetainedLikelihood
import CausalLowerbound.PartB.PhysicalFiniteExperiment
import CausalLowerbound.PartB.EffectiveActivation

/-! A local Hellinger bound for the actual legal physical experiments.
The partial-shift equality, stability, and positive cell bound are all
proved from the physical model rather than supplied as hypotheses. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators Classical
open Filter
namespace CausalLowerbound.PartB.ShellGeometry
open Wiener
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem physical_finite_activation (Q : ℕ) (ρ : ℝ) (H : DiscreteLaw ℕ)
    (kernel : ℕ → FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q)))
    (θ ε : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ) (r h a b t : ℝ) (hr : 0 < r)
    {m : ℕ} (x : Fin m → d → ℝ)
    (hq : ∀ k : activeBlocks (d := d) r h, (carrierSites x₀ r k.val x).card ≤ Q)
    (hm : ComponentActivationIdentity Q H kernel ρ θ ε t hθ hθ1
      (fun k : activeBlocks (d := d) r h => carrierSites x₀ r k.val x) (fun k => siteCompletion Q _ (hq k))
      (fun k => physicalBlockCoordinates x₀ r x k.val) (fun k => physicalBlockPackets x₀ r h x k.val))
    {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}
    (hlegal : ∀ z : activeBlocks (d := d) r h → MomentGrid (CoefficientExponent d Q) (4 * Q),
      (modelFields false (activeBlocks r h) (fun k => paperCoefficientAtoms Q ρ (extendBlockSample (activeBlocks r h) z k))
        x₀ r h a b t (a * b * t ^ 2)).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) (w : Fin m → Bool × Bool) :
    (finitePhysicalConditional false (activeBlocks r h) (paperCoefficientAtoms Q ρ) x₀ r h a b t (a * b * t ^ 2)
      (physicalCoefficientPosteriors H kernel Q (activeBlocks r h) θ hθ hθ1 x₀ r x) hlegal hκ x).weight w =
    (FiniteLaw.independent (fun k : activeBlocks (d := d) r h => evaluatedBlockActivation H Q θ ε hθ hθ1
      (carrierSites x₀ r k.val x) (siteCompletion Q _ (hq k)) (physicalBlockCoordinates x₀ r x k.val))).expect
      (fun active => (FiniteLaw.independent (fun _ : activeBlocks (d := d) r h => paperCoefficientLaw Q)).expect
        (fun z => freshJitterCell x₀ r h a b t x
          (physicalBaselineValues Q ρ (activeBlocks r h) x₀ r h x z) active w)) := by
  have he := physical_posterior_activation Q ρ H kernel θ ε hθ hθ1 false (activeBlocks r h)
    x₀ r h a b t (a * b * t ^ 2) hr x hq hm w
  rw [designPosterior_Bayes] at he
  rw [designPosterior_coefficient_expect H kernel Q (activeBlocks r h) θ hθ hθ1 x₀ r x
    (fun z => ∏ i, modelCellMass false (activeBlocks r h) (paperCoefficientAtoms Q ρ)
      x₀ r h a b t (a * b * t ^ 2) (x i) (w i) z)] at he
  simp_rw [physicalPartialCell_fresh Q ρ x₀ r h a b t hr x hq w] at he
  rw [finitePhysicalConditional_weight]
  exact he

theorem physical_local_hellinger (Q : ℕ) (ρ : ℝ) (H : DiscreteLaw ℕ)
    (kernel : ℕ → FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q)))
    (θ ε : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ) (r h a b t : ℝ)
    (hr : 0 < r) (hh : 0 < h) (ha : 0 < a) (hb : 0 ≤ b) (hat : a ^ 2 * t ^ 2 ≤ 1)
    (hδ : a * b * t ^ 2 ≤ 1 / 2) {m : ℕ} (x : Fin m → d → ℝ)
    (hq : ∀ k : activeBlocks (d := d) r h, (carrierSites x₀ r k.val x).card ≤ Q)
    (hm : ComponentActivationIdentity Q H kernel ρ θ ε t hθ hθ1
      (fun k : activeBlocks (d := d) r h => carrierSites x₀ r k.val x) (fun k => siteCompletion Q _ (hq k))
      (fun k => physicalBlockCoordinates x₀ r x k.val) (fun k => physicalBlockPackets x₀ r h x k.val))
    {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ} (hκ : 0 < κ)
    (hlegal : ∀ (side : Bool) (z : activeBlocks (d := d) r h → MomentGrid (CoefficientExponent d Q) (4 * Q)),
      (modelFields side (activeBlocks r h) (fun k => paperCoefficientAtoms Q ρ (extendBlockSample (activeBlocks r h) z k))
        x₀ r h a b t (a * b * t ^ 2)).Legal α β γ Lπ L₀ Lτ κ) :
    let P := finitePhysicalConditional true (activeBlocks r h) (paperCoefficientAtoms Q ρ) x₀ r h a b t (a * b * t ^ 2)
      (fun _ => paperCoefficientLaw Q) (hlegal true) hκ.le x
    let R := finitePhysicalConditional false (activeBlocks r h) (paperCoefficientAtoms Q ρ) x₀ r h a b t (a * b * t ^ 2)
      (physicalCoefficientPosteriors H kernel Q (activeBlocks r h) θ hθ hθ1 x₀ r x) (hlegal false) hκ.le x
    P.hellingerSq R ≤
      ((Fintype.card (Fin m → Bool × Bool) : ℝ) * (componentStabilityConstant m * (a * b * t ^ 2)) ^ 2 / (κ ^ 2) ^ m) *
        ∑ k : activeBlocks (d := d) r h, if (carrierSites x₀ r k.val x).Nonempty then
          1 - evaluatedBlockWeight H Q θ ε (carrierSites x₀ r k.val x)
            (siteCompletion Q _ (hq k)) (physicalBlockCoordinates x₀ r x k.val) else 0 := by
  dsimp only
  let P := finitePhysicalConditional true (activeBlocks r h) (paperCoefficientAtoms Q ρ) x₀ r h a b t (a * b * t ^ 2)
    (fun _ => paperCoefficientLaw Q) (hlegal true) hκ.le x
  let R := finitePhysicalConditional false (activeBlocks r h) (paperCoefficientAtoms Q ρ) x₀ r h a b t (a * b * t ^ 2)
    (physicalCoefficientPosteriors H kernel Q (activeBlocks r h) θ hθ hθ1 x₀ r x) (hlegal false) hκ.le x
  let χ : activeBlocks (d := d) r h → ℝ := fun k => evaluatedBlockWeight H Q θ ε
    (carrierSites x₀ r k.val x) (siteCompletion Q _ (hq k)) (physicalBlockCoordinates x₀ r x k.val)
  have hχ (k : activeBlocks (d := d) r h) : 0 ≤ χ k ∧ χ k ≤ 1 :=
    evaluatedBlockWeight_bounds H Q θ ε hθ hθ1 _ _ _
  let A := activationProduct χ (fun k => (hχ k).1) (fun k => (hχ k).2)
  let F := fun active (w : Fin m → Bool × Bool) =>
    (FiniteLaw.independent (fun _ : activeBlocks (d := d) r h => paperCoefficientLaw Q)).expect
      (fun z => freshJitterCell x₀ r h a b t x
        (physicalBaselineValues Q ρ (activeBlocks r h) x₀ r h x z) active w)
  have hR (w : Fin m → Bool × Bool) : R.weight w = A.expect (fun active => F active w) :=
    physical_finite_activation Q ρ H kernel θ ε hθ hθ1 x₀ r h a b t hr x hq hm (hlegal false) hκ.le w
  have hfull (w : Fin m → Bool × Bool) : F (fun _ => true) w = P.weight w := by
    dsimp only [F, P]
    simp_rw [freshJitterCell_full x₀ r h a b t hr hh ha.ne']
    rw [finitePhysicalConditional_weight]
    rfl
  have herr (active) (w : Fin m → Bool × Bool) :
      |F active w - P.weight w| ≤ componentStabilityConstant m * (a * b * t ^ 2) := by
    dsimp only [F, P]
    rw [finitePhysicalConditional_weight, ← FiniteLaw.expect_sub]
    apply FiniteLaw.abs_expect_le_bound
    intro z
    exact freshJitterCell_stability x₀ r h a b t hr hh ha hb hat hδ x
      (physicalBaselineValues Q ρ (activeBlocks r h) x₀ r h x z)
      (fun i => legal_model_propensity_abs true (activeBlocks r h)
        (fun k => paperCoefficientAtoms Q ρ (extendBlockSample (activeBlocks r h) z k))
        x₀ r h a b t (a * b * t ^ 2) (hlegal true z) hκ.le (x i)) w
      (fun i => modelCellMass_abs_le_one true (activeBlocks r h) (paperCoefficientAtoms Q ρ)
        x₀ r h a b t (a * b * t ^ 2) (x i) (w i) z (hlegal true z) hκ.le) active
  have hs (w : Fin m → Bool × Bool) :
      (P.weight w - R.weight w) ^ 2 ≤ (componentStabilityConstant m * (a * b * t ^ 2)) ^ 2 *
        ∑ k, if (carrierSites x₀ r k.val x).Nonempty then 1 - χ k else 0 := by
    rw [hR, sub_sq_comm]
    have he := effective_activation_sq_error χ (fun k => (carrierSites x₀ r k.val x).Nonempty)
      (fun k => (hχ k).1) (fun k => (hχ k).2) (fun active => F active w) (P.weight w)
      (componentStabilityConstant m * (a * b * t ^ 2)) (by
        intro k hk active v
        dsimp only [F]
        apply FiniteLaw.expect_congr
        intro z
        exact freshJitterCell_ignore x₀ r h a b t x _ active w k hk v)
      (hfull w) (fun active => herr active w)
    convert he using 1
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : (carrierSites x₀ r k.val x).Nonempty <;> simp [hk]
  have he := FiniteLaw.hellingerSq_le_of_sq_error P R ((κ ^ 2) ^ m)
    ((componentStabilityConstant m * (a * b * t ^ 2)) ^ 2 *
      ∑ k, if (carrierSites x₀ r k.val x).Nonempty then 1 - χ k else 0)
    (pow_pos (sq_pos_of_pos hκ) m)
    (fun w => finitePhysicalConditional_lower true (activeBlocks r h) (paperCoefficientAtoms Q ρ)
      x₀ r h a b t (a * b * t ^ 2) (fun _ => paperCoefficientLaw Q) (hlegal true) hκ.le x w) hs
  convert he using 1 <;> ring

/-- Construct the same positive carrier once for all physical configurations.
The local information bound has no moment-matching, partial-shift, or
cell-separation assumption; model legality is the property proved in item 2. -/
theorem paper_uniform_local_hellinger (Q : ℕ) [NeZero Q] (ρ θ p B : ℝ)
    (hρ : 0 < ρ) (hθ : 0 < θ) (hθ1 : θ < 1) (hp : 0 < p)
    (hB : ((Q.choose 2 : ℝ) + 2) / 2 < B) :
    ∀ᶠ n : ℕ in atTop, ∃ (H : DiscreteLaw ℕ)
      (kernel : ℕ → FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q))),
      0 < H.weight 0 ∧ (∀ label z, 0 < (kernel label).weight z) ∧
      ∀ (x₀ : d → ℝ) (r h a b : ℝ), 0 < r → 0 < h → 0 < a → 0 ≤ b →
        a ^ 2 * polynomialAmplitude p (n + 1) ^ 2 ≤ 1 →
        a * b * polynomialAmplitude p (n + 1) ^ 2 ≤ 1 / 2 →
        ∀ (m : ℕ) (x : Fin m → d → ℝ)
          (hq : ∀ k : activeBlocks (d := d) r h, (carrierSites x₀ r k.val x).card ≤ Q)
          (α β γ : Regularity) (Lπ L₀ Lτ κ : ℝ) (hκ : 0 < κ)
          (hlegal : ∀ (side : Bool) (z : activeBlocks (d := d) r h → MomentGrid (CoefficientExponent d Q) (4 * Q)),
            (modelFields side (activeBlocks r h)
              (fun k => paperCoefficientAtoms Q ρ (extendBlockSample (activeBlocks r h) z k))
              x₀ r h a b (polynomialAmplitude p (n + 1)) (a * b * polynomialAmplitude p (n + 1) ^ 2)).Legal
                α β γ Lπ L₀ Lτ κ),
        let t := polynomialAmplitude p (n + 1)
        let ε := logarithmicThreshold p B (n + 1)
        let P := finitePhysicalConditional true (activeBlocks r h) (paperCoefficientAtoms Q ρ) x₀ r h a b t (a * b * t ^ 2)
          (fun _ => paperCoefficientLaw Q) (hlegal true) hκ.le x
        let R := finitePhysicalConditional false (activeBlocks r h) (paperCoefficientAtoms Q ρ) x₀ r h a b t (a * b * t ^ 2)
          (physicalCoefficientPosteriors H kernel Q (activeBlocks r h) θ hθ.le hθ1 x₀ r x) (hlegal false) hκ.le x
        P.hellingerSq R ≤
          ((Fintype.card (Fin m → Bool × Bool) : ℝ) * (componentStabilityConstant m * (a * b * t ^ 2)) ^ 2 / (κ ^ 2) ^ m) *
            ∑ k : activeBlocks (d := d) r h, if (carrierSites x₀ r k.val x).Nonempty then
              1 - evaluatedBlockWeight H Q θ ε (carrierSites x₀ r k.val x)
                (siteCompletion Q _ (hq k)) (physicalBlockCoordinates x₀ r x k.val) else 0 := by
  filter_upwards [paper_component_activation (d := d) Q ρ θ p B hρ hθ hθ1 hp hB] with n hn
  obtain ⟨H, kernel, h0, hk, hm⟩ := hn
  refine ⟨H, kernel, h0, hk, ?_⟩
  intro x₀ r h a b hr hh ha hb hat hδ m x hq α β γ Lπ L₀ Lτ κ hκ hlegal
  have hi := hm (Fin m) (activeBlocks (d := d) r h) (fun k => carrierSites x₀ r k.val x)
    (fun k => Fin (Q - (carrierSites x₀ r k.val x).card)) (fun k => siteCompletion Q _ (hq k))
    (fun k => physicalBlockCoordinates x₀ r x k.val) (fun k => physicalBlockPackets x₀ r h x k.val)
    (fun k => physicalBlockPackets_zero x₀ r h x k.val)
  exact physical_local_hellinger Q ρ H kernel θ _ hθ.le hθ1 x₀ r h a b _ hr hh ha hb hat hδ x hq hi hκ hlegal

end CausalLowerbound.PartB.ShellGeometry
