import CausalLowerbound.PartB.PhysicalComponentExperiments
import CausalLowerbound.PartB.ComponentLeakage
import CausalLowerbound.PartB.UniformLocalConstant

/-! The actual conditional Hellinger bound off the large-cluster event.
The constructed carrier works for all components at once. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Filter
open scoped BigOperators Classical
namespace CausalLowerbound.PartB.ShellGeometry
open Wiener
attribute [local instance] finOrderedDecEq finOrderedDecLt incidenceComponentFintype physicalComponentFintype
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem physical_global_hellinger_of_local (Q : ℕ) (hQ : 1 ≤ Q) (ρ : ℝ) (H : DiscreteLaw ℕ)
    (kernel : ℕ → FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q)))
    (θ ε : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ) (r h a b t : ℝ)
    (hr : 0 < r) (hrh : r ≤ h) {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ} (hκ : 0 < κ)
    (hlegal : ∀ (side : Bool) (z : activeBlocks (d := d) r h → MomentGrid (CoefficientExponent d Q) (4 * Q)),
      (modelFields side (activeBlocks r h) (fun k => paperCoefficientAtoms Q ρ (extendBlockSample (activeBlocks r h) z k))
        x₀ r h a b t (a * b * t ^ 2)).Legal α β γ Lπ L₀ Lτ κ)
    (hlocal : ∀ (m : ℕ) (y : Fin m → d → ℝ)
      (hq : ∀ k : activeBlocks (d := d) r h, (carrierSites x₀ r k.val y).card ≤ Q),
      (finitePhysicalConditional true (activeBlocks r h) (paperCoefficientAtoms Q ρ) x₀ r h a b t (a * b * t ^ 2)
        (fun _ => paperCoefficientLaw Q) (hlegal true) hκ.le y).hellingerSq
        (finitePhysicalConditional false (activeBlocks r h) (paperCoefficientAtoms Q ρ) x₀ r h a b t (a * b * t ^ 2)
          (physicalCoefficientPosteriors H kernel Q (activeBlocks r h) θ hθ hθ1 x₀ r y) (hlegal false) hκ.le y) ≤
        ((Fintype.card (Fin m → Bool × Bool) : ℝ) * (componentStabilityConstant m * (a * b * t ^ 2)) ^ 2 / (κ ^ 2) ^ m) *
          ∑ k : activeBlocks (d := d) r h, actualBlockLeakage H Q θ ε x₀ r k.val y (hq k))
    {n : ℕ} (x : Fin n → d → ℝ) (hx : x ∉ largeClusterEvent n Q x₀ r h) :
    (finitePhysicalConditional true (activeBlocks r h) (paperCoefficientAtoms Q ρ) x₀ r h a b t (a * b * t ^ 2)
      (fun _ => paperCoefficientLaw Q) (hlegal true) hκ.le x).hellingerSq
      (finitePhysicalConditional false (activeBlocks r h) (paperCoefficientAtoms Q ρ) x₀ r h a b t (a * b * t ^ 2)
        (physicalCoefficientPosteriors H kernel Q (activeBlocks r h) θ hθ hθ1 x₀ r x) (hlegal false) hκ.le x) ≤
      uniformInformationConstant κ Q * (a * b * t ^ 2) ^ 2 * globalGhostCost H Q θ ε x₀ r h x := by
  let S := activeBlocks (d := d) r h
  let inc := fun j (k : S) => x j ∈ carrierBox x₀ r k.val
  let m := fun c : Option (observationGraph S x₀ r x).ConnectedComponent => Fintype.card {i // siteComponent inc i = c}
  let e := fun c : Option (observationGraph S x₀ r x).ConnectedComponent => (Fintype.equivFin {i // siteComponent inc i = c}).symm
  have hm (c) : m c ≤ Q := component_fiber_small_off_largeCluster n Q hQ x₀ r h hr hrh x hx c
  let y := fun c => componentConfiguration S x₀ r x c (e c)
  have hq (c) (k : S) : (carrierSites x₀ r k.val (y c)).card ≤ Q :=
    (component_carrier_card_le S x₀ r x c (e c) k).trans (hm c)
  have hf (k : S) : (carrierSites x₀ r k.val x).card ≤ Q :=
    carrierSites_small_off_largeCluster n Q hQ x₀ r h hr hrh x hx k
  let C := uniformInformationConstant κ Q * (a * b * t ^ 2) ^ 2
  have hC : 0 ≤ C := mul_nonneg (uniformInformationConstant_nonneg κ Q) (sq_nonneg _)
  let leak := fun c => ∑ k : S, actualBlockLeakage H Q θ ε x₀ r k.val (y c) (hq c k)
  have hl0 (c) : 0 ≤ leak c := Finset.sum_nonneg
    (fun k _ => actualBlockLeakage_nonneg H Q θ ε hθ hθ1 x₀ r k.val (y c) (hq c k))
  have he := physical_posterior_component_hellinger S (paperCoefficientAtoms Q ρ)
    (fun _ => paperCoefficientLaw Q) H kernel θ hθ hθ1 x₀ r h a b t (a * b * t ^ 2) hr hlegal hκ.le x m e
  apply he.trans
  calc
    _ ≤ ∑ c, C * leak c := by
      apply Finset.sum_le_sum
      intro c _
      exact (hlocal (m c) (y c) (hq c)).trans
        (mul_le_mul_of_nonneg_right (localInformation_prefactor_le κ (a * b * t ^ 2) Q (m c) (hm c)) (hl0 c))
    _ = C * ∑ c, leak c := (Finset.mul_sum _ _ _).symm
    _ = C * ∑ k : S, actualBlockLeakage H Q θ ε x₀ r k.val x (hf k) := by
      congr 1
      exact component_leakage_sum H Q θ ε S x₀ r x m e hq hf
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (actual_total_leakage_le_globalGhostCost H Q θ ε hθ hθ1 x₀ r h hr x hf) hC

/-- A global conditional bound for the physical experiments, with the carrier
and all local matching identities constructed rather than assumed. -/
theorem paper_uniform_global_hellinger (Q : ℕ) [NeZero Q] (ρ θ p B : ℝ)
    (hρ : 0 < ρ) (hθ : 0 < θ) (hθ1 : θ < 1) (hp : 0 < p)
    (hB : ((Q.choose 2 : ℝ) + 2) / 2 < B) :
    ∀ᶠ N : ℕ in atTop, ∃ (H : DiscreteLaw ℕ)
      (kernel : ℕ → FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q))),
      0 < H.weight 0 ∧ (∀ label z, 0 < (kernel label).weight z) ∧
      ∀ (x₀ : d → ℝ) (r h a b : ℝ), 0 < r → 0 < h → r ≤ h → 0 < a → 0 ≤ b →
        a ^ 2 * polynomialAmplitude p (N + 1) ^ 2 ≤ 1 →
        a * b * polynomialAmplitude p (N + 1) ^ 2 ≤ 1 / 2 →
        ∀ (α β γ : Regularity) (Lπ L₀ Lτ κ : ℝ) (hκ : 0 < κ)
          (hlegal : ∀ (side : Bool) (z : activeBlocks (d := d) r h → MomentGrid (CoefficientExponent d Q) (4 * Q)),
            (modelFields side (activeBlocks r h)
              (fun k => paperCoefficientAtoms Q ρ (extendBlockSample (activeBlocks r h) z k))
              x₀ r h a b (polynomialAmplitude p (N + 1)) (a * b * polynomialAmplitude p (N + 1) ^ 2)).Legal
                α β γ Lπ L₀ Lτ κ)
          (n : ℕ) (x : Fin n → d → ℝ), x ∉ largeClusterEvent n Q x₀ r h →
        let t := polynomialAmplitude p (N + 1)
        let ε := logarithmicThreshold p B (N + 1)
        let P := finitePhysicalConditional true (activeBlocks r h) (paperCoefficientAtoms Q ρ) x₀ r h a b t (a * b * t ^ 2)
          (fun _ => paperCoefficientLaw Q) (hlegal true) hκ.le x
        let R := finitePhysicalConditional false (activeBlocks r h) (paperCoefficientAtoms Q ρ) x₀ r h a b t (a * b * t ^ 2)
          (physicalCoefficientPosteriors H kernel Q (activeBlocks r h) θ hθ.le hθ1 x₀ r x) (hlegal false) hκ.le x
        P.hellingerSq R ≤ uniformInformationConstant κ Q * (a * b * t ^ 2) ^ 2 *
          globalGhostCost H Q θ ε x₀ r h x := by
  filter_upwards [paper_uniform_local_hellinger (d := d) Q ρ θ p B hρ hθ hθ1 hp hB] with N hN
  obtain ⟨H, kernel, h0, hk, hl⟩ := hN
  refine ⟨H, kernel, h0, hk, ?_⟩
  intro x₀ r h a b hr hh hrh ha hb hat hδ α β γ Lπ L₀ Lτ κ hκ hlegal n x hx
  exact physical_global_hellinger_of_local Q (Nat.one_le_iff_ne_zero.mpr (NeZero.ne Q)) ρ H kernel
    θ (logarithmicThreshold p B (N + 1)) hθ.le hθ1 x₀ r h a b (polynomialAmplitude p (N + 1))
    hr hrh hκ hlegal
    (fun m y hq => hl x₀ r h a b hr hh ha hb hat hδ m y hq α β γ Lπ L₀ Lτ κ hκ hlegal) x hx

end CausalLowerbound.PartB.ShellGeometry
