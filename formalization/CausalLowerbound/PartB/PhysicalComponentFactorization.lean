import CausalLowerbound.PartB.ComponentFactorization
import CausalLowerbound.PartB.CoefficientIndependence
import CausalLowerbound.PartB.LikelihoodPolynomials
import CausalLowerbound.PartB.LegalBinaryModels

/-! Component factorization for the actual physical model, including
the Z^n-tilted prior and its normalized design likelihood. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
namespace CausalLowerbound.PartB.ShellGeometry
open Wiener
attribute [local instance] incidenceComponentFintype
variable {d Ω V : Type*} [Fintype d] [DecidableEq d] [Fintype Ω] [Inhabited Ω] [Fintype V]
local instance physicalComponentFintype (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (x : V → d → ℝ) : Fintype (observationGraph S x₀ r x).ConnectedComponent := by
  unfold observationGraph
  infer_instance

def extendBlockSample (S : Finset (d → ℤ)) (sample : S → Ω) (k : d → ℤ) : Ω :=
  if hk : k ∈ S then sample ⟨k, hk⟩ else default

theorem packet_zero_outside_carrier (G : (d → ℝ) → ℝ) (x₀ : d → ℝ)
    (r : ℝ) (k : d → ℤ) (x : d → ℝ) (hx : x ∉ carrierBox x₀ r k) :
    packet G x₀ r k x = 0 := by
  by_contra hn
  have hq : quadraticPartition (localCoordinate x₀ r k x) ≠ 0 := (mul_ne_zero_iff.mp hn).2
  have hb := quadraticPartition_support (subset_tsupport _ hq)
  apply hx
  exact ⟨fun i => (by norm_num : (-2 : ℝ) ≤ -1).trans (hb.1 i),
    fun i => (hb.2 i).trans (by norm_num : (1 : ℝ) ≤ 2)⟩

theorem packetField_incident_local {Q : ℕ} (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h : ℝ) (hr : 0 < r)
    (x : d → ℝ) (u v : S → Ω)
    (he : ∀ k : S, x ∈ carrierBox x₀ r k.val → u k = v k) :
    packetField S (fun k => atoms (extendBlockSample S u k)) x₀ r h x =
      packetField S (fun k => atoms (extendBlockSample S v k)) x₀ r h x := by
  rw [packetField_eq_physical _ _ _ _ _ hr, packetField_eq_physical _ _ _ _ _ hr]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hx : x ∈ carrierBox x₀ r k
  · simp only [extendBlockSample, dif_pos hk, he ⟨k, hk⟩ hx]
  · rw [packet_zero_outside_carrier _ x₀ r k x hx, zero_mul, zero_mul]

def modelCellMass {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h a b t δ : ℝ)
    (x : d → ℝ) (w : Bool × Bool) (u : S → Ω) : ℝ :=
  siteFieldLikelihood side (sign w.1) (sign w.2) a b (packetEta S x₀ r h a t x)
    (targetField x₀ h δ x) (packetField S (fun k => atoms (extendBlockSample S u k)) x₀ r h x) / 4

theorem modelCellMass_eq_conditional {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h a b t δ : ℝ)
    (x : d → ℝ) (w : Bool × Bool) (u : S → Ω)
    {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}
    (hlegal : (modelFields side S (fun k => atoms (extendBlockSample S u k)) x₀ r h a b t δ).Legal
      α β γ Lπ L₀ Lτ κ) (hκ : 0 ≤ κ) :
    modelCellMass side S atoms x₀ r h a b t δ x w u =
      ((modelFields side S (fun k => atoms (extendBlockSample S u k)) x₀ r h a b t δ).conditionalLaw
        hlegal hκ x).weight w := by
  rcases w with ⟨R, T⟩
  change _ = codedLikelihood _ _ _ _ _ / 4
  rw [model_codedLikelihood_eq_site]
  rfl

theorem modelCellMass_incident_local {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h a b t δ : ℝ) (hr : 0 < r)
    (x : d → ℝ) (w : Bool × Bool) (u v : S → Ω)
    (he : ∀ k : S, x ∈ carrierBox x₀ r k.val → u k = v k) :
    modelCellMass side S atoms x₀ r h a b t δ x w u =
      modelCellMass side S atoms x₀ r h a b t δ x w v := by
  unfold modelCellMass
  rw [packetField_incident_local S atoms x₀ r h hr x u v he]

def physicalCoefficientPosteriors (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (Q : ℕ) (S : Finset (d → ℤ)) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (x₀ : d → ℝ) (r : ℝ) {n : ℕ} (x : Fin n → d → ℝ) (k : S) : FiniteLaw Ω :=
  coefficientPosterior H kernel Q θ hθ hθ1 (fun i : carrierSites x₀ r k.val x =>
    torusProjection (carrierCoordinate (localCoordinate x₀ r k.val (x i.val))))

/-- The actual conditional cell mass factors over observation components.
Both the prior tilt and the design normalizer are discharged in this identity. -/
theorem physical_conditional_cell_factorization (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (Q : ℕ) (side : Bool) (S : Finset (d → ℤ)) (atoms : Ω → CoefficientExponent d Q → ℝ)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ) (r h a b t δ : ℝ) (hr : 0 < r)
    (n : ℕ) (x : Fin n → d → ℝ) (w : Fin n → Bool × Bool) :
    let inc := fun i (k : S) => x i ∈ carrierBox x₀ r k.val
    let f := fun i u => modelCellMass side S atoms x₀ r h a b t δ (x i) (w i) u
    let μ := physicalCoefficientPosteriors H kernel Q S θ hθ hθ1 x₀ r x
    (tiltedBlockPrior Q S θ hθ hθ1 H kernel x₀ r n).expect
      (fun z => (∏ i, normalizedDesign Q S θ (extendLabels S z.1) x₀ r (x i)) * ∏ i, f i z.2) /
      (tiltedBlockPrior Q S θ hθ hθ1 H kernel x₀ r n).expect
        (fun z => ∏ i, normalizedDesign Q S θ (extendLabels S z.1) x₀ r (x i)) =
      ∏ c : Option (observationGraph S x₀ r x).ConnectedComponent,
        (FiniteLaw.independent (fun k : {k // blockComponent inc k = c} => μ k.val)).expect
          (componentIntegrand inc f c) := by
  dsimp only
  rw [designPosterior_Bayes]
  rw [designPosterior_coefficient_expect H kernel Q S θ hθ hθ1 x₀ r x
    (fun u => ∏ i, modelCellMass side S atoms x₀ r h a b t δ (x i) (w i) u)]
  exact independent_incidence_factorization _ _ _ (fun i u v he =>
    modelCellMass_incident_local side S atoms x₀ r h a b t δ hr (x i) (w i) u v he)

end CausalLowerbound.PartB.ShellGeometry
