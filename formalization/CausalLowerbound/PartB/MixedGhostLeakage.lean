import CausalLowerbound.PartB.PhysicalGhostLeakage
import CausalLowerbound.PartB.DesignMarginals

/-! Integrate the actual physical ghost leakage under the common mixed
design distribution, retaining only the observations in one carrier. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open MeasureTheory
open scoped BigOperators Classical
namespace CausalLowerbound.PartB.ShellGeometry
open Wiener
attribute [local instance] Real.fact_zero_lt_one
local instance mixedGhostCircleMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance mixedGhostCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance mixedGhostCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {d K G Ω : Type*} [Fintype d] [DecidableEq d] [Fintype K] [Fintype G] [Fintype Ω]
local instance : BorelSpace (K → Torus d) := Pi.borelSpace

theorem carrierBox_eq_Icc (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r) (k : d → ℤ) :
    carrierBox x₀ r k = Set.Icc (fun a => x₀ a + r * k a - 2 * r)
      (fun a => x₀ a + r * k a + 2 * r) := by
  ext x
  constructor
  · intro hx
    constructor <;> intro a
    · have hh : -2 + (k a : ℝ) ≤ (x a - x₀ a) / r := by
        have := hx.1 a; change -2 ≤ (x a - x₀ a) / r - k a at this; linarith
      have := (le_div_iff₀ hr).mp hh
      dsimp
      nlinarith
    · have hh : (x a - x₀ a) / r ≤ 2 + (k a : ℝ) := by
        have := hx.2 a; change (x a - x₀ a) / r - k a ≤ 2 at this; linarith
      have := (div_le_iff₀ hr).mp hh
      dsimp
      nlinarith
  · intro hx
    constructor <;> intro a
    · have hh : -2 + (k a : ℝ) ≤ (x a - x₀ a) / r := by
        apply (le_div_iff₀ hr).mpr
        have := hx.1 a
        dsimp at this
        nlinarith
      change -2 ≤ (x a - x₀ a) / r - k a
      linarith
    · have hh : (x a - x₀ a) / r ≤ 2 + (k a : ℝ) := by
        apply (div_le_iff₀ hr).mpr
        have := hx.2 a
        dsimp at this
        nlinarith
      change (x a - x₀ a) / r - k a ≤ 2
      linarith

theorem carrierConfigurationBox_compact (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r) (k : d → ℤ) :
    IsCompact (carrierConfigurationBox (K := K) x₀ r k) := by
  simp only [carrierConfigurationBox, carrierBox_eq_Icc x₀ r hr k, Set.pi_univ_Icc]
  exact isCompact_Icc

def physicalGhostCost (H : DiscreteLaw ℕ) (Q : ℕ) (e : K ⊕ G ≃ Fin Q) (θ t : ℝ)
    (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ) : (K → d → ℝ) → ℝ :=
  (carrierConfigurationBox x₀ r k).indicator (fun x =>
    1 - ghostActivation H Q θ (completedTorusTaper Q e t)
      (fun i => torusProjection (carrierCoordinate (localCoordinate x₀ r k (x i)))))

theorem physicalGhostCost_regular (H : DiscreteLaw ℕ) (Q : ℕ) (e : K ⊕ G ≃ Fin Q)
    (θ t : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r) (k : d → ℤ) :
    Measurable (physicalGhostCost H Q e θ t x₀ r k) ∧
      Integrable (physicalGhostCost H Q e θ t x₀ r k) volume ∧
      ∀ x, 0 ≤ physicalGhostCost H Q e θ t x₀ r k x := by
  have hc : Continuous (fun x : K → d → ℝ =>
      1 - ghostActivation H Q θ (completedTorusTaper Q e t)
        (fun i => torusProjection (carrierCoordinate (localCoordinate x₀ r k (x i))))) := by
    apply continuous_const.sub
    apply (ghostActivation_continuous H Q θ hθ hθ1 _ (completedTorusTaper_continuous Q e t)).comp
    apply continuous_pi
    intro i
    apply torusProjection_quotient.continuous.comp
    unfold carrierCoordinate localCoordinate
    fun_prop
  have hbox := carrierConfigurationBox_measurable (K := K) x₀ r k
  refine ⟨hc.measurable.indicator hbox,
    (integrable_indicator_iff hbox).mpr
      (hc.continuousOn.integrableOn_compact (carrierConfigurationBox_compact x₀ r hr k)), ?_⟩
  intro x
  apply Set.indicator_nonneg
  intro y _
  exact sub_nonneg.mpr (ghostActivation_bounds H Q θ hθ hθ1 _
    (completedTorusTaper_continuous Q e t) (completedTorusTaper_bounds Q e t) _).2

theorem mixedDesign_physical_ghost_leakage [Nonempty d] (H : DiscreteLaw ℕ) (q : ℕ)
    (e : K ⊕ G ≃ Fin (q + 1)) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (s : ℝ) (hs : 0 < s) (hsd : s < (Fintype.card d : ℝ)) (t : ℝ) (ht : 0 < t)
    (S : Finset (d → ℤ)) (kernel : ℕ → FiniteLaw Ω) (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r)
    (k : d → ℤ) (n : ℕ) (v : K → Fin n) (hv : Function.Injective v) :
    (∫ x, physicalGhostCost H (q + 1) e θ t x₀ r k (fun i => x (v i))
      ∂mixedDesignExperiment (q + 1) S θ hθ hθ1 H kernel x₀ r n) ≤
      (designDensityCeiling d θ : ℝ) ^ Fintype.card K *
        ((4 * r) ^ (Fintype.card K * Fintype.card d) *
          (((1 + θ) ^ (q + 1) * ((q + 1 : ℝ) * ((2 * t) ^ s * collisionMomentBound d s ^ q))) /
            (1 - θ) ^ Fintype.card K)) := by
  obtain ⟨hm, hi, h0⟩ := physicalGhostCost_regular H (q + 1) e θ t hθ hθ1 x₀ r hr k
  have hb := mixedDesign_coordinate_integral_le (q + 1) S θ hθ hθ1 H kernel x₀ r n v hv
    (physicalGhostCost H (q + 1) e θ t x₀ r k) hm h0 hi
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [physicalGhostCost, integral_indicator (carrierConfigurationBox_measurable x₀ r k)]
  exact physical_ghost_leakage H q e θ hθ hθ1 s hs hsd t ht x₀ r hr k

end CausalLowerbound.PartB.ShellGeometry
