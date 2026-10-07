import CausalLowerbound.PartB.ConcreteGhostLeakage

/-! The physical ghost integral, including the affine Jacobian on the
actual carrier boxes. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open MeasureTheory
open scoped BigOperators Classical
namespace CausalLowerbound.PartB.ShellGeometry
open Wiener
attribute [local instance] Real.fact_zero_lt_one
local instance physicalGhostCircleMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalGhostCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance physicalGhostCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {d K G : Type*} [Fintype d] [DecidableEq d] [Fintype K] [Fintype G]
local instance : BorelSpace (K → Torus d) := Pi.borelSpace

def carrierConfigurationBox (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ) : Set (K → d → ℝ) :=
  Set.univ.pi (fun _ => carrierBox x₀ r k)

theorem carrierConfigurationBox_measurable (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ) :
    MeasurableSet (carrierConfigurationBox (K := K) x₀ r k) :=
  MeasurableSet.univ_pi (fun _ => carrierBox_measurable x₀ r k)

theorem torusProjection_pi_cube_integral (g : (K → Torus d) → ℝ) (hg : Continuous g) :
    (∫ u : K → d → ℝ, g (fun i => torusProjection (u i)) ∂Measure.pi (fun _ : K => cubeMeasure d)) =
      ∫ u : K → Torus d, g u := by
  have hm := torusProjection_pi_cube_preserving (d := d) (J := K)
  have he := integral_map (μ := Measure.pi (fun _ : K => cubeMeasure d))
    hm.measurable.aemeasurable hg.aestronglyMeasurable
  rw [hm.map_eq] at he
  exact he.symm

theorem physical_carrier_integral (g : (K → Torus d) → ℝ) (hg : Continuous g)
    (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r) (k : d → ℤ) :
    (∫ x in carrierConfigurationBox (K := K) x₀ r k,
      g (fun i => torusProjection (carrierCoordinate (localCoordinate x₀ r k (x i))))) =
      (4 * r) ^ (Fintype.card K * Fintype.card d) * ∫ u : K → Torus d, g u := by
  let C : Set (K → d → ℝ) := Set.univ.pi (fun _ => Set.Icc (0 : d → ℝ) 1)
  let f : (K → d → ℝ) → ℝ := C.indicator (fun u => g (fun i => torusProjection (u i)))
  let corner : K → d → ℝ := fun _ a => x₀ a + r * k a - 2 * r
  have hC : MeasurableSet C := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hf : (∫ u, f u) = ∫ u : K → Torus d, g u := by
    rw [integral_indicator hC]
    have hm : (volume : Measure (K → d → ℝ)).restrict C =
        Measure.pi (fun _ : K => cubeMeasure d) := by
      exact Measure.restrict_pi_pi (fun _ : K => (volume : Measure (d → ℝ))) _
    rw [hm]
    exact torusProjection_pi_cube_integral g hg
  have hcoord (x : K → d → ℝ) :
      (fun i => carrierCoordinate (localCoordinate x₀ r k (x i))) = (4 * r)⁻¹ • (x - corner) := by
    funext i a
    dsimp [carrierCoordinate, localCoordinate, corner]
    field_simp
    ring
  have hmem (x : K → d → ℝ) :
      (fun i => carrierCoordinate (localCoordinate x₀ r k (x i))) ∈ C ↔
        x ∈ carrierConfigurationBox x₀ r k := by
    simp only [C, carrierConfigurationBox, Set.mem_pi, Set.mem_univ, forall_const]
    exact forall_congr' (fun i => carrierCoordinate_mem_unit_iff (localCoordinate x₀ r k (x i)))
  have hind : (carrierConfigurationBox x₀ r k).indicator
      (fun x : K → d → ℝ => g (fun i => torusProjection (carrierCoordinate (localCoordinate x₀ r k (x i))))) =
      fun x => f ((4 * r)⁻¹ • (x - corner)) := by
    funext x
    rw [← hcoord]
    by_cases hx : x ∈ carrierConfigurationBox x₀ r k
    · rw [Set.indicator_of_mem hx]
      dsimp only [f]
      rw [Set.indicator_of_mem ((hmem x).mpr hx)]
    · rw [Set.indicator_of_not_mem hx]
      dsimp only [f]
      rw [Set.indicator_of_not_mem (mt (hmem x).mp hx)]
  rw [← integral_indicator (carrierConfigurationBox_measurable x₀ r k), hind]
  rw [integral_sub_right_eq_self (fun y => f ((4 * r)⁻¹ • y)) corner]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume f (by positivity : 0 ≤ 4 * r), hf]
  simp only [Module.finrank_pi_fintype, Module.finrank_pi, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, smul_eq_mul, Module.finrank_self, mul_one]

theorem physical_ghost_leakage [Nonempty d] (H : DiscreteLaw ℕ) (q : ℕ)
    (e : K ⊕ G ≃ Fin (q + 1)) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (s : ℝ) (hs : 0 < s) (hsd : s < (Fintype.card d : ℝ)) (t : ℝ) (ht : 0 < t)
    (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r) (k : d → ℤ) :
    (∫ x in carrierConfigurationBox (K := K) x₀ r k,
      1 - ghostActivation H (q + 1) θ (completedTorusTaper (q + 1) e t)
        (fun i => torusProjection (carrierCoordinate (localCoordinate x₀ r k (x i))))) ≤
      (4 * r) ^ (Fintype.card K * Fintype.card d) *
        (((1 + θ) ^ (q + 1) * ((q + 1 : ℝ) * ((2 * t) ^ s * collisionMomentBound d s ^ q))) /
          (1 - θ) ^ Fintype.card K) := by
  rw [physical_carrier_integral _ (continuous_const.sub
    (ghostActivation_continuous H (q + 1) θ hθ hθ1 _ (completedTorusTaper_continuous _ _ _))) x₀ r hr k]
  exact mul_le_mul_of_nonneg_left (concrete_ghost_leakage H q e θ hθ hθ1 s hs hsd t ht)
    (pow_nonneg (by positivity) _)

end CausalLowerbound.PartB.ShellGeometry
