import CausalLowerbound.WienerAlgebra

/-! Translation of the spatial argument, realized in the actual Fourier
coefficient space. Unlike frequency regrouping, this multiplies each
coefficient by a unit-modulus character and preserves the Wiener norm. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open UnitAddTorus

namespace CausalLowerbound.Wiener
variable {d : Type*} [Fintype d]

theorem mFourier_spatial_add (k : d → ℤ) (x y : Torus d) :
    mFourier k (x + y) = mFourier k x * mFourier k y := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply,
    zsmul_add, AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

theorem mFourier_point_norm (k : d → ℤ) (x : Torus d) : ‖mFourier k x‖ = 1 := by
  simp only [mFourier, ContinuousMap.coe_mk, fourier_apply, norm_prod,
    Circle.norm_coe, Finset.prod_const_one]

def spatialShift (z : Torus d) : Fourier d →L[ℂ] Fourier d :=
  synthesis (fun k => mFourier k z • characterSeries k) 1 (fun k => by
    rw [norm_smul, mFourier_point_norm, characterSeries_norm, one_mul])

theorem spatialShift_bound (z : Torus d) (a : Fourier d) : ‖spatialShift z a‖ ≤ ‖a‖ := by
  simpa only [one_mul] using norm_synthesis
    (fun k => mFourier k z • characterSeries k) 1 (fun k => by
      rw [norm_smul, mFourier_point_norm, characterSeries_norm, one_mul]) a

theorem spatialShift_value (z : Torus d) (a : Fourier d) (x : Torus d) :
    toContinuous (spatialShift z a) x = toContinuous a (x + z) := by
  have hs := summable_synthesis (fun k => mFourier k z • characterSeries k) 1
    (fun k => by rw [norm_smul, mFourier_point_norm, characterSeries_norm, one_mul]) a
  change toContinuous (∑' k, a k • (mFourier k z • characterSeries k)) x = _
  rw [toContinuous.map_tsum hs]
  have he := (ContinuousMap.evalCLM ℂ x).map_tsum (toContinuous.summable hs)
  rw [show (∑' k, toContinuous (a k • (mFourier k z • characterSeries k))) x =
    ∑' k, toContinuous (a k • (mFourier k z • characterSeries k)) x from he]
  have hr := (ContinuousMap.evalCLM ℂ (x + z)).map_tsum
    (summable_synthesis mFourier 1 (fun _ => mFourier_norm.le) a)
  simp only [ContinuousMap.evalCLM_apply] at hr
  change _ = (∑' k, a k • mFourier k) (x + z)
  rw [hr]
  apply tsum_congr
  intro k
  simp only [map_smul, characterSeries_toContinuous, ContinuousMap.smul_apply,
    smul_eq_mul, ContinuousMap.evalCLM_apply, mFourier_spatial_add]
  ring

theorem spatialShift_neg_cancel (z : Torus d) (a : Fourier d) :
    spatialShift (-z) (spatialShift z a) = a := by
  apply toContinuous_injective
  ext x
  simp only [spatialShift_value, neg_add_cancel_right]

theorem spatialShift_norm (z : Torus d) (a : Fourier d) : ‖spatialShift z a‖ = ‖a‖ := by
  apply le_antisymm (spatialShift_bound z a)
  have h := spatialShift_bound (-z) (spatialShift z a)
  rwa [spatialShift_neg_cancel] at h

end CausalLowerbound.Wiener
