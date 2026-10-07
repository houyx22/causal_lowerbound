import CausalLowerbound.WienerAlgebra

/-! Pull a one-dimensional Wiener element into any coordinate. The
construction is on actual Fourier coefficients and its norm is at most
the original norm. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open UnitAddTorus
namespace CausalLowerbound.Wiener
variable {d : Type*} [Fintype d] [DecidableEq d]

def coordinateFrequency (i : d) (k : Fin 1 → ℤ) : d → ℤ := Pi.single i (k 0)

theorem coordinateFrequency_character (i : d) (k : Fin 1 → ℤ) (x : Torus d) :
    mFourier (coordinateFrequency i k) x = mFourier k (fun _ => x i) := by
  simp only [mFourier, ContinuousMap.coe_mk, coordinateFrequency]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j hj hji
    simp [Pi.single_eq_of_ne hji, fourier_zero]
  · simp

def liftCoordinate (i : d) : Fourier (Fin 1) →L[ℂ] Fourier d := regroup (coordinateFrequency i)

theorem liftCoordinate_norm (i : d) (a : Fourier (Fin 1)) : ‖liftCoordinate i a‖ ≤ ‖a‖ :=
  regroup_bound _ a

theorem liftCoordinate_value (i : d) (a : Fourier (Fin 1)) (x : Torus d) :
    toContinuous (liftCoordinate i a) x = toContinuous a (fun _ => x i) := by
  change synthesis mFourier 1 (fun _ => mFourier_norm.le) (regroup (coordinateFrequency i) a) x = _
  rw [synthesis_regroup]
  have h := (ContinuousMap.evalCLM ℂ x).map_tsum
    (summable_synthesis (fun k => mFourier (coordinateFrequency i k)) 1 (fun _ => mFourier_norm.le) a)
  have h' := (ContinuousMap.evalCLM ℂ (fun _ : Fin 1 => x i)).map_tsum
    (summable_synthesis mFourier 1 (fun _ => mFourier_norm.le) a)
  simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply,
    coordinateFrequency_character] at h h'
  exact h.trans h'.symm

end CausalLowerbound.Wiener
