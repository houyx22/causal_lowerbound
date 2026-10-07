import CausalLowerbound.WienerLattice
import CausalLowerbound.WienerTensor

/-!
# Fourier pullback on a finite configuration graph

All edge variables are pulled back simultaneously. Shared vertices and cycles
are allowed; no independence assumption is imposed on the edge differences.
The input is a coefficient decay bound, not yet the paper's derivative bound.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators
open UnitAddTorus

namespace CausalLowerbound.Wiener

theorem fourier_eval_sub (n : ℤ) (x y : UnitAddCircle) :
    fourier n (x - y) = fourier n x * fourier (-n) y := by
  simp only [fourier_apply, sub_eq_add_neg, smul_add, smul_neg, neg_smul,
    AddCircle.toCircle_add, Circle.coe_mul]

variable {d : Type*} [Fintype d]

theorem mFourier_eval_sub (k : d → ℤ) (x y : Torus d) :
    mFourier k (x - y) = mFourier k x * mFourier (-k) y := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.sub_apply, fourier_eval_sub,
    Finset.prod_mul_distrib, Pi.neg_apply]

theorem mFourier_finset_sum {α : Type*} (s : Finset α) (k : α → d → ℤ) (x : Torus d) :
    mFourier (∑ i ∈ s, k i) x = ∏ i ∈ s, mFourier (k i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mFourier_zero]
  | @insert i s hi ih => simp [hi, mFourier_add, ih]

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]

def configurationLift (a b : E → ι) (x : Torus (ι × d)) : Torus ((ι × d) ⊕ (E × d)) :=
  Sum.elim x (fun p => x (a p.1, p.2) - x (b p.1, p.2))

def configurationFrequency (a b : E → ι) (k : ((ι × d) ⊕ (E × d)) → ℤ) : (ι × d) → ℤ :=
  (fun p => k (Sum.inl p)) + ∑ e,
    (slotFrequency (a e) (fun j => k (Sum.inr (e, j))) +
      slotFrequency (b e) (fun j => -k (Sum.inr (e, j))))

theorem configuration_character (a b : E → ι)
    (k : ((ι × d) ⊕ (E × d)) → ℤ) (x : Torus (ι × d)) :
    mFourier (configurationFrequency a b k) x = mFourier k (configurationLift a b x) := by
  have hr : mFourier k (configurationLift a b x) =
      mFourier (fun p => k (Sum.inl p)) x * ∏ e,
        mFourier (fun j => k (Sum.inr (e, j)))
          ((fun j => x (a e, j)) - (fun j => x (b e, j))) := by
    simp only [mFourier, configurationLift, ContinuousMap.coe_mk,
      Fintype.prod_sum_type, Fintype.prod_prod_type, Sum.elim_inl, Sum.elim_inr, Pi.sub_apply]
  rw [hr]
  simp only [configurationFrequency, mFourier_add, mFourier_finset_sum,
    slotFrequency_character, mFourier_eval_sub]
  rfl

def configurationPullback (a b : E → ι) :
    Fourier ((ι × d) ⊕ (E × d)) →L[ℂ] Fourier (ι × d) :=
  regroup (configurationFrequency a b)

theorem configurationPullback_bound (a b : E → ι) (f : Fourier ((ι × d) ⊕ (E × d))) :
    ‖configurationPullback a b f‖ ≤ ‖f‖ := regroup_bound _ f

theorem configurationPullback_value (a b : E → ι)
    (f : Fourier ((ι × d) ⊕ (E × d))) (x : Torus (ι × d)) :
    toContinuous (configurationPullback a b f) x = toContinuous f (configurationLift a b x) := by
  change synthesis mFourier 1 (fun _ => mFourier_norm.le)
    (regroup (configurationFrequency a b) f) x = _
  rw [synthesis_regroup]
  have h := (ContinuousMap.evalCLM ℂ x).map_tsum
    (summable_synthesis (fun k => mFourier (configurationFrequency a b k)) 1
      (fun _ => mFourier_norm.le) f)
  have h' := (ContinuousMap.evalCLM ℂ (configurationLift a b x)).map_tsum
    (summable_synthesis mFourier 1 (fun _ => mFourier_norm.le) f)
  simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply,
    configuration_character] at h h'
  exact h.trans h'.symm

/-- A graph pullback obeys a uniform Wiener bound once the rescaled profile's
Fourier coefficients satisfy the mixed-derivative decay estimate. -/
theorem configurationPullback_of_decay (a b : E → ι)
    (N : ((ι × d) ⊕ (E × d)) → ℕ) (hN : ∀ i, N i ≠ 0)
    (C : ℝ) (hC : 0 ≤ C) (c : (((ι × d) ⊕ (E × d)) → ℤ) → ℂ)
    (hc : ∀ k, ‖c k‖ ≤ C * anisotropicKernel N k) :
    ‖configurationPullback a b (fourierOfDecay N hN C c hc)‖ ≤
      C * latticeConstant ^ (Fintype.card d * (Fintype.card ι + Fintype.card E)) := by
  have h := (configurationPullback_bound a b (fourierOfDecay N hN C c hc)).trans
    (fourierOfDecay_bound N hN C hC c hc)
  simpa only [Fintype.card_sum, Fintype.card_prod, Nat.mul_add, Nat.mul_comm] using h

end CausalLowerbound.Wiener
