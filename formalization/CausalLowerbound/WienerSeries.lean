import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Absolute Fourier coefficient series

The coefficient space is the actual complete ℓ¹ space. In particular its norm
is an infinite sum, and synthesis and regrouping are bounded linear maps.
Regrouping need not be injective: this is the operation needed when edges of
a configuration graph share vertices and their frequencies collide.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal

namespace CausalLowerbound
namespace Wiener

abbrev Series (ι : Type*) (𝕜 : Type*) [NormedAddCommGroup 𝕜] := lp (fun _ : ι => 𝕜) 1

variable {ι κ 𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem hasSum_norm (a : Series ι 𝕜) : HasSum (fun i => ‖a i‖) ‖a‖ := by
  simpa using lp.hasSum_norm (p := 1) (by norm_num) a

theorem summable_norm (a : Series ι 𝕜) : Summable (fun i => ‖a i‖) :=
  (hasSum_norm a).summable

theorem norm_eq_tsum (a : Series ι 𝕜) : ‖a‖ = ∑' i, ‖a i‖ :=
  (hasSum_norm a).tsum_eq.symm

def entry (i : ι) : Series ι 𝕜 →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun a => a i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun a => by simpa only [one_mul] using lp.norm_apply_le_norm (by norm_num) a i)

@[simp]
theorem entry_apply (i : ι) (a : Series ι 𝕜) : entry i a = a i := rfl

variable [CompleteSpace E]

theorem summable_synthesis (v : ι → E) (M : ℝ) (hv : ∀ i, ‖v i‖ ≤ M)
    (a : Series ι 𝕜) : Summable (fun i => a i • v i) := by
  apply Summable.of_norm_bounded (fun i => M * ‖a i‖) ((summable_norm a).mul_left M)
  intro i
  rw [norm_smul, mul_comm M]
  exact mul_le_mul_of_nonneg_left (hv i) (norm_nonneg _)

omit [CompleteSpace E] in
theorem norm_synthesis (v : ι → E) (M : ℝ) (hv : ∀ i, ‖v i‖ ≤ M)
    (a : Series ι 𝕜) : ‖∑' i, a i • v i‖ ≤ M * ‖a‖ := by
  apply tsum_of_norm_bounded ((hasSum_norm a).mul_left M)
  intro i
  rw [norm_smul, mul_comm M]
  exact mul_le_mul_of_nonneg_left (hv i) (norm_nonneg _)

/-- Synthesis against a bounded dictionary, constructed rather than assumed. -/
def synthesis (v : ι → E) (M : ℝ) (hv : ∀ i, ‖v i‖ ≤ M) : Series ι 𝕜 →L[𝕜] E :=
  LinearMap.mkContinuous
    { toFun := fun a => ∑' i, a i • v i
      map_add' := by
        intro a b
        simp only [lp.coeFn_add, Pi.add_apply, add_smul]
        exact (summable_synthesis v M hv a).tsum_add (summable_synthesis v M hv b)
      map_smul' := by
        intro c a
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_smul]
        exact (summable_synthesis v M hv a).tsum_const_smul c }
    M (norm_synthesis v M hv)

@[simp]
theorem synthesis_apply (v : ι → E) (M : ℝ) (hv : ∀ i, ‖v i‖ ≤ M) (a : Series ι 𝕜) :
    synthesis v M hv a = ∑' i, a i • v i := rfl

theorem synthesis_hasSum (v : ι → E) (M : ℝ) (hv : ∀ i, ‖v i‖ ≤ M) (a : Series ι 𝕜) :
    HasSum (fun i => a i • v i) (synthesis v M hv a) :=
  (summable_synthesis v M hv a).hasSum

variable [DecidableEq ι] [DecidableEq κ]

theorem synthesis_single (v : ι → E) (M : ℝ) (hv : ∀ i, ‖v i‖ ≤ M) (i : ι) (c : 𝕜) :
    synthesis v M hv (lp.single 1 i c) = c • v i := by
  classical
  rw [synthesis_apply, tsum_eq_single i]
  · rw [lp.single_apply_self]
  · intro j hj
    rw [lp.single_apply_ne _ _ _ hj, zero_smul]

variable [CompleteSpace 𝕜]

/-- Push forward a Fourier sequence through an arbitrary frequency map.
No injectivity or independence assumption is imposed on this map. -/
def regroup (f : ι → κ) : Series ι 𝕜 →L[𝕜] Series κ 𝕜 :=
  synthesis (fun i => (lp.single 1 (f i) (1 : 𝕜) : Series κ 𝕜)) 1 (by
    intro i
    rw [lp.norm_single (by norm_num), norm_one])

omit [DecidableEq ι] in
theorem regroup_bound (f : ι → κ) (a : Series ι 𝕜) : ‖regroup f a‖ ≤ ‖a‖ := by
  simpa only [one_mul] using norm_synthesis (𝕜 := 𝕜) (E := Series κ 𝕜)
    (fun i => (lp.single 1 (f i) (1 : 𝕜) : Series κ 𝕜)) 1
    (fun i => by rw [lp.norm_single (by norm_num), norm_one]) a

theorem regroup_single (f : ι → κ) (i : ι) (c : 𝕜) :
    regroup f (lp.single 1 i c) = lp.single 1 (f i) c := by
  rw [regroup, synthesis_single, ← lp.single_smul]
  simp

omit [DecidableEq ι] in
/-- Applying a character dictionary after regrouping agrees with evaluating
each original character before regrouping. -/
theorem synthesis_regroup (f : ι → κ) (v : κ → E) (M : ℝ) (hv : ∀ k, ‖v k‖ ≤ M)
    (a : Series ι 𝕜) :
    synthesis v M hv (regroup f a) = synthesis (fun i => v (f i)) M (fun i => hv (f i)) a := by
  change synthesis v M hv (∑' i, a i • (lp.single 1 (f i) (1 : 𝕜) : Series κ 𝕜)) = _
  rw [(synthesis v M hv).map_tsum (summable_synthesis _ 1 (by
    intro i; rw [lp.norm_single (by norm_num), norm_one]) a)]
  simp only [map_smul]
  simp_rw [synthesis_single, one_smul]
  rfl

end Wiener
end CausalLowerbound
