import CausalLowerbound.PartC.PhysicalAssignedParameters
import CausalLowerbound.PartC.PhysicalLocalSigns

/-! Assignment is needed only where the coarse envelope is nonzero.
Masking the multiplier elsewhere changes neither the retained rough
variable, its correction, nor the target amplitude. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
variable {d I : Type*} [Fintype d] [DecidableEq d]

def supportedAssignmentScale (x₀ : d → ℝ) (r h c w N : ℝ) (k : d → ℤ) (x : d → ℝ) : ℝ :=
  if coarseBump x₀ h x = 0 then 0 else assignmentMultiplier c w (localCoordinate x₀ r k x) / N

theorem supportedAssignmentScale_rough (x₀ : d → ℝ) (ℓ r h c w N : ℝ)
    (k : d → ℤ) (ζ : activeBlocks (d := d) ℓ h → Bool) (x : d → ℝ) :
    supportedAssignmentScale x₀ r h c w N k x * physicalRoughField x₀ ℓ h ζ x =
      (assignmentMultiplier c w (localCoordinate x₀ r k x) / N) * physicalRoughField x₀ ℓ h ζ x := by
  by_cases hx : coarseBump x₀ h x = 0
  · simp only [supportedAssignmentScale, if_pos hx, physicalRoughField_zero x₀ ℓ h ζ x hx,
      zero_mul, mul_zero]
  · simp only [supportedAssignmentScale, if_neg hx]

theorem supportedAssignmentScale_variance (x₀ : d → ℝ) (r h c w N ja : ℝ)
    (k : d → ℤ) (x : d → ℝ) :
    supportedAssignmentScale x₀ r h c w N k x ^ 2 * ja ^ 2 * (coarseBump x₀ h x ^ 2) ^ 2 =
      (assignmentMultiplier c w (localCoordinate x₀ r k x) / N) ^ 2 * ja ^ 2 *
        (coarseBump x₀ h x ^ 2) ^ 2 := by
  by_cases hx : coarseBump x₀ h x = 0
  · simp only [hx, zero_pow (by decide : 2 ≠ 0), mul_zero]
  · simp only [supportedAssignmentScale, if_neg hx]

theorem supportedAssignmentScale_amplitude (x₀ : d → ℝ) (r h c w N ja b t : ℝ)
    (hr : r ≠ 0) (hN : N ≠ 0)
    (hm : ∀ z : d → ℝ, assignmentMultiplier c w z * linearPartition z = assignmentPartition w z)
    (k : d → ℤ) (x : d → ℝ) :
    ja * ((b * linearPartition (localCoordinate x₀ r k x)) * (t * N)) *
      supportedAssignmentScale x₀ r h c w N k x * coarseBump x₀ h x ^ 2 =
        assignmentWeight w x₀ r k x * targetField x₀ h (ja * b * t) x := by
  by_cases hx : coarseBump x₀ h x = 0
  · simp only [targetField, hx, zero_pow (by decide : 2 ≠ 0), mul_zero]
  · rw [supportedAssignmentScale, if_neg hx]
    exact physical_propensity_local_shift_amplitude x₀ r h hr k c w N ja b t hN hm x

theorem exists_supported_assigned_parameters (S : Finset (d → ℤ)) [Nonempty S]
    (x₀ : d → ℝ) (r h c w N ja b t : ℝ) (hr : 0 < r) (hw : 0 < w) (hw1 : w ≤ 1) (hN : N ≠ 0)
    (hm : ∀ z : d → ℝ, assignmentMultiplier c w z * linearPartition z = assignmentPartition w z)
    (x : I → d → ℝ)
    (hcover : ∀ i, coarseBump x₀ h (x i) ≠ 0 → ∀ k, assignmentWeight w x₀ r k (x i) ≠ 0 → k ∈ S)
    (htr : ∀ i, coarseBump x₀ h (x i) ≠ 0 → x i ∉ assignmentTransitionUnion S w x₀ r) :
    ∃ owner : I → S,
      (∀ i (k : S), k ≠ owner i → supportedAssignmentScale x₀ r h c w N k.val (x i) = 0) ∧
      ∀ i, ja * ((b * linearPartition (localCoordinate x₀ r (owner i).val (x i))) * (t * N)) *
        supportedAssignmentScale x₀ r h c w N (owner i).val (x i) *
          coarseBump x₀ h (x i) ^ 2 = targetField x₀ h (ja * b * t) (x i) := by
  have hex (i : I) : ∃ k : S, coarseBump x₀ h (x i) ≠ 0 → assignmentWeight w x₀ r k.val (x i) = 1 := by
    by_cases hi : coarseBump x₀ h (x i) = 0
    · exact ⟨Classical.choice inferInstance, fun hn => (hn hi).elim⟩
    · obtain ⟨k, hk, _⟩ := assignment_exists_unique S w hw hw1 x₀ r hr (x i) (hcover i hi) (htr i hi)
      exact ⟨⟨k, hk.1⟩, fun _ => hk.2⟩
  choose owner howner using hex
  refine ⟨owner, ?_, ?_⟩
  · intro i k hk
    by_cases hi : coarseBump x₀ h (x i) = 0
    · simp only [supportedAssignmentScale, if_pos hi]
    · rw [supportedAssignmentScale, if_neg hi,
        assignmentMultiplier_local_off_owner c w hw hw1 x₀ r hr (x i) (owner i).val k.val
          (howner i hi) (fun he => hk (Subtype.ext he)), zero_div]
  · intro i
    rw [supportedAssignmentScale_amplitude x₀ r h c w N ja b t hr.ne' hN hm]
    by_cases hi : coarseBump x₀ h (x i) = 0
    · simp only [targetField, hi, zero_pow (by decide : 2 ≠ 0), mul_zero]
    · rw [howner i hi, one_mul]

end CausalLowerbound.PartC
