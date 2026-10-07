import CausalLowerbound.PartC.PhysicalPropensityShift

/-! Actual parameters for the assigned-row bridge. Off the measured
transition set, the physical assignment supplies an owner, all other
normalized multipliers vanish, and the bridge effect equals the original
target field after exact cancellation of N. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
variable {d I : Type*} [Fintype d] [DecidableEq d]

theorem assignmentMultiplier_local_off_owner (c w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1)
    (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r) (x : d → ℝ) (owner k : d → ℤ)
    (howner : assignmentWeight w x₀ r owner x = 1) (hk : k ≠ owner) :
    assignmentMultiplier c w (localCoordinate x₀ r k x) = 0 := by
  have hz := assignmentMultiplier_zero_of_weight_zero c w x₀ r k x
    (assignmentWeight_one_excludes w hw hw1 x₀ r hr x owner k howner hk)
  simpa only [rescaled, packet_local_coordinate x₀ r hr.ne', localCoordinate] using hz

theorem physical_propensity_local_shift_amplitude (x₀ : d → ℝ) (r h : ℝ) (hr : r ≠ 0)
    (k : d → ℤ) (c w N ja b t : ℝ) (hN : N ≠ 0)
    (hm : ∀ y : d → ℝ, assignmentMultiplier c w y * linearPartition y = assignmentPartition w y)
    (x : d → ℝ) :
    ja * ((b * linearPartition (localCoordinate x₀ r k x)) * (t * N)) *
      (assignmentMultiplier c w (localCoordinate x₀ r k x) / N) * coarseBump x₀ h x ^ 2 =
      assignmentWeight w x₀ r k x * targetField x₀ h (ja * b * t) x := by
  have ha : assignmentWeight w x₀ r k x = assignmentPartition w (localCoordinate x₀ r k x) := by
    simp only [assignmentWeight, rescaled, packet_local_coordinate x₀ r hr k x, localCoordinate]
    rfl
  rw [ha, targetField]
  calc
    _ = (assignmentMultiplier c w (localCoordinate x₀ r k x) * linearPartition (localCoordinate x₀ r k x)) *
        ((ja * b * t) * coarseBump x₀ h x ^ 2) := by
      field_simp
      <;> ring
    _ = _ := by rw [hm]

theorem exists_physical_assigned_parameters (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (r h c w N ja b t : ℝ) (hr : 0 < r) (hw : 0 < w) (hw1 : w ≤ 1) (hN : N ≠ 0)
    (hm : ∀ y : d → ℝ, assignmentMultiplier c w y * linearPartition y = assignmentPartition w y)
    (x : I → d → ℝ)
    (hcover : ∀ i k, assignmentWeight w x₀ r k (x i) ≠ 0 → k ∈ S)
    (htr : ∀ i, x i ∉ assignmentTransitionUnion S w x₀ r) :
    ∃ owner : I → S,
      (∀ i, assignmentWeight w x₀ r (owner i).val (x i) = 1) ∧
      (∀ i (k : S), k ≠ owner i → assignmentMultiplier c w (localCoordinate x₀ r k.val (x i)) / N = 0) ∧
      ∀ i, ja * ((b * linearPartition (localCoordinate x₀ r (owner i).val (x i))) * (t * N)) *
        (assignmentMultiplier c w (localCoordinate x₀ r (owner i).val (x i)) / N) *
          coarseBump x₀ h (x i) ^ 2 = targetField x₀ h (ja * b * t) (x i) := by
  have hex (i : I) : ∃ k : S, assignmentWeight w x₀ r k.val (x i) = 1 := by
    obtain ⟨k, hk, _⟩ := assignment_exists_unique S w hw hw1 x₀ r hr (x i) (hcover i) (htr i)
    exact ⟨⟨k, hk.1⟩, hk.2⟩
  choose owner howner using hex
  refine ⟨owner, howner, ?_, ?_⟩
  · intro i k hk
    rw [assignmentMultiplier_local_off_owner c w hw hw1 x₀ r hr (x i) (owner i).val k.val
      (howner i) (fun he => hk (Subtype.ext he)), zero_div]
  · intro i
    rw [physical_propensity_local_shift_amplitude x₀ r h hr.ne' (owner i).val c w N ja b t hN hm,
      howner i, one_mul]

end CausalLowerbound.PartC
