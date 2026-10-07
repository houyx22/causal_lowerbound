import CausalLowerbound.PartC.SupportedAssignment
import CausalLowerbound.PartC.PhysicalCompletedMatching
import CausalLowerbound.PartC.NormalizedRoughMoments

/-! Physical assignment parameters for the cubic bridge. Outside the
coarse envelope the supported normalization is zero; inside it the
unique assigned block has effective shift exactly a*t. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
variable {d I V G : Type*} [Fintype d] [DecidableEq d]
  [Fintype I] [Fintype V] [Fintype G]

theorem supportedAssignmentScale_zero_of_not_incident (x₀ : d → ℝ) (r h c w N : ℝ)
    (hw : 0 < w) (hw1 : w ≤ 1) (k : d → ℤ) (x : d → ℝ)
    (hx : x ∉ carrierBox x₀ r k) : supportedAssignmentScale x₀ r h c w N k x = 0 := by
  have hm : assignmentMultiplier c w (localCoordinate x₀ r k x) = 0 := by
    by_contra hn
    have hs := assignmentPartition_support w hw (assignmentMultiplier_support c w (subset_tsupport _ hn))
    apply hx
    exact ⟨fun i => (show (-2 : ℝ) ≤ -(1 + w) / 2 by linarith).trans (hs.1 i),
      fun i => (hs.2 i).trans (show (1 + w) / 2 ≤ (2 : ℝ) by linarith)⟩
  simp only [supportedAssignmentScale, hm, zero_div, ite_self]

theorem supportedAssignmentScale_outcome_variance (x₀ : d → ℝ) (r h c w N : ℝ)
    (k : d → ℤ) (x : d → ℝ) :
    supportedAssignmentScale x₀ r h c w N k x ^ 2 * coarseBump x₀ h x ^ 2 =
      (assignmentMultiplier c w (localCoordinate x₀ r k x) / N) ^ 2 * coarseBump x₀ h x ^ 2 := by
  by_cases hx : coarseBump x₀ h x = 0
  · simp only [hx, zero_pow (by decide : 2 ≠ 0), mul_zero]
  · simp only [supportedAssignmentScale, if_neg hx]

theorem normalizedRoughVariance_local (x₀ : d → ℝ) (r h : ℝ) (hr : r ≠ 0)
    (k : d → ℤ) (c w N : ℝ) (x : d → ℝ) :
    normalizedRoughVariance x₀ r h k c w N (carrierCoordinate (localCoordinate x₀ r k x)) =
      supportedAssignmentScale x₀ r h c w N k x ^ 2 * coarseBump x₀ h x ^ 2 := by
  rw [normalizedRoughVariance, carrierCoordinate_rescale,
    roughChartPoint_carrierCoordinate_local x₀ r hr k x,
    supportedAssignmentScale_outcome_variance]

theorem normalizedRoughVariance_completed_retained
    (x₀ : d → ℝ) (r h : ℝ) (hr : r ≠ 0) (k : d → ℤ) (c w N : ℝ)
    (x : I → d → ℝ) (e : {i // x i ∈ carrierBox x₀ r k} ⊕ G ≃ V)
    (ghost : G → d → ℝ) (i : {i // x i ∈ carrierBox x₀ r k}) :
    normalizedRoughVariance x₀ r h k c w N
      (configurationSite
        (completedConfiguration e (fun j => carrierCoordinate (localCoordinate x₀ r k (x j.val))) ghost)
        (e (Sum.inl i))) =
      supportedAssignmentScale x₀ r h c w N k (x i.val) ^ 2 * coarseBump x₀ h (x i.val) ^ 2 := by
  change normalizedRoughVariance x₀ r h k c w N
    (completedSites e (fun j => carrierCoordinate (localCoordinate x₀ r k (x j.val))) ghost
      (e (Sum.inl i))) = _
  rw [completedSites_retained]
  exact normalizedRoughVariance_local x₀ r h hr k c w N (x i.val)

theorem exists_supported_outcome_parameters (S : Finset (d → ℤ)) [Nonempty S]
    (x₀ : d → ℝ) (r h c w N a jb t : ℝ) (hr : 0 < r) (hw : 0 < w) (hw1 : w ≤ 1) (hN : N ≠ 0)
    (hm : ∀ z : d → ℝ, assignmentMultiplier c w z * linearPartition z = assignmentPartition w z)
    (x : I → d → ℝ)
    (hcover : ∀ i, coarseBump x₀ h (x i) ≠ 0 → ∀ k, assignmentWeight w x₀ r k (x i) ≠ 0 → k ∈ S)
    (htr : ∀ i, coarseBump x₀ h (x i) ≠ 0 → x i ∉ assignmentTransitionUnion S w x₀ r) :
    ∃ owner : I → S,
      (∀ i (k : S), k ≠ owner i → supportedAssignmentScale x₀ r h c w N k.val (x i) = 0) ∧
      (∀ i, coarseBump x₀ h (x i) = 0 ∨
        ((a * linearPartition (localCoordinate x₀ r (owner i).val (x i))) * (t * N)) *
          supportedAssignmentScale x₀ r h c w N (owner i).val (x i) = a * t) ∧
      ∀ i, (((a * linearPartition (localCoordinate x₀ r (owner i).val (x i))) * (t * N)) *
        supportedAssignmentScale x₀ r h c w N (owner i).val (x i)) * jb * coarseBump x₀ h (x i) ^ 2 =
          targetField x₀ h (a * t * jb) (x i) := by
  obtain ⟨owner, hscale, he⟩ := exists_supported_assigned_parameters S x₀ r h c w N 1 a t
    hr hw hw1 hN hm x hcover htr
  simp only [one_mul, targetField] at he
  refine ⟨owner, hscale, ?_, ?_⟩
  · intro i
    by_cases hi : coarseBump x₀ h (x i) = 0
    · exact Or.inl hi
    · exact Or.inr (mul_right_cancel₀ (pow_ne_zero 2 hi) (he i))
  · intro i
    calc
      _ = jb * ((((a * linearPartition (localCoordinate x₀ r (owner i).val (x i))) * (t * N)) *
          supportedAssignmentScale x₀ r h c w N (owner i).val (x i)) * coarseBump x₀ h (x i) ^ 2) := by ring
      _ = jb * (a * t * coarseBump x₀ h (x i) ^ 2) := by rw [he i]
      _ = _ := by rw [targetField]; ring

end CausalLowerbound.PartC
