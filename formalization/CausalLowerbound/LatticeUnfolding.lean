import CausalLowerbound.WienerPeriodization
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! Unfolding integration over the unit cell for a genuinely periodized compact
profile. The multidimensional lattice action and its fundamental domain are
constructed explicitly. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Topology

namespace CausalLowerbound.Wiener

variable {α : Type*} [Fintype α]

def unitCell : Set (α → ℝ) := Set.univ.pi (fun _ => Set.Ioc 0 1)

theorem measurableSet_unitCell : MeasurableSet (unitCell (α := α)) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ioc)

theorem unitCell_subset_cube : unitCell (α := α) ⊆ Set.Icc (0 : α → ℝ) 1 := by
  intro x hx
  exact ⟨fun i => (hx i (Set.mem_univ _)).1.le, fun i => (hx i (Set.mem_univ _)).2⟩

local instance integerLatticeAction : AddAction (α → ℤ) (α → ℝ) where
  vadd k x := fun i => (k i : ℝ) + x i
  zero_vadd x := by
    change (fun i => ((0 : ℤ) : ℝ) + x i) = x
    funext i; simp
  add_vadd k l x := by
    change (fun i => ((k i + l i : ℤ) : ℝ) + x i) =
      (fun i => (k i : ℝ) + ((l i : ℝ) + x i))
    funext i; simp [add_assoc]

local instance integerLatticeMeasurable : MeasurableVAdd (α → ℤ) (α → ℝ) where
  measurable_const_vadd _ := measurable_const.add measurable_id
  measurable_vadd_const _ := measurable_of_countable _

local instance integerLatticeInvariant :
    VAddInvariantMeasure (α → ℤ) (α → ℝ) (volume : Measure (α → ℝ)) where
  measure_preimage_vadd k _s _hs := measure_preimage_add volume (fun i => (k i : ℝ)) _

theorem unitCell_fundamental :
    IsAddFundamentalDomain (α → ℤ) (unitCell (α := α)) (volume : Measure (α → ℝ)) := by
  apply IsAddFundamentalDomain.mk' measurableSet_unitCell.nullMeasurableSet
  intro x
  refine ⟨fun i => 1 - ⌈x i⌉, ?_, ?_⟩
  · intro i _
    change 0 < ((1 - ⌈x i⌉ : ℤ) : ℝ) + x i ∧ ((1 - ⌈x i⌉ : ℤ) : ℝ) + x i ≤ 1
    push_cast
    constructor <;> linarith [Int.ceil_lt_add_one (x i), Int.le_ceil (x i)]
  · intro k hk
    funext i
    have hi := hk i (Set.mem_univ i)
    change 0 < (k i : ℝ) + x i ∧ (k i : ℝ) + x i ≤ 1 at hi
    have hc : ⌈x i + (k i : ℝ)⌉ = (1 : ℤ) :=
      Int.ceil_eq_iff.mpr ⟨by norm_num; linarith [hi.1], by norm_num; linarith [hi.2]⟩
    rw [Int.ceil_add_intCast] at hc
    omega

/-- Integration over a fundamental cell exactly unfolds the locally finite
lattice sum, without an assumed Poisson or Fourier coefficient identity. -/
theorem integral_unitCell_periodize (f : (α → ℝ) → ℂ)
    (hf : HasCompactSupport f) (hc : Continuous f) :
    (∫ x in unitCell, periodize f (fun _ => 1) x) = ∫ x, f x := by
  classical
  obtain ⟨S, hS⟩ := periodize_finite_on_compact f hf (fun _ => 1) (by simp)
    (Set.Icc (0 : α → ℝ) 1) isCompact_Icc
  have hInt (k : α → ℤ) : IntegrableOn (fun x => f (latticeTranslate (fun _ => 1) k x)) unitCell :=
    ((hc.comp (continuous_id.add continuous_const)).continuousOn.integrableOn_compact
      (isCompact_Icc : IsCompact (Set.Icc (0 : α → ℝ) 1))).mono_set unitCell_subset_cube
  calc
    _ = ∫ x in unitCell, ∑ k ∈ S, f (latticeTranslate (fun _ => 1) k x) := by
      apply setIntegral_congr_fun measurableSet_unitCell
      intro x hx
      exact periodize_eq_finite_sum f _ x S (hS x (unitCell_subset_cube hx))
    _ = ∑ k ∈ S, ∫ x in unitCell, f (latticeTranslate (fun _ => 1) k x) :=
      integral_finset_sum S (fun k _ => hInt k)
    _ = ∑' k : α → ℤ, ∫ x in unitCell, f (latticeTranslate (fun _ => 1) k x) := by
      symm
      apply tsum_eq_sum
      intro k hk
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      exact hS x (unitCell_subset_cube hx) k hk
    _ = ∫ x, f x := by
      have h := unitCell_fundamental.integral_eq_tsum'' f (hc.integrable_of_hasCompactSupport hf)
      change (∫ x, f x) = ∑' k : α → ℤ, ∫ x in unitCell, f (fun i => (k i : ℝ) + x i) at h
      rw [h]
      apply tsum_congr
      intro k
      apply setIntegral_congr_fun measurableSet_unitCell
      intro x _
      exact congrArg f (funext (fun i => by simp [latticeTranslate, add_comm]))

end CausalLowerbound.Wiener
