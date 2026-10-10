import CausalLowerbound.UpperBound.StencilTemplate

/-! One inward reflection works uniformly for every target in the closed
cube.  In particular the geometry does not exclude boundary targets. -/

noncomputable section
set_option autoImplicit false
open scoped Classical

namespace CausalLowerbound.UpperBound

def inwardSign (x : ℝ) : ℝ := if x ≤ 1 / 2 then 1 else -1

theorem inwardSign_abs (x : ℝ) : |inwardSign x| = 1 := by
  unfold inwardSign
  split_ifs <;> norm_num

theorem inwardSign_mul_self (x : ℝ) : inwardSign x * inwardSign x = 1 := by
  unfold inwardSign
  split_ifs <;> norm_num

theorem inward_scalar_in_unit_interval {x u : ℝ}
    (hx : 0 ≤ x ∧ x ≤ 1) (hu : 0 ≤ u ∧ u ≤ 1 / 2) :
    0 ≤ x + inwardSign x * u ∧ x + inwardSign x * u ≤ 1 := by
  unfold inwardSign
  split_ifs with hs <;> constructor <;> nlinarith

theorem inward_scalar_distance (x : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    |(x + inwardSign x * u) - x| = u := by
  rw [add_sub_cancel_left, abs_mul, inwardSign_abs, one_mul, abs_of_nonneg hu]

variable {d : Type*} [Fintype d]

def inwardReflection (x u : d → ℝ) : d → ℝ := fun i => inwardSign (x i) * u i

def inwardDisplace (x u : d → ℝ) : d → ℝ := x + inwardReflection x u

omit [Fintype d] in
theorem inwardReflection_involutive (x : d → ℝ) : Function.Involutive (inwardReflection x) := by
  intro u
  funext i
  simp only [inwardReflection, ← mul_assoc, inwardSign_mul_self, one_mul]

theorem inwardReflection_norm (x u : d → ℝ) : ‖inwardReflection x u‖ = ‖u‖ := by
  have hb (v : d → ℝ) : ‖inwardReflection x v‖ ≤ ‖v‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
    intro i
    simpa only [inwardReflection, Real.norm_eq_abs, abs_mul, inwardSign_abs, one_mul] using
      norm_le_pi_norm v i
  exact le_antisymm (hb u) (by simpa only [inwardReflection_involutive x u] using hb (inwardReflection x u))

theorem inwardDisplace_norm_bound (x u : d → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (hu : ∀ i, 0 ≤ u i ∧ u i ≤ h) : ‖inwardDisplace x u - x‖ ≤ h := by
  apply (pi_norm_le_iff_of_nonneg hh).mpr
  intro i
  change ‖(x i + inwardSign (x i) * u i) - x i‖ ≤ h
  rw [Real.norm_eq_abs, inward_scalar_distance _ (hu i).1]
  exact (hu i).2

omit [Fintype d] in
theorem inwardDisplace_in_cube (x u : d → ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1 / 2) :
    ∀ i, 0 ≤ inwardDisplace x u i ∧ inwardDisplace x u i ≤ 1 :=
  fun i => inward_scalar_in_unit_interval (hx i) (hu i)

/-- An anchor offset of at most h/4 and a further inward offset of at most
h/4 remain in the cube, even when the target is on its boundary. -/
theorem twoScale_point_geometry (x u v : d → ℝ) {h t : ℝ}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (ht : 0 ≤ t) (hth : t ≤ h / 4)
    (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1 / 4) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) :
    (∀ i, 0 ≤ inwardDisplace x (h • u + t • v) i ∧
      inwardDisplace x (h • u + t • v) i ≤ 1) ∧
      ‖inwardDisplace x (h • u + t • v) - x‖ ≤ h := by
  have hdisp : ∀ i, 0 ≤ (h • u + t • v) i ∧ (h • u + t • v) i ≤ h / 2 := by
    intro i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor
    · exact add_nonneg (mul_nonneg hh.le (hu i).1) (mul_nonneg ht (hv i).1)
    · have ha := mul_le_mul_of_nonneg_left (hu i).2 hh.le
      have hb := mul_le_mul_of_nonneg_left (hv i).2 ht
      nlinarith
  constructor
  · apply inwardDisplace_in_cube x _ hx
    intro i
    exact ⟨(hdisp i).1, (hdisp i).2.trans (by linarith)⟩
  · apply inwardDisplace_norm_bound x _ hh.le
    intro i
    exact ⟨(hdisp i).1, (hdisp i).2.trans (by linarith)⟩

omit [Fintype d] in
theorem inwardDisplace_add (x u v : d → ℝ) :
    inwardDisplace x (u + v) = inwardDisplace x u + inwardReflection x v := by
  funext i
  simp only [inwardDisplace, inwardReflection, Pi.add_apply]
  ring

omit [Fintype d] in
theorem inwardReflection_smul (x u : d → ℝ) (a : ℝ) :
    inwardReflection x (a • u) = a • inwardReflection x u := by
  funext i
  simp only [inwardReflection, Pi.smul_apply, smul_eq_mul]
  ring

end CausalLowerbound.UpperBound
