import CausalLowerbound.WienerPeriodization

/-! Descent of actual lattice periodization to continuous torus functions,
with an exact formula for every choice of real representatives. -/

noncomputable section
set_option autoImplicit false
open scoped Topology

namespace CausalLowerbound.Wiener

variable {α : Type*} [Fintype α]

def torusProjection (x : α → ℝ) : Torus α := fun i => (x i : UnitAddCircle)

theorem torusProjection_quotient : IsOpenQuotientMap (torusProjection (α := α)) :=
  IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)

def torusRepresentative (x : Torus α) : α → ℝ :=
  Classical.choose (torusProjection_quotient.surjective x)

@[simp] theorem torusProjection_representative (x : Torus α) :
    torusProjection (torusRepresentative x) = x :=
  Classical.choose_spec (torusProjection_quotient.surjective x)

theorem torusProjection_eq_integer_shift (x y : α → ℝ) (h : torusProjection x = torusProjection y) :
    ∃ k : α → ℤ, x = fun i => y i + (k i : ℝ) := by
  have hi (i : α) : ∃ n : ℤ, x i = y i + (n : ℝ) := by
    have hxy : (x i : UnitAddCircle) = (y i : UnitAddCircle) := congrFun h i
    have hz : ((x i - y i : ℝ) : UnitAddCircle) = 0 := by
      rw [QuotientAddGroup.mk_sub, hxy, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff 1).mp hz
    refine ⟨n, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hn
    linarith
  choose k hk using hi
  exact ⟨k, funext hk⟩

def periodizedTorus (f : (α → ℝ) → ℂ) (N : α → ℕ) (x : Torus α) : ℂ :=
  periodize f N (fun i => (N i : ℝ) * torusRepresentative x i)

theorem periodizedTorus_coe (f : (α → ℝ) → ℂ) (N : α → ℕ) (x : α → ℝ) :
    periodizedTorus f N (torusProjection x) = periodize f N (fun i => (N i : ℝ) * x i) := by
  obtain ⟨k, hk⟩ := torusProjection_eq_integer_shift (torusRepresentative (torusProjection x)) x
    (torusProjection_representative _)
  unfold periodizedTorus
  have he : (fun i => (N i : ℝ) * torusRepresentative (torusProjection x) i) =
      latticeTranslate N k (fun i => (N i : ℝ) * x i) := by
    funext i
    rw [hk]
    simp only [latticeTranslate]
    ring
  rw [he, periodize_lattice_invariant]

theorem periodizedTorus_continuous (f : (α → ℝ) → ℂ) (hf : HasCompactSupport f)
    (hc : Continuous f) (N : α → ℕ) (hN : ∀ i, N i ≠ 0) : Continuous (periodizedTorus f N) := by
  apply torusProjection_quotient.continuous_comp_iff.mp
  have he : periodizedTorus f N ∘ torusProjection =
      (fun x : α → ℝ => periodize f N (fun i => (N i : ℝ) * x i)) :=
    funext (periodizedTorus_coe f N)
  rw [he]
  exact (periodize_continuous f hf hc N hN).comp
    (continuous_pi (fun i => continuous_const.mul (continuous_apply i)))

def periodizedContinuous (f : (α → ℝ) → ℂ) (hf : HasCompactSupport f)
    (hc : Continuous f) (N : α → ℕ) (hN : ∀ i, N i ≠ 0) : C(Torus α, ℂ) :=
  ⟨periodizedTorus f N, periodizedTorus_continuous f hf hc N hN⟩

end CausalLowerbound.Wiener
