import CausalLowerbound.PartB.MixedShellDomain
import CausalLowerbound.PartB.FineFactorEvaluation

/-! Exact evaluation of a jointly periodized graph profile on a configuration.
This works with shared vertices, cycles, and coupled (non-product) profiles. -/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.PartB.ShellGeometry

open Wiener
variable {V F d : Type*} [Fintype V] [DecidableEq V] [Fintype F] [Fintype d]

def configurationSite (u : V × d → ℝ) (v : V) : d → ℝ := fun i => u (v, i)

def realConfiguration (a b : F → V) (u : V × d → ℝ) : (V × d) ⊕ (F × d) → ℝ :=
  Sum.elim u (fun i => u (a i.1, i.2) - u (b i.1, i.2))

def centralConfiguration (a b : F → V) (m : F → ℕ) (u : V × d → ℝ) : (V × d) ⊕ (F × d) → ℝ :=
  Sum.elim u (fun i => fineLift (m i.1) (configurationSite u (a i.1)) (configurationSite u (b i.1)) i.2)

def dyadicPeriods (m : F → ℕ) : F × d → ℕ := fun i => 2 ^ m i.1

theorem configurationLift_coe (a b : F → V) (u : V × d → ℝ) :
    configurationLift a b (torusProjection u) = torusProjection (realConfiguration a b u) := by
  funext i
  cases i with
  | inl i => rfl
  | inr i => rfl

theorem graph_periodization_central (a b : F → V) (m : F → ℕ) (hm : ∀ e, 5 ≤ m e)
    (u : V × d → ℝ) (f : (F × d → ℝ) → ℂ)
    (hf : ∀ z, f z ≠ 0 → ∀ i, |z i| < 1) :
    periodize f (dyadicPeriods m) (fun i => (2 : ℝ) ^ m i.1 * (u (a i.1, i.2) - u (b i.1, i.2))) =
      f (fun i => fineLift (m i.1) (configurationSite u (a i.1)) (configurationSite u (b i.1)) i.2) := by
  let z : F × d → ℝ := fun i => fineLift (m i.1) (configurationSite u (a i.1)) (configurationSite u (b i.1)) i.2
  let k : F × d → ℤ := fun i => centralShift (configurationSite u (a i.1)) (configurationSite u (b i.1)) i.2
  have hp (e : F) : (2 : ℝ) ≤ 2 ^ m e := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 1 ≤ m e by have := hm e; omega)
  have he : (fun i => (2 : ℝ) ^ m i.1 * (u (a i.1, i.2) - u (b i.1, i.2))) =
      latticeTranslate (dyadicPeriods m) k z := by
    funext i
    simp only [latticeTranslate, dyadicPeriods, z, k, fineLift, centralDifference, centralShift,
      configurationSite, Nat.cast_pow, Nat.cast_ofNat]
    ring
  rw [he, periodize_lattice_invariant]
  apply periodize_no_extra_copies_closed
  · intro y hy i
    have hle : 1 ≤ (2 : ℝ) ^ m i.1 / 2 := by linarith [hp i.1]
    simpa only [dyadicPeriods, Nat.cast_pow, Nat.cast_ofNat] using (hf y hy i).trans_le hle
  · intro i
    simp only [z, fineLift, dyadicPeriods, Nat.cast_pow, Nat.cast_ofNat, abs_mul,
      abs_of_pos (by positivity : 0 < (2 : ℝ) ^ m i.1)]
    exact (mul_le_mul_of_nonneg_left
      (centralDifference_abs (configurationSite u (a i.1)) (configurationSite u (b i.1)) i.2)
      (by positivity : 0 ≤ (2 : ℝ) ^ m i.1)).trans_eq (by ring)

theorem mixed_graph_evaluation (a b : F → V) (m : F → ℕ) (hm : ∀ e, 5 ≤ m e)
    (H : ((V × d) ⊕ (F × d) → ℝ) → ℂ)
    (hper : ∀ k u z, H (Sum.elim (latticeTranslate (fun _ => 1) k u) z) = H (Sum.elim u z))
    (hs : ∀ x, H x ≠ 0 → ∀ e, annularCutoff (edgePoint x e) ≠ 0)
    (u : V × d → ℝ) :
    mixedPeriodizedTorus H (dyadicPeriods m) (configurationLift a b (torusProjection u)) =
      H (centralConfiguration a b m u) := by
  rw [configurationLift_coe, mixedPeriodizedTorus_coe H hper]
  simp only [realConfiguration, Sum.elim_inl, Sum.elim_inr, dyadicPeriods, Nat.cast_pow, Nat.cast_ofNat]
  apply graph_periodization_central a b m hm u
  intro z hz i
  exact (annularCutoff_support_point _ (hs (Sum.elim u z) hz i.1)).1 i.2

end CausalLowerbound.PartB.ShellGeometry
