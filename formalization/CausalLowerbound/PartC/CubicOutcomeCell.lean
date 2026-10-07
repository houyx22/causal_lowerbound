import CausalLowerbound.PartC.CubicAssignedPolynomial
import CausalLowerbound.PartC.CubicTaylorEvaluation

/-! Apply the cubic target to the full multi-block Taylor polynomial at
one observation. The assigned normalization annihilates every mixed
block term, after which the actual fourth-moment bridge applies. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial Representative RoughOutcome
variable {K Ω : Type*} [Fintype K] [DecidableEq K] [Fintype Ω]

theorem outcomeTaylorCoefficient_scaled (R T shift jb η smooth rough : ℝ) (f : Fin 4) :
    outcomeTaylorCoefficient R T 1 jb η smooth rough f * shift ^ f.val =
      outcomeTaylorCoefficient R T shift jb η smooth rough f := by
  fin_cases f <;> simp [outcomeTaylorCoefficient, incrementOne, incrementTwo, incrementThree]
  <;> ring

theorem assigned_outcome_taylor_functional
    (R T jb η v smooth rough : ℝ) (shift scale : K → ℝ) (owner : K)
    (hscale : ∀ k, k ≠ owner → scale k = 0) (e : K → Fin 4) :
    cubicSiteFunctional (fun f => ∏ k,
      if f k = 0 then (scale k * rough) ^ (e k).val else
        outcomeMoment (scale k ^ 2 * v) (e k) * (scale k * rough) ^ (f k).val)
      (outcomeTaylorPolynomial R T 1 jb η smooth rough (∑ k, C (shift k) * X k)) =
      (∏ k ∈ Finset.univ.erase owner, (scale k * rough) ^ (e k).val) *
        ((scale owner * rough) ^ (e owner).val * likelihood R T jb η smooth rough +
          normalizedIncrement (e owner) (scale owner) v R T (shift owner) jb η smooth rough) := by
  let w := fun k (f : Fin 4) => if f = 0 then (scale k * rough) ^ (e k).val else
    outcomeMoment (scale k ^ 2 * v) (e k) * (scale k * rough) ^ f.val
  have hw : ∀ k, k ≠ owner → ∀ f : Fin 4, f ≠ 0 → w k f = 0 := by
    intro k hk f hf
    have hfn : f.val ≠ 0 := fun he => hf (Fin.ext he)
    simp only [w, if_neg hf, hscale k hk, zero_mul, zero_pow hfn, mul_zero]
  change cubicSiteFunctional (fun f => ∏ k, w k (f k)) _ = _
  rw [outcomeTaylorPolynomial_eq_sum, cubicSiteFunctional_assigned_polynomial w shift owner hw]
  simp only [outcomeTaylorCoefficient_scaled, w, if_true]
  rw [outcomeTaylorCoefficient_slot_sum]

theorem assigned_outcome_cell_matching (μ : FiniteLaw Ω) (rough : Ω → ℝ)
    (R T jb η v smooth : ℝ) (shift scale : K → ℝ) (owner : K)
    (hscale : ∀ k, k ≠ owner → scale k = 0) (e : K → Fin 4)
    (hmean : μ.expect rough = 0) (hvar : μ.expect (fun ω => rough ω ^ 2) = v)
    (hthird : μ.expect (fun ω => rough ω ^ 3) = 0)
    (hcorrection : ((shift owner * scale owner) * jb * v) * η =
      (shift owner * scale owner) ^ 3 * jb * μ.expect (fun ω => rough ω ^ 4)) :
    μ.expect (fun ω => cubicSiteFunctional (fun f => ∏ k,
      if f k = 0 then (scale k * rough ω) ^ (e k).val else
        outcomeMoment (scale k ^ 2 * v) (e k) * (scale k * rough ω) ^ (f k).val)
      (outcomeTaylorPolynomial R T 1 jb η smooth (rough ω) (∑ k, C (shift k) * X k))) =
    μ.expect (fun ω => (∏ k, (scale k * rough ω) ^ (e k).val) *
      (likelihood R T jb η smooth (rough ω) +
        realField R T smooth ((shift owner * scale owner) * jb * v))) := by
  let b := ∏ k ∈ Finset.univ.erase owner, (0 : ℝ) ^ (e k).val
  have hoff (x : ℝ) : (∏ k ∈ Finset.univ.erase owner, (scale k * x) ^ (e k).val) = b := by
    apply Finset.prod_congr rfl
    intro k hk
    rw [hscale k (Finset.mem_erase.mp hk).1, zero_mul]
  have hp (x : ℝ) : (∏ k, (scale k * x) ^ (e k).val) = b * (scale owner * x) ^ (e owner).val := by
    rw [← Finset.mul_prod_erase Finset.univ (fun k => (scale k * x) ^ (e k).val)
      (Finset.mem_univ owner), hoff, mul_comm]
  simp_rw [assigned_outcome_taylor_functional R T jb η v smooth _ shift scale owner hscale e,
    hoff, hp, mul_assoc]
  rw [μ.expect_mul, μ.expect_mul]
  simpa only [normalizedIncrement, mul_assoc] using congrArg (fun a : ℝ => b * a)
    (normalized_cell_bridge μ rough R T (shift owner) jb η smooth v (scale owner)
      hmean hvar hthird hcorrection (e owner))

end CausalLowerbound.PartC
