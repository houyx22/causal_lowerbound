import CausalLowerbound.PartB.SignMonomials
import CausalLowerbound.FiniteReindex
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! Exact moments of a weighted sign sum indexed by an arbitrary finite
type, matching the actual block index set of the physical model. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
namespace CausalLowerbound.PartB
variable {K : Type*} [Fintype K] [DecidableEq K]

def independentSignSum (w : K → ℝ) (ζ : K → Bool) : ℝ := ∑ k, w k * sign (ζ k)

theorem independentSigns_fin_succ (n : ℕ) (f : (Fin (n + 1) → Bool) → ℝ) :
    (independentSigns (ι := Fin (n + 1))).expect f =
      ((independentSigns (ι := Fin n)).expect (fun ζ => f (Fin.cons true ζ)) +
        (independentSigns (ι := Fin n)).expect (fun ζ => f (Fin.cons false ζ))) / 2 := by
  simp only [independentSigns, FiniteLaw.expect, FiniteLaw.independent, rademacher]
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.prod_univ_succ,
    Fin.consEquiv_apply, ← Finset.mul_sum]
  ring
  rfl

theorem fin_signSum_moments (n : ℕ) (w : Fin n → ℝ) :
    independentSigns.expect (independentSignSum w) = 0 ∧
    independentSigns.expect (fun ζ => independentSignSum w ζ ^ 2) = ∑ k, w k ^ 2 ∧
    independentSigns.expect (fun ζ => independentSignSum w ζ ^ 3) = 0 ∧
    independentSigns.expect (fun ζ => independentSignSum w ζ ^ 4) =
      3 * (∑ k, w k ^ 2) ^ 2 - 2 * ∑ k, w k ^ 4 := by
  induction n with
  | zero => unfold independentSignSum; simp
  | succ n ih =>
    obtain ⟨hmean, hvar, hthird, hfourth⟩ := ih (fun k => w k.succ)
    have ht (ζ : Fin n → Bool) : independentSignSum w (Fin.cons true ζ) =
        w 0 + independentSignSum (fun k => w k.succ) ζ := by
      simp [independentSignSum, Fin.sum_univ_succ, sign]
    have hf (ζ : Fin n → Bool) : independentSignSum w (Fin.cons false ζ) =
        -w 0 + independentSignSum (fun k => w k.succ) ζ := by
      simp [independentSignSum, Fin.sum_univ_succ, sign]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [independentSigns_fin_succ]
      simp only [ht, hf]
      rw [expect_shift _ _ _ hmean, expect_shift _ _ _ hmean]
      ring
    · rw [independentSigns_fin_succ]
      simp only [ht, hf]
      rw [expect_shift_sq _ _ _ hmean, expect_shift_sq _ _ _ hmean, hvar, Fin.sum_univ_succ]
      ring
    · rw [independentSigns_fin_succ]
      simp only [ht, hf]
      rw [expect_shift_cube _ _ _ hmean hthird, expect_shift_cube _ _ _ hmean hthird]
      ring
    · rw [independentSigns_fin_succ]
      simp only [ht, hf]
      rw [expect_shift_fourth _ _ _ hmean hthird, expect_shift_fourth _ _ _ hmean hthird, hvar, hfourth]
      simp only [Fin.sum_univ_succ]
      ring

theorem independentSignSum_moments (w : K → ℝ) :
    independentSigns.expect (independentSignSum w) = 0 ∧
    independentSigns.expect (fun ζ => independentSignSum w ζ ^ 2) = ∑ k, w k ^ 2 ∧
    independentSigns.expect (fun ζ => independentSignSum w ζ ^ 3) = 0 ∧
    independentSigns.expect (fun ζ => independentSignSum w ζ ^ 4) =
      3 * (∑ k, w k ^ 2) ^ 2 - 2 * ∑ k, w k ^ 4 := by
  let e : Fin (Fintype.card K) ≃ K := (Fintype.equivFin K).symm
  have hf (ζ : Fin (Fintype.card K) → Bool) :
      independentSignSum w (fun k => ζ (e.symm k)) = independentSignSum (fun i => w (e i)) ζ := by
    unfold independentSignSum
    rw [← e.sum_comp]
    simp
  have h := fin_signSum_moments (Fintype.card K) (fun i => w (e i))
  simp only [independentSigns] at h ⊢
  simp_rw [FiniteLaw.expect_independent_equiv e (fun _ => rademacher), hf]
  simpa only [e.sum_comp (fun k => w k ^ 2), e.sum_comp (fun k => w k ^ 4)] using h

end CausalLowerbound.PartB
