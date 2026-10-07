import CausalLowerbound.PartB.BinaryExperiment

/-! Discharge the partial-jitter moment bounds for an actual subset of block weights. -/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.PartB

theorem sumSq_nonneg (w : List ℝ) : 0 ≤ sumSq w := by
  induction w with
  | nil => exact le_refl 0
  | cons a w ih => rw [sumSq_cons]; exact add_nonneg (sq_nonneg a) ih

theorem sumFourth_nonneg (w : List ℝ) : 0 ≤ sumFourth w := by
  induction w with
  | nil => exact le_refl 0
  | cons a w ih => rw [sumFourth_cons]; exact add_nonneg (by positivity) ih

theorem sumFourth_le_sumSq_sq (w : List ℝ) : sumFourth w ≤ sumSq w ^ 2 := by
  induction w with
  | nil => simp [sumFourth, sumSq]
  | cons a w ih =>
    rw [sumFourth_cons, sumSq_cons]
    nlinarith [mul_nonneg (sq_nonneg a) (sumSq_nonneg w)]

theorem sumSq_sublist {u w : List ℝ} (h : u.Sublist w) : sumSq u ≤ sumSq w := by
  induction h with
  | slnil => exact le_refl 0
  | cons a h ih => rw [sumSq_cons]; exact ih.trans (le_add_of_nonneg_left (sq_nonneg a))
  | cons₂ a h ih => simpa only [sumSq_cons] using add_le_add_left ih (a ^ 2)

theorem scaled_sign_fourth_bound (w : List ℝ) (j : ℝ) :
    (signLaw w.length).expect (fun ω => (j * signSum w ω) ^ 4) ≤
      3 * (j ^ 2 * sumSq w) ^ 2 := by
  have hfourth := (signSum_moments w).2.2.2
  calc
    _ = 3 * (j ^ 2 * sumSq w) ^ 2 - 2 * j ^ 4 * sumFourth w := by
      rw [expect_scaled_pow, hfourth]
      ring
    _ ≤ _ := sub_le_self _ (mul_nonneg (by positivity) (sumFourth_nonneg w))

/-- A sublist represents any selection of the active blocks, including the empty one. -/
theorem partial_sign_moments (u w : List ℝ) (hsub : u.Sublist w)
    (hw : sumSq w = 1) (j : ℝ) :
    (signLaw u.length).expect (fun ω => j * signSum u ω) = 0 ∧
    (signLaw u.length).expect (fun ω => (j * signSum u ω) ^ 3) = 0 ∧
    0 ≤ (signLaw u.length).expect (fun ω => (j * signSum u ω) ^ 2) ∧
    (signLaw u.length).expect (fun ω => (j * signSum u ω) ^ 2) ≤ j ^ 2 ∧
    0 ≤ (signLaw u.length).expect (fun ω => (j * signSum u ω) ^ 4) ∧
    (signLaw u.length).expect (fun ω => (j * signSum u ω) ^ 4) ≤ 3 * (j ^ 2) ^ 2 := by
  rcases signSum_moments u with ⟨hmean, hvar, hthird, _⟩
  have hu : sumSq u ≤ 1 := by simpa only [hw] using sumSq_sublist hsub
  have hv0 : 0 ≤ j ^ 2 * sumSq u := mul_nonneg (sq_nonneg j) (sumSq_nonneg u)
  have hv : j ^ 2 * sumSq u ≤ j ^ 2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hu (sq_nonneg j)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [FiniteLaw.expect_mul, hmean, mul_zero]
  · rw [expect_scaled_pow, hthird, mul_zero]
  · exact (signLaw u.length).expect_nonneg _ (fun ω => sq_nonneg _)
  · rw [expect_scaled_pow, hvar]
    exact hv
  · exact (signLaw u.length).expect_nonneg _ (fun ω => by positivity)
  · exact (scaled_sign_fourth_bound u j).trans (by nlinarith)

/-- The paper's fourth-moment correction satisfies 0 ≤ η ≤ 1 for |j| ≤ 1. -/
theorem normalized_eta_bounds (w : List ℝ) (hw : sumSq w = 1)
    (j : ℝ) (hj : j ^ 2 ≤ 1) :
    0 ≤ j ^ 2 / 3 * (3 - 2 * sumFourth w) ∧
    j ^ 2 / 3 * (3 - 2 * sumFourth w) ≤ 1 := by
  have hq0 := sumFourth_nonneg w
  have hq1 : sumFourth w ≤ 1 := by simpa only [hw, one_pow] using sumFourth_le_sumSq_sq w
  have hprod0 := mul_nonneg (sq_nonneg j) hq0
  have hprod1 := mul_le_mul_of_nonneg_left hq1 (sq_nonneg j)
  constructor <;> nlinarith [sq_nonneg j]

/-- Partial-shift stability with every moment and correction derived from signs.
No positivity or moment bound for the partial law is left as a hypothesis. -/
theorem partial_aggregate_walsh_stability (u w : List ℝ) (hsub : u.Sublist w)
    (hw : sumSq w = 1) (p c j : ℝ) (hp : |p| ≤ 1) (hc : 0 ≤ c)
    (hj : j ^ 2 ≤ 1) (χ : WalshCharacter) :
    |(signLaw u.length).expect (fun ω =>
        walshCoefficient χ (p + j * signSum u ω)
          (cubic c (j ^ 2 / 3 * (3 - 2 * sumFourth w)) (p + j * signSum u ω)) 0) -
      walshCoefficient χ p
        (cubic c (j ^ 2 / 3 * (3 - 2 * sumFourth w)) p - (c * j ^ 2) * (1 + 2 * p))
        (c * j ^ 2)| ≤ 3 * (c * j ^ 2) := by
  rcases partial_sign_moments u w hsub hw j with ⟨hmean, hthird, hs0, hsv, hms0, hms⟩
  rcases normalized_sign_moments w hw j with ⟨_, hvar, _, hfourth⟩
  rcases partial_sign_moments w w (List.Sublist.refl w) hw j with ⟨_, _, _, _, hm0, hm⟩
  rcases normalized_eta_bounds w hw j hj with ⟨hη0, hη1⟩
  rw [expect_walsh _ _ _ _ _ hmean hthird χ]
  apply partial_walsh_stability χ p c (j ^ 2 / 3 * (3 - 2 * sumFourth w))
    (j ^ 2) _ ((signLaw w.length).expect (fun ω => (j * signSum w ω) ^ 4)) _
    hp hc hη0 hη1 (sq_nonneg j) hj hs0 hsv hm0 hm hms0 hms
  rw [hfourth]
  ring

open scoped BigOperators

/-- The finite-site version of `B:lem:partial-stability`, for actual sign laws.
Binary legality is explicit; the baseline coefficients may be arbitrarily dependent. -/
theorem joint_partial_aggregate_walsh_stability {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u w : ι → List ℝ) (hsub : ∀ i, (u i).Sublist (w i))
    (hw : ∀ i, sumSq (w i) = 1) (p c j : ι → ℝ)
    (hp : ∀ i, |p i| ≤ 1) (hc : ∀ i, 0 ≤ c i) (hj : ∀ i, j i ^ 2 ≤ 1)
    (hP : ∀ i, BinaryLegal (p i)
      (cubic (c i) (j i ^ 2 / 3 * (3 - 2 * sumFourth (w i))) (p i) -
        (c i * j i ^ 2) * (1 + 2 * p i)) (c i * j i ^ 2))
    (hQ : ∀ i ω, BinaryLegal (p i + j i * signSum (u i) ω)
      (cubic (c i) (j i ^ 2 / 3 * (3 - 2 * sumFourth (w i)))
        (p i + j i * signSum (u i) ω)) 0) (χ : ι → WalshCharacter) :
    |(FiniteLaw.independent (fun i => signLaw (u i).length)).expect (fun ω => ∏ i,
        walshCoefficient (χ i) (p i + j i * signSum (u i) (ω i))
          (cubic (c i) (j i ^ 2 / 3 * (3 - 2 * sumFourth (w i)))
            (p i + j i * signSum (u i) (ω i))) 0) -
      ∏ i, walshCoefficient (χ i) (p i)
        (cubic (c i) (j i ^ 2 / 3 * (3 - 2 * sumFourth (w i))) (p i) -
          (c i * j i ^ 2) * (1 + 2 * p i)) (c i * j i ^ 2)| ≤
      3 * ∑ i, c i * j i ^ 2 := by
  rw [Finset.mul_sum]
  apply joint_walsh_stability (fun i => signLaw (u i).length)
    (fun i ω => walshCoefficient (χ i) (p i + j i * signSum (u i) ω)
      (cubic (c i) (j i ^ 2 / 3 * (3 - 2 * sumFourth (w i)))
        (p i + j i * signSum (u i) ω)) 0)
    (fun i => walshCoefficient (χ i) (p i)
      (cubic (c i) (j i ^ 2 / 3 * (3 - 2 * sumFourth (w i))) (p i) -
        (c i * j i ^ 2) * (1 + 2 * p i)) (c i * j i ^ 2))
    (fun i => 3 * (c i * j i ^ 2))
  · intro i
    exact averaged_walsh_abs_le_one (signLaw (u i).length) _ _ _ (hQ i) (χ i)
  · intro i
    exact walshCoefficient_abs_le_one _ _ _ (hP i) (χ i)
  · intro i
    exact partial_aggregate_walsh_stability (u i) (w i) (hsub i) (hw i)
      (p i) (c i) (j i) (hp i) (hc i) (hj i) (χ i)

end CausalLowerbound.PartB
