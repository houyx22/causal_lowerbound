import CausalLowerbound.PartB.CubicBridge
import Mathlib.Tactic.NormNum

/-!
# Independent Rademacher sums

We construct a genuine finite product probability law and prove its first four
weighted-sum moments. The final theorem instantiates the cubic bridge for any
finite collection of block weights satisfying the quadratic partition identity.
-/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.PartB

open FiniteLaw

def rademacher : FiniteLaw Bool where
  weight _ := 1 / 2
  nonneg _ := by norm_num
  total := by norm_num [Fintype.sum_bool]

def sign : Bool → ℝ
  | true => 1
  | false => -1

theorem rademacher_expect (f : Bool → ℝ) :
    rademacher.expect f = (f true + f false) / 2 := by
  simp only [FiniteLaw.expect, rademacher, Fintype.sum_bool]
  ring

/-- A recursively presented sample space of n independent binary signs. -/
def Signs : ℕ → Type
  | 0 => Unit
  | n + 1 => Bool × Signs n

instance signsFintype (n : ℕ) : Fintype (Signs n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Bool × Signs n))

def signLaw : (n : ℕ) → FiniteLaw (Signs n)
  | 0 => { weight := fun _ => 1, nonneg := fun _ => zero_le_one, total := by simp [Signs] }
  | n + 1 => rademacher.prod (signLaw n)

theorem expect_head (n : ℕ) (f : Signs (n + 1) → ℝ) :
    (signLaw (n + 1)).expect f =
      ((signLaw n).expect (fun ω => f (true, ω)) +
        (signLaw n).expect (fun ω => f (false, ω))) / 2 := by
  change (rademacher.prod (signLaw n)).expect f = _
  rw [FiniteLaw.expect_prod, rademacher_expect]

def signSum : (w : List ℝ) → Signs w.length → ℝ
  | [], _ => 0
  | a :: w, ω => a * sign ω.1 + signSum w ω.2

@[simp] theorem signSum_cons (a : ℝ) (w : List ℝ) (ω : Signs (a :: w).length) :
    signSum (a :: w) ω = a * sign ω.1 + signSum w ω.2 := rfl

def sumSq (w : List ℝ) : ℝ := (w.map (fun a => a ^ 2)).sum
def sumFourth (w : List ℝ) : ℝ := (w.map (fun a => a ^ 4)).sum

@[simp] theorem sumSq_cons (a : ℝ) (w : List ℝ) :
    sumSq (a :: w) = a ^ 2 + sumSq w := rfl

@[simp] theorem sumFourth_cons (a : ℝ) (w : List ℝ) :
    sumFourth (a :: w) = a ^ 4 + sumFourth w := rfl

/-- First through fourth moments, including the non-Gaussian fourth-moment
correction. No independence or moment identity is assumed: the law is a product. -/
theorem signSum_moments (w : List ℝ) :
    (signLaw w.length).expect (signSum w) = 0 ∧
    (signLaw w.length).expect (fun ω => signSum w ω ^ 2) = sumSq w ∧
    (signLaw w.length).expect (fun ω => signSum w ω ^ 3) = 0 ∧
    (signLaw w.length).expect (fun ω => signSum w ω ^ 4) =
      3 * sumSq w ^ 2 - 2 * sumFourth w := by
  induction w with
  | nil => simp [signSum, sumSq, sumFourth]
  | cons a w ih =>
    rcases ih with ⟨hmean, hvar, hthird, hfourth⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · erw [expect_head w.length]
      simp only [signSum_cons, sign, mul_one, mul_neg_one]
      change ((signLaw w.length).expect (fun ω => a + signSum w ω) +
        (signLaw w.length).expect (fun ω => -a + signSum w ω)) / 2 = 0
      rw [expect_shift _ _ a hmean, expect_shift _ _ (-a) hmean]
      ring
    · erw [expect_head w.length]
      simp only [signSum_cons, sign, mul_one, mul_neg_one]
      change ((signLaw w.length).expect (fun ω => (a + signSum w ω) ^ 2) +
        (signLaw w.length).expect (fun ω => (-a + signSum w ω) ^ 2)) / 2 = sumSq (a :: w)
      rw [expect_shift_sq _ _ a hmean, expect_shift_sq _ _ (-a) hmean, hvar, sumSq_cons]
      ring
    · erw [expect_head w.length]
      simp only [signSum_cons, sign, mul_one, mul_neg_one]
      change ((signLaw w.length).expect (fun ω => (a + signSum w ω) ^ 3) +
        (signLaw w.length).expect (fun ω => (-a + signSum w ω) ^ 3)) / 2 = 0
      rw [expect_shift_cube _ _ a hmean hthird, expect_shift_cube _ _ (-a) hmean hthird]
      ring
    · erw [expect_head w.length]
      simp only [signSum_cons, sign, mul_one, mul_neg_one]
      change ((signLaw w.length).expect (fun ω => (a + signSum w ω) ^ 4) +
        (signLaw w.length).expect (fun ω => (-a + signSum w ω) ^ 4)) / 2 =
          3 * sumSq (a :: w) ^ 2 - 2 * sumFourth (a :: w)
      rw [expect_shift_fourth _ _ a hmean hthird, expect_shift_fourth _ _ (-a) hmean hthird,
        hvar, hfourth, sumSq_cons, sumFourth_cons]
      ring

theorem expect_scaled_pow {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (f : Ω → ℝ) (j : ℝ) (k : ℕ) :
    μ.expect (fun ω => (j * f ω) ^ k) = j ^ k * μ.expect (fun ω => f ω ^ k) := by
  simp only [mul_pow, μ.expect_mul]

/-- The moments in `B:eq:variance` and `B:eq:fourth-moment`, for normalized
packet weights. The paper's scalar j is a * t * G_h(x). -/
theorem normalized_sign_moments (w : List ℝ) (hw : sumSq w = 1) (j : ℝ) :
    (signLaw w.length).expect (fun ω => j * signSum w ω) = 0 ∧
    (signLaw w.length).expect (fun ω => (j * signSum w ω) ^ 2) = j ^ 2 ∧
    (signLaw w.length).expect (fun ω => (j * signSum w ω) ^ 3) = 0 ∧
    (signLaw w.length).expect (fun ω => (j * signSum w ω) ^ 4) =
      j ^ 4 * (3 - 2 * sumFourth w) := by
  rcases signSum_moments w with ⟨hmean, hvar, hthird, hfourth⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [FiniteLaw.expect_mul, hmean, mul_zero]
  · rw [expect_scaled_pow, hvar, hw, mul_one]
  · rw [expect_scaled_pow, hthird, mul_zero]
  · rw [expect_scaled_pow, hfourth, hw]
    ring

/-- The complete aggregate cubic bridge, now with all jitter moments derived
from an explicit independent-sign law. Includes j = 0 without a special case.

Use c = b/a, j = a*t*G_h(x), and w_k = φ(u_k(x)). The only geometric hypothesis
is the quadratic partition identity `sumSq w = 1`.
-/
theorem aggregate_likelihood_bridge (w : List ℝ) (hw : sumSq w = 1)
    (p c j R T : ℝ) :
    (signLaw w.length).expect (fun ω =>
      codedLikelihood R T (p + j * signSum w ω)
        (cubic c (j ^ 2 / 3 * (3 - 2 * sumFourth w)) (p + j * signSum w ω)) 0) =
      codedLikelihood R T p
        (cubic c (j ^ 2 / 3 * (3 - 2 * sumFourth w)) p - (c * j ^ 2) * (1 + 2 * p))
        (c * j ^ 2) := by
  rcases normalized_sign_moments w hw j with ⟨hmean, hvar, hthird, hfourth⟩
  have hcorrection :
      3 * (j ^ 2 / 3 * (3 - 2 * sumFourth w)) *
          (signLaw w.length).expect (fun ω => (j * signSum w ω) ^ 2) =
        (signLaw w.length).expect (fun ω => (j * signSum w ω) ^ 4) := by
    rw [hvar, hfourth]
    ring
  have h := single_site_likelihood_bridge (signLaw w.length) (fun ω => j * signSum w ω)
    p c (j ^ 2 / 3 * (3 - 2 * sumFourth w)) hmean hthird hcorrection R T
  simpa only [hvar] using h

end CausalLowerbound.PartB
