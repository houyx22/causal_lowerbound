import CausalLowerbound.PartB.IndependentSites
import CausalLowerbound.FiniteBounds

/-!
# Quantitative partial-jitter stability

This is the algebraic and probabilistic core of `B:lem:partial-stability`.
The uniform smallness assumptions are explicit: |p| ≤ 1, 0 ≤ η ≤ 1,
0 ≤ v ≤ 1, and c ≥ 0. The bounds below are in units of d_* = c*v.
The geometric estimate d_*(x) ≤ C*Δ is not assumed silently or proved here.
-/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.PartB

open scoped BigOperators

/-- Outcome Walsh coefficient after averaging a centered symmetric jitter. -/
def outcomeMoment (p c η v : ℝ) : ℝ := cubic c η p - c * p * v

/-- Interaction Walsh coefficient; m is the fourth jitter moment. -/
def interactionMoment (p c η v m : ℝ) : ℝ :=
  p * cubic c η p + c * (1 + η) * v - (c / 3) * (6 * p ^ 2 * v + m)

theorem outcomeMoment_stability (p c η v s : ℝ)
    (hp : |p| ≤ 1) (hc : 0 ≤ c) (hs : 0 ≤ s) (hsv : s ≤ v) :
    |outcomeMoment p c η s - outcomeMoment p c η v| ≤ c * v := by
  have hvs : 0 ≤ v - s := sub_nonneg.mpr hsv
  calc
    _ = c * |p| * (v - s) := by
      have he : outcomeMoment p c η s - outcomeMoment p c η v = c * p * (v - s) := by
        unfold outcomeMoment
        ring
      rw [he, abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg hvs]
    _ ≤ c * 1 * v := mul_le_mul (mul_le_mul_of_nonneg_left hp hc)
      (sub_le_self v hs) hvs (by simpa using hc)
    _ = c * v := by ring

theorem interactionMoment_stability (p c η v s m ms : ℝ)
    (hp : |p| ≤ 1) (hc : 0 ≤ c) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hs0 : 0 ≤ s) (hsv : s ≤ v)
    (hm0 : 0 ≤ m) (hm : m ≤ 3 * v ^ 2)
    (hms0 : 0 ≤ ms) (hms : ms ≤ 3 * v ^ 2) :
    |interactionMoment p c η s ms - interactionMoment p c η v m| ≤ 3 * (c * v) := by
  have hp2 : p ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one p).mpr hp
  have hv2 : v ^ 2 ≤ v := by nlinarith
  have hcoef : |1 + η - 2 * p ^ 2| ≤ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg p]
  have hvar : |s - v| ≤ v := by rw [abs_le]; constructor <;> linarith
  have hfourth : |ms - m| ≤ 3 * v := by rw [abs_le]; constructor <;> nlinarith
  calc
    _ = |c * (1 + η - 2 * p ^ 2) * (s - v) - (c / 3) * (ms - m)| := by
      congr 1
      unfold interactionMoment
      ring
    _ ≤ |c * (1 + η - 2 * p ^ 2) * (s - v)| + |(c / 3) * (ms - m)| :=
      abs_sub _ _
    _ = c * |1 + η - 2 * p ^ 2| * |s - v| + (c / 3) * |ms - m| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hc,
        abs_of_nonneg (div_nonneg hc (by norm_num : (0 : ℝ) ≤ 3))]
    _ ≤ (c * 2) * v + (c / 3) * (3 * v) := add_le_add
      (mul_le_mul (mul_le_mul_of_nonneg_left hcoef hc) hvar (abs_nonneg _)
        (mul_nonneg hc (by norm_num)))
      (mul_le_mul_of_nonneg_left hfourth (div_nonneg hc (by norm_num)))
    _ = 3 * (c * v) := by ring

/-- The four coefficients of the binary Walsh expansion. -/
inductive WalshCharacter
  | constant | propensity | outcome | interaction
  deriving DecidableEq

def walshCoefficient (χ : WalshCharacter) (p y τ : ℝ) : ℝ :=
  match χ with
  | .constant => 1
  | .propensity => p
  | .outcome => y + τ * (1 + p)
  | .interaction => p * y + τ * (1 + p)

def jitterWalsh (χ : WalshCharacter) (p c η v m : ℝ) : ℝ :=
  match χ with
  | .constant => 1
  | .propensity => p
  | .outcome => outcomeMoment p c η v
  | .interaction => interactionMoment p c η v m

theorem expect_walsh {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (δ : Ω → ℝ) (p c η : ℝ) (hmean : μ.expect δ = 0)
    (hthird : μ.expect (fun ω => δ ω ^ 3) = 0) (χ : WalshCharacter) :
    μ.expect (fun ω => walshCoefficient χ (p + δ ω) (cubic c η (p + δ ω)) 0) =
      jitterWalsh χ p c η (μ.expect (fun ω => δ ω ^ 2))
        (μ.expect (fun ω => δ ω ^ 4)) := by
  cases χ with
  | constant => exact μ.expect_const 1
  | propensity => exact expect_shift μ δ p hmean
  | outcome =>
    simpa only [walshCoefficient, jitterWalsh, outcomeMoment, zero_mul, add_zero]
      using expect_cubic μ δ p c η hmean hthird
  | interaction =>
    simpa only [walshCoefficient, jitterWalsh, interactionMoment, zero_mul, add_zero]
      using expect_mul_cubic μ δ p c η hmean hthird

/-- All four full-jitter coefficients equal the actual P-side coefficients. -/
theorem full_jitter_walsh (χ : WalshCharacter) (p c η v m : ℝ)
    (hcorrection : 3 * η * v = m) :
    jitterWalsh χ p c η v m =
      walshCoefficient χ p (cubic c η p - (c * v) * (1 + 2 * p)) (c * v) := by
  cases χ <;> simp only [jitterWalsh, walshCoefficient, outcomeMoment, interactionMoment]
  · ring
  · rw [← hcorrection]
    ring

/-- An explicit constant in the single-site part of `B:lem:partial-stability`. -/
theorem partial_walsh_stability (χ : WalshCharacter) (p c η v s m ms : ℝ)
    (hp : |p| ≤ 1) (hc : 0 ≤ c) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hs0 : 0 ≤ s) (hsv : s ≤ v)
    (hm0 : 0 ≤ m) (hm : m ≤ 3 * v ^ 2)
    (hms0 : 0 ≤ ms) (hms : ms ≤ 3 * v ^ 2) (hcorrection : 3 * η * v = m) :
    |jitterWalsh χ p c η s ms -
      walshCoefficient χ p (cubic c η p - (c * v) * (1 + 2 * p)) (c * v)| ≤
      3 * (c * v) := by
  rw [← full_jitter_walsh χ p c η v m hcorrection]
  have hcv : 0 ≤ c * v := mul_nonneg hc hv0
  cases χ with
  | constant => simpa [jitterWalsh] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hcv
  | propensity => simpa [jitterWalsh] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hcv
  | outcome =>
    exact (outcomeMoment_stability p c η v s hp hc hs0 hsv).trans (by linarith)
  | interaction =>
    exact interactionMoment_stability p c η v s m ms hp hc hη0 hη1 hv0 hv1
      hs0 hsv hm0 hm hms0 hms

/-- Independent site coefficients accumulate at most the sum of their errors.
The |coefficient| ≤ 1 hypotheses are discharged by binary probability laws. -/
theorem joint_walsh_stability {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ξ : ι → Type*} [∀ i, Fintype (Ξ i)] (laws : ∀ i, FiniteLaw (Ξ i))
    (f : ∀ i, Ξ i → ℝ) (target error : ι → ℝ)
    (hf : ∀ i, |(laws i).expect (f i)| ≤ 1) (ht : ∀ i, |target i| ≤ 1)
    (herr : ∀ i, |(laws i).expect (f i) - target i| ≤ error i) :
    |(FiniteLaw.independent laws).expect (fun ω => ∏ i, f i (ω i)) -
      ∏ i, target i| ≤ ∑ i, error i := by
  rw [FiniteLaw.expect_independent_prod laws f]
  exact (abs_prod_sub_prod_le Finset.univ (fun i => (laws i).expect (f i)) target
    (fun i _ => hf i) (fun i _ => ht i)).trans (Finset.sum_le_sum (fun i _ => herr i))

end CausalLowerbound.PartB
