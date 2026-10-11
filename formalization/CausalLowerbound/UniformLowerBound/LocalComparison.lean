import CausalLowerbound.UniformLowerBound.CenteredProducts
import CausalLowerbound.FiniteHellinger
import Mathlib.Tactic.GCongr

/-! Local likelihoods and the finite-mixture comparison for the uniform
covariate construction. The sign distribution enters only through two moments. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.UniformLowerBound

def likelihoodP1 (a b r t u g : ℝ) : ℝ := 1 + 2*b*t*u + 4*a*b*r*t*g
def likelihoodP2 (a b r t u g : ℝ) : ℝ :=
  1 + 2*a*r*u + 4*a*b*r*t*g + 8*a^2*b*t*u*g
def likelihoodQ (a b r t u : ℝ) : ℝ :=
  1 + 2*a*r*u + 2*b*t*u + 4*a*b*r*t*u^2

def likelihoodP (regime : Bool) (a b r t u g : ℝ) : ℝ :=
  if regime then likelihoodP2 a b r t u g else likelihoodP1 a b r t u g

theorem expect_likelihoodP1 {Λ : Type*} [Fintype Λ] (μ : FiniteLaw Λ)
    (U : Λ → ℝ) (a b r t g : ℝ) (hU : μ.expect U = 0) :
    μ.expect (fun ζ => likelihoodP1 a b r t (U ζ) g) = 1 + 4*a*b*r*t*g := by
  simp only [likelihoodP1, μ.expect_add, μ.expect_const, μ.expect_mul, hU, mul_zero,
    add_zero]

theorem expect_likelihoodP2 {Λ : Type*} [Fintype Λ] (μ : FiniteLaw Λ)
    (U : Λ → ℝ) (a b r t g : ℝ) (hU : μ.expect U = 0) :
    μ.expect (fun ζ => likelihoodP2 a b r t (U ζ) g) = 1 + 4*a*b*r*t*g := by
  simp only [likelihoodP2, μ.expect_add, μ.expect_const, μ.expect_mul_const,
    μ.expect_mul, hU, mul_zero, zero_mul, add_zero]

theorem expect_likelihoodQ {Λ : Type*} [Fintype Λ] (μ : FiniteLaw Λ)
    (U : Λ → ℝ) (a b r t g : ℝ) (hU : μ.expect U = 0)
    (hU2 : μ.expect (fun ζ => (U ζ)^2) = g) :
    μ.expect (fun ζ => likelihoodQ a b r t (U ζ)) = 1 + 4*a*b*r*t*g := by
  simp only [likelihoodQ, μ.expect_add, μ.expect_const, μ.expect_mul, hU, hU2,
    mul_zero, add_zero]

theorem one_observation_mixture_equality {Λ : Type*} [Fintype Λ]
    (μ : FiniteLaw Λ) (regime : Bool) (U : Λ → ℝ) (a b r t g : ℝ)
    (hU : μ.expect U = 0) (hU2 : μ.expect (fun ζ => (U ζ)^2) = g) :
    μ.expect (fun ζ => likelihoodP regime a b r t (U ζ) g) =
      μ.expect (fun ζ => likelihoodQ a b r t (U ζ)) := by
  rw [expect_likelihoodQ μ U a b r t g hU hU2]
  cases regime
  · exact expect_likelihoodP1 μ U a b r t g hU
  · exact expect_likelihoodP2 μ U a b r t g hU

/-- An envelope valid for either smoothness regime. -/
def likelihoodEnvelope (N : ℝ) : ℝ := 10*N + 4*N^2 + 4

theorem likelihoodEnvelope_nonneg (N : ℝ) (hN : 0 ≤ N) :
    0 ≤ likelihoodEnvelope N := by unfold likelihoodEnvelope; positivity

private theorem linear_bound (a r u N : ℝ) (ha : 0 ≤ a)
    (hr : |r| ≤ 1) (hu : |u| ≤ N) : |2*a*r*u| ≤ 2*a*N := by
  norm_num only [abs_mul, abs_of_nonneg ha]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    2*a*|r| * |u| ≤ 2*a*1*N := by gcongr
    _ = _ := by ring

private theorem cross_bound (a b r t g : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hr : |r| ≤ 1) (ht : |t| ≤ 1) (hg : |g| ≤ 1) :
    |4*a*b*r*t*g| ≤ 4*a*b := by
  norm_num only [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  calc
    4*a*b*|r| * |t| * |g| ≤ 4*a*b*1*1*1 := by gcongr
    _ = _ := by ring

private theorem square_bound (a b r t u N : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hr : |r| ≤ 1) (ht : |t| ≤ 1) (hu : |u| ≤ N) :
    |4*a*b*r*t*u^2| ≤ 4*a*b*N^2 := by
  norm_num only [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb, abs_pow]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  calc
    4*a*b*|r| * |t| * |u|^2 ≤ 4*a*b*1*1*N^2 := by gcongr
    _ = _ := by ring

private theorem cubic_bound (a b t u g N : ℝ) (hb : 0 ≤ b)
    (ht : |t| ≤ 1) (hu : |u| ≤ N) (hg : |g| ≤ 1) :
    |8*a^2*b*t*u*g| ≤ 8*a^2*b*N := by
  norm_num only [abs_mul, abs_of_nonneg hb, abs_pow, sq_abs]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)]
  calc
    8*a^2*b*|t| * |u| * |g| ≤ 8*a^2*b*1*N*1 := by
      have hN := (abs_nonneg u).trans hu
      gcongr
    _ = _ := by ring

theorem likelihood_bounds (regime : Bool) (a b r t u g N : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hN : 0 ≤ N) (hr : |r| ≤ 1) (ht : |t| ≤ 1)
    (hu : |u| ≤ N) (hg : |g| ≤ 1) :
    |likelihoodP regime a b r t u g - 1| ≤ likelihoodEnvelope N * (a+b) ∧
    |likelihoodQ a b r t u - 1| ≤ likelihoodEnvelope N * (a+b) ∧
    |likelihoodP regime a b r t u g - likelihoodQ a b r t u| ≤
      likelihoodEnvelope N * (if regime then b else a) := by
  have hla := linear_bound a r u N ha hr hu
  have hlb := linear_bound b t u N hb ht hu
  have hc := cross_bound a b r t g ha hb hr ht hg
  have hs := square_bound a b r t u N ha hb hr ht hu
  have ht' := cubic_bound a b t u g N hb ht hu hg
  have hab_a : a*b ≤ a := by nlinarith only [ha, hb1]
  have hab_b : a*b ≤ b := by nlinarith only [hb, ha1]
  have ha2 : a^2 ≤ 1 := by nlinarith only [ha, ha1]
  have ha2b : a^2*b ≤ b := by nlinarith only [hb, ha2]
  have hca : |4*a*b*r*t*g| ≤ 4*a := hc.trans (by nlinarith only [hab_a])
  have hcb : |4*a*b*r*t*g| ≤ 4*b := hc.trans (by nlinarith only [hab_b])
  have hsa : |4*a*b*r*t*u^2| ≤ 4*a*N^2 := hs.trans (by nlinarith only [mul_le_mul_of_nonneg_right hab_a (sq_nonneg N)])
  have hsb : |4*a*b*r*t*u^2| ≤ 4*b*N^2 := hs.trans (by nlinarith only [mul_le_mul_of_nonneg_right hab_b (sq_nonneg N)])
  have htb : |8*a^2*b*t*u*g| ≤ 8*b*N := ht'.trans (by nlinarith only [mul_le_mul_of_nonneg_right ha2b hN])
  have hEa : 2*N ≤ likelihoodEnvelope N := by unfold likelihoodEnvelope; nlinarith only [hN, sq_nonneg N]
  have hEb : 2*N+4*N^2 ≤ likelihoodEnvelope N := by unfold likelihoodEnvelope; nlinarith only [hN]
  have hEc : 2*N+4 ≤ likelihoodEnvelope N := by unfold likelihoodEnvelope; nlinarith only [hN, sq_nonneg N]
  have hEd : 4+8*N ≤ likelihoodEnvelope N := by unfold likelihoodEnvelope; nlinarith only [hN, sq_nonneg N]
  have hq : |likelihoodQ a b r t u - 1| ≤ likelihoodEnvelope N*(a+b) := by
    have hh : likelihoodQ a b r t u - 1 = (2*a*r*u + 2*b*t*u) + 4*a*b*r*t*u^2 := by
      unfold likelihoodQ; ring
    rw [hh]
    calc
      _ ≤ (|2*a*r*u| + |2*b*t*u|) + |4*a*b*r*t*u^2| :=
        (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
      _ ≤ 2*a*N + 2*b*N + 4*b*N^2 := add_le_add (add_le_add hla hlb) hsb
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hEa ha, mul_le_mul_of_nonneg_right hEb hb]
  cases regime
  · change _ ∧ _ ∧ _ ≤ likelihoodEnvelope N*a
    simp only [likelihoodP, Bool.false_eq_true, ↓reduceIte]
    refine ⟨?_, hq, ?_⟩
    · have he : likelihoodP1 a b r t u g - 1 = 2*b*t*u + 4*a*b*r*t*g := by unfold likelihoodP1; ring
      rw [he]
      calc
        _ ≤ |2*b*t*u| + |4*a*b*r*t*g| := abs_add _ _
        _ ≤ 2*b*N + 4*b := add_le_add hlb hcb
        _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hEc hb,
          mul_nonneg (likelihoodEnvelope_nonneg N hN) ha]
    · have he : likelihoodP1 a b r t u g - likelihoodQ a b r t u =
          -2*a*r*u + (4*a*b*r*t*g - 4*a*b*r*t*u^2) := by
        unfold likelihoodP1 likelihoodQ; ring
      rw [he]
      have hn : |-2*a*r*u| = |2*a*r*u| := by ring_nf; rw [abs_neg]
      calc
        _ ≤ |-2*a*r*u| + (|4*a*b*r*t*g| + |4*a*b*r*t*u^2|) :=
          (abs_add _ _).trans (add_le_add_left (abs_sub _ _) _)
        _ ≤ 2*a*N + (4*a + 4*a*N^2) := by rw [hn]; exact add_le_add hla (add_le_add hca hsa)
        _ ≤ _ := by unfold likelihoodEnvelope; nlinarith only [mul_nonneg ha hN]
  · change _ ∧ _ ∧ _ ≤ likelihoodEnvelope N*b
    simp only [likelihoodP, ↓reduceIte]
    refine ⟨?_, hq, ?_⟩
    · have he : likelihoodP2 a b r t u g - 1 =
          (2*a*r*u + 4*a*b*r*t*g) + 8*a^2*b*t*u*g := by unfold likelihoodP2; ring
      rw [he]
      calc
        _ ≤ (|2*a*r*u| + |4*a*b*r*t*g|) + |8*a^2*b*t*u*g| :=
          (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
        _ ≤ 2*a*N + 4*b + 8*b*N := add_le_add (add_le_add hla hcb) htb
        _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hEa ha, mul_le_mul_of_nonneg_right hEd hb]
    · have he : likelihoodP2 a b r t u g - likelihoodQ a b r t u =
          (-2*b*t*u + (4*a*b*r*t*g - 4*a*b*r*t*u^2)) + 8*a^2*b*t*u*g := by
        unfold likelihoodP2 likelihoodQ; ring
      rw [he]
      have hn : |-2*b*t*u| = |2*b*t*u| := by ring_nf; rw [abs_neg]
      calc
        _ ≤ (|-2*b*t*u| + (|4*a*b*r*t*g| + |4*a*b*r*t*u^2|)) + |8*a^2*b*t*u*g| :=
          (abs_add _ _).trans (add_le_add_right ((abs_add _ _).trans (add_le_add_left (abs_sub _ _) _)) _)
        _ ≤ (2*b*N + (4*b + 4*b*N^2)) + 8*b*N := by rw [hn]; exact add_le_add (add_le_add hlb (add_le_add hcb hsb)) htb
        _ = _ := by unfold likelihoodEnvelope; ring

/-- The local constant is independent of the amplitudes and packet scales. -/
def componentConstant (N : ℝ) (n : ℕ) : ℝ :=
  centeredProductConstant (1 + 2 * likelihoodEnvelope N) n * (likelihoodEnvelope N)^2

theorem componentConstant_nonneg (N : ℝ) (hN : 0 ≤ N) (n : ℕ) :
    0 ≤ componentConstant N n := by
  unfold componentConstant
  exact mul_nonneg (centeredProductConstant_nonneg _
    (by have := likelihoodEnvelope_nonneg N hN; linarith) _) (sq_nonneg _)

theorem componentConstant_mono (N : ℝ) (hN : 0 ≤ N) : Monotone (componentConstant N) := by
  intro m n hmn
  exact mul_le_mul_of_nonneg_right
    (centeredProductConstant_mono _ (by have := likelihoodEnvelope_nonneg N hN; linarith) hmn)
    (sq_nonneg _)

theorem component_product_difference {I Λ : Type*} [Fintype Λ]
    (μ : FiniteLaw Λ) (regime : Bool) (s : Finset I)
    (r t g : I → ℝ) (U : I → Λ → ℝ) (a b N : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) (hN : 0 ≤ N)
    (hr : ∀ i ∈ s, |r i| ≤ 1) (ht : ∀ i ∈ s, |t i| ≤ 1)
    (hg : ∀ i ∈ s, |g i| ≤ 1) (hU : ∀ i ∈ s, ∀ ζ, |U i ζ| ≤ N)
    (hmean : ∀ i ∈ s, μ.expect (U i) = 0)
    (hsecond : ∀ i ∈ s, μ.expect (fun ζ => (U i ζ)^2) = g i) :
    |μ.expect (fun ζ => ∏ i ∈ s, likelihoodP regime a b (r i) (t i) (U i ζ) (g i)) -
      μ.expect (fun ζ => ∏ i ∈ s, likelihoodQ a b (r i) (t i) (U i ζ))| ≤
      componentConstant N s.card * (if regime then b else a) * (a+b) := by
  let L := likelihoodEnvelope N
  have hL : 0 ≤ L := likelihoodEnvelope_nonneg N hN
  have hM : 1 ≤ 1+2*L := by linarith
  have hsmall : 0 ≤ (if regime then b else a) := by cases regime <;> assumption
  have hbounds (i : I) (hi : i ∈ s) (ζ : Λ) :=
    likelihood_bounds regime a b (r i) (t i) (U i ζ) (g i) N ha ha1 hb hb1 hN
      (hr i hi) (ht i hi) (hU i hi ζ) (hg i hi)
  have hfull (x : ℝ) (hx : |x-1| ≤ L*(a+b)) : |x| ≤ 1+2*L := by
    calc
      |x| = |(x-1)+1| := by congr 1; ring
      _ ≤ |x-1| + |(1 : ℝ)| := abs_add _ _
      _ ≤ L*(a+b)+1 := by simpa using add_le_add_right hx 1
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left (add_le_add ha1 hb1) hL]
  have he := common_mean_product_difference μ s (fun _ => 1)
    (fun i ζ => likelihoodP regime a b (r i) (t i) (U i ζ) (g i))
    (fun i ζ => likelihoodQ a b (r i) (t i) (U i ζ))
    (1+2*L) (L*(a+b)) (L*(if regime then b else a)) hM
    (mul_nonneg hL (add_nonneg ha hb)) (mul_nonneg hL hsmall)
    (fun _ _ => by simpa using hM)
    (fun i hi ζ => hfull _ (hbounds i hi ζ).1)
    (fun i hi ζ => hfull _ (hbounds i hi ζ).2.1)
    (fun i hi ζ => (hbounds i hi ζ).1)
    (fun i hi ζ => (hbounds i hi ζ).2.1)
    (fun i hi ζ => (hbounds i hi ζ).2.2)
    (fun i hi => one_observation_mixture_equality μ regime (U i) a b (r i) (t i)
      (g i) (hmean i hi) (hsecond i hi))
  exact he.trans_eq (by unfold componentConstant; dsimp [L]; ring)

/-- The reference law removes the otherwise artificial cardinality factor
in a finite Hellinger bound. -/
theorem hellingerSq_le_of_density_error {W : Type*} [Fintype W]
    (R P Q : FiniteLaw W) (p q : W → ℝ) (lower error : ℝ)
    (hP : ∀ w, P.weight w = R.weight w * p w)
    (hQ : ∀ w, Q.weight w = R.weight w * q w)
    (hlower : 0 < lower) (hp : ∀ w, lower ≤ p w) (hq : ∀ w, 0 ≤ q w)
    (herr : ∀ w, |p w - q w| ≤ error) :
    P.hellingerSq Q ≤ error^2 / lower := by
  have hpoint (w : W) : (Real.sqrt (P.weight w) - Real.sqrt (Q.weight w))^2 ≤
      R.weight w * (error^2/lower) := by
    rw [hP w, hQ w, Real.sqrt_mul (R.nonneg w), Real.sqrt_mul (R.nonneg w),
      ← mul_sub, mul_pow, Real.sq_sqrt (R.nonneg w)]
    apply mul_le_mul_of_nonneg_left _ (R.nonneg w)
    apply (sqrt_sub_sq_le _ _ lower hlower (hp w) (hq w)).trans
    apply div_le_div_of_nonneg_right _ hlower.le
    nlinarith only [herr w, abs_nonneg (p w-q w), sq_abs (p w-q w)]
  calc
    P.hellingerSq Q ≤ ∑ w, R.weight w * (error^2/lower) := Finset.sum_le_sum (fun w _ => hpoint w)
    _ = error^2/lower := by rw [← Finset.sum_mul, R.total, one_mul]

/-- A component comparison for genuine finite output laws, whose densities
are products of the local likelihoods mixed over a shared prior. -/
theorem component_hellinger_bound {I Λ W : Type*} [Fintype Λ] [Fintype W]
    (μ : FiniteLaw Λ) (R P Q : FiniteLaw W) (regime : Bool) (s : Finset I)
    (r t : W → I → ℝ) (g : I → ℝ) (U : I → Λ → ℝ) (a b N κ : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) (hN : 0 ≤ N)
    (hκ : 0 < κ)
    (hr : ∀ w i, i ∈ s → |r w i| ≤ 1) (ht : ∀ w i, i ∈ s → |t w i| ≤ 1)
    (hg : ∀ i ∈ s, |g i| ≤ 1) (hU : ∀ i ∈ s, ∀ ζ, |U i ζ| ≤ N)
    (hmean : ∀ i ∈ s, μ.expect (U i) = 0)
    (hsecond : ∀ i ∈ s, μ.expect (fun ζ => (U i ζ)^2) = g i)
    (hpositive : ∀ w i, i ∈ s → ∀ ζ,
      κ ≤ likelihoodP regime a b (r w i) (t w i) (U i ζ) (g i))
    (hnonneg : ∀ w i, i ∈ s → ∀ ζ,
      0 ≤ likelihoodQ a b (r w i) (t w i) (U i ζ))
    (hP : ∀ w, P.weight w = R.weight w * μ.expect (fun ζ =>
      ∏ i ∈ s, likelihoodP regime a b (r w i) (t w i) (U i ζ) (g i)))
    (hQ : ∀ w, Q.weight w = R.weight w * μ.expect (fun ζ =>
      ∏ i ∈ s, likelihoodQ a b (r w i) (t w i) (U i ζ))) :
    P.hellingerSq Q ≤
      (componentConstant N s.card * (if regime then b else a) * (a+b))^2 / κ^s.card := by
  apply hellingerSq_le_of_density_error R P Q _ _ _ _ hP hQ (pow_pos hκ _)
  · intro w
    calc
      κ^s.card = μ.expect (fun _ => κ^s.card) := (μ.expect_const _).symm
      _ ≤ _ := by
        apply μ.expect_mono
        intro ζ
        rw [← Finset.prod_const]
        exact Finset.prod_le_prod (fun _ _ => hκ.le) (fun i hi => hpositive w i hi ζ)
  · intro w
    exact μ.expect_nonneg _ (fun ζ => Finset.prod_nonneg (fun i hi => hnonneg w i hi ζ))
  · intro w
    exact component_product_difference μ regime s (r w) (t w) g U a b N
      ha ha1 hb hb1 hN (hr w) (ht w) hg hU hmean hsecond

def componentHellingerConstant (N κ : ℝ) (cutoff : ℕ) : ℝ :=
  2 * (componentConstant N cutoff)^2 / (min 1 κ)^cutoff

theorem componentHellingerConstant_nonneg (N κ : ℝ) (hκ : 0 < κ) (cutoff : ℕ) :
    0 ≤ componentHellingerConstant N κ cutoff := by
  unfold componentHellingerConstant
  have hm : 0 < min 1 κ := lt_min zero_lt_one hκ
  positivity

theorem selected_amplitude_sq_le (regime : Bool) (a b : ℝ) :
    (if regime then b else a)^2 * (a+b)^2 ≤
      2 * (a^2*b^2 + (if regime then b^4 else a^4)) := by
  cases regime
  · simp only [Bool.false_eq_true, ↓reduceIte]
    nlinarith only [mul_nonneg (sq_nonneg a) (sq_nonneg (a-b))]
  · simp only [↓reduceIte]
    nlinarith only [mul_nonneg (sq_nonneg b) (sq_nonneg (a-b))]

/-- Conversion of the component estimate to a single constant for all
component sizes at most a fixed cutoff. No upper bound on `κ` is needed. -/
theorem component_hellinger_bound_cutoff {W : Type*} [Fintype W]
    (P Q : FiniteLaw W) (regime : Bool) (N κ a b : ℝ) (n cutoff : ℕ)
    (hN : 0 ≤ N) (hκ : 0 < κ) (hn : n ≤ cutoff)
    (hlocal : P.hellingerSq Q ≤
      (componentConstant N n * (if regime then b else a) * (a+b))^2 / κ^n) :
    P.hellingerSq Q ≤ componentHellingerConstant N κ cutoff *
      (a^2*b^2 + (if regime then b^4 else a^4)) := by
  have hm : 0 < min 1 κ := lt_min zero_lt_one hκ
  have hpow : (min 1 κ)^cutoff ≤ κ^n :=
    (pow_le_pow_of_le_one hm.le (min_le_left _ _) hn).trans
      (pow_le_pow_left₀ hm.le (min_le_right _ _) n)
  have hC : (componentConstant N n)^2 ≤ (componentConstant N cutoff)^2 :=
    pow_le_pow_left₀ (componentConstant_nonneg N hN n) (componentConstant_mono N hN hn) 2
  have hnum : (componentConstant N n * (if regime then b else a) * (a+b))^2 ≤
      2*(componentConstant N cutoff)^2 * (a^2*b^2 + (if regime then b^4 else a^4)) := by
    calc
      _ = (componentConstant N n)^2 * ((if regime then b else a)^2 * (a+b)^2) := by ring
      _ ≤ (componentConstant N cutoff)^2 * ((if regime then b else a)^2 * (a+b)^2) :=
        mul_le_mul_of_nonneg_right hC (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ ≤ (componentConstant N cutoff)^2 * (2*(a^2*b^2 + (if regime then b^4 else a^4))) :=
        mul_le_mul_of_nonneg_left (selected_amplitude_sq_le regime a b) (sq_nonneg _)
      _ = _ := by ring
  calc
    _ ≤ (componentConstant N n * (if regime then b else a) * (a+b))^2 / κ^n := hlocal
    _ ≤ (componentConstant N n * (if regime then b else a) * (a+b))^2 / (min 1 κ)^cutoff :=
      div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hm _) hpow
    _ ≤ (2*(componentConstant N cutoff)^2 * (a^2*b^2 + (if regime then b^4 else a^4))) /
        (min 1 κ)^cutoff := div_le_div_of_nonneg_right hnum (pow_nonneg hm.le _)
    _ = _ := by unfold componentHellingerConstant; ring

end CausalLowerbound.UniformLowerBound
