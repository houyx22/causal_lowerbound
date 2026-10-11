import CausalLowerbound.FiniteProductBounds

/-! A second-order product comparison requiring only equality of the
one-coordinate means. No independence between the factors is assumed. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.UniformLowerBound

/-- A finite-size constant; the fixed-component cutoff needs no asymptotic
estimate for this recurrence. -/
def centeredProductConstant (M : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => M * centeredProductConstant M n + 2 * n * M ^ n

theorem centeredProductConstant_nonneg (M : ℝ) (hM : 0 ≤ M) (n : ℕ) :
    0 ≤ centeredProductConstant M n := by
  induction n with
  | zero => simp [centeredProductConstant]
  | succ n ih => simp only [centeredProductConstant]; positivity

theorem centeredProductConstant_mono (M : ℝ) (hM : 1 ≤ M) :
    Monotone (centeredProductConstant M) := by
  apply monotone_nat_of_le_succ
  intro n
  have hK := centeredProductConstant_nonneg M (zero_le_one.trans hM) n
  have hprod := mul_le_mul_of_nonneg_right hM hK
  have hrest : 0 ≤ 2 * (n : ℝ) * M^n := by positivity
  simp only [centeredProductConstant]
  nlinarith only [hprod, hrest]

theorem bounded_product_difference {I : Type*} (s : Finset I) (f g : I → ℝ)
    (M δ : ℝ) (hM : 1 ≤ M)
    (hf : ∀ i ∈ s, |f i| ≤ M) (hg : ∀ i ∈ s, |g i| ≤ M)
    (hδ : ∀ i ∈ s, |f i - g i| ≤ δ) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤ M ^ s.card * s.card * δ := by
  apply (abs_prod_sub_prod_le_bounded s f g M hM hf hg).trans
  calc
    M ^ s.card * ∑ i ∈ s, |f i - g i| ≤ M ^ s.card * ∑ _i ∈ s, δ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hδ)
        (pow_nonneg (zero_le_one.trans hM) _)
    _ = _ := by simp [mul_assoc]

/-- Shared first moments remove the linear error of a product mixture.
The baseline `d` need not itself be the shared mean. -/
theorem common_mean_product_difference {I Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (s : Finset I) (d : I → ℝ) (f g : I → Ω → ℝ)
    (M B δ : ℝ) (hM : 1 ≤ M) (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hd : ∀ i ∈ s, |d i| ≤ M)
    (hf : ∀ i ∈ s, ∀ ω, |f i ω| ≤ M)
    (hg : ∀ i ∈ s, ∀ ω, |g i ω| ≤ M)
    (hfb : ∀ i ∈ s, ∀ ω, |f i ω - d i| ≤ B)
    (hgb : ∀ i ∈ s, ∀ ω, |g i ω - d i| ≤ B)
    (hfg : ∀ i ∈ s, ∀ ω, |f i ω - g i ω| ≤ δ)
    (hmean : ∀ i ∈ s, μ.expect (f i) = μ.expect (g i)) :
    |μ.expect (fun ω => ∏ i ∈ s, f i ω) -
      μ.expect (fun ω => ∏ i ∈ s, g i ω)| ≤
      centeredProductConstant M s.card * δ * B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [centeredProductConstant]
  | @insert i s hi ih =>
    have his : i ∈ insert i s := Finset.mem_insert_self _ _
    have hin (j : I) (hj : j ∈ s) : j ∈ insert i s := Finset.mem_insert_of_mem hj
    have hrec := ih (fun j hj => hd j (hin j hj))
      (fun j hj => hf j (hin j hj)) (fun j hj => hg j (hin j hj))
      (fun j hj => hfb j (hin j hj)) (fun j hj => hgb j (hin j hj))
      (fun j hj => hfg j (hin j hj)) (fun j hj => hmean j (hin j hj))
    let F : Ω → ℝ := fun ω => ∏ j ∈ s, f j ω
    let G : Ω → ℝ := fun ω => ∏ j ∈ s, g j ω
    let D : ℝ := ∏ j ∈ s, d j
    have hFD (ω : Ω) : |F ω - D| ≤ M ^ s.card * s.card * B :=
      bounded_product_difference s (fun j => f j ω) d M B hM
        (fun j hj => hf j (hin j hj) ω) (fun j hj => hd j (hin j hj))
        (fun j hj => hfb j (hin j hj) ω)
    have hFG (ω : Ω) : |F ω - G ω| ≤ M ^ s.card * s.card * δ :=
      bounded_product_difference s (fun j => f j ω) (fun j => g j ω) M δ hM
        (fun j hj => hf j (hin j hj) ω) (fun j hj => hg j (hin j hj) ω)
        (fun j hj => hfg j (hin j hj) ω)
    have he : μ.expect (fun ω => f i ω * F ω) - μ.expect (fun ω => g i ω * G ω) =
        d i * (μ.expect F - μ.expect G) +
        μ.expect (fun ω => (f i ω - g i ω) * (F ω - D)) +
        μ.expect (fun ω => (g i ω - d i) * (F ω - G ω)) := by
      rw [← μ.expect_sub]
      have hid (ω : Ω) : f i ω * F ω - g i ω * G ω =
          d i * (F ω - G ω) + (f i ω - g i ω) * (F ω - D) +
          (g i ω - d i) * (F ω - G ω) + (f i ω - g i ω) * D := by ring
      simp only [hid, μ.expect_add, μ.expect_mul, μ.expect_mul_const,
        μ.expect_sub, hmean i his, sub_self, zero_mul, add_zero]
    have hfirst : |d i * (μ.expect F - μ.expect G)| ≤
        M * (centeredProductConstant M s.card * δ * B) := by
      rw [abs_mul]
      exact mul_le_mul (hd i his) hrec (abs_nonneg _) (zero_le_one.trans hM)
    have hsecond : |μ.expect (fun ω => (f i ω - g i ω) * (F ω - D))| ≤
        δ * (M ^ s.card * s.card * B) := by
      apply μ.abs_expect_le_bound
      intro ω
      rw [abs_mul]
      exact mul_le_mul (hfg i his ω) (hFD ω) (abs_nonneg _) hδ
    have hthird : |μ.expect (fun ω => (g i ω - d i) * (F ω - G ω))| ≤
        B * (M ^ s.card * s.card * δ) := by
      apply μ.abs_expect_le_bound
      intro ω
      rw [abs_mul]
      exact mul_le_mul (hgb i his ω) (hFG ω) (abs_nonneg _) hB
    simp only [Finset.prod_insert hi, Finset.card_insert_of_not_mem hi]
    change |μ.expect (fun ω => f i ω * F ω) - μ.expect (fun ω => g i ω * G ω)| ≤ _
    rw [he]
    calc
      _ ≤ |d i * (μ.expect F - μ.expect G)| +
          |μ.expect (fun ω => (f i ω - g i ω) * (F ω - D))| +
          |μ.expect (fun ω => (g i ω - d i) * (F ω - G ω))| :=
        (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
      _ ≤ M * (centeredProductConstant M s.card * δ * B) +
          δ * (M ^ s.card * s.card * B) + B * (M ^ s.card * s.card * δ) :=
        add_le_add (add_le_add hfirst hsecond) hthird
      _ = _ := by simp only [centeredProductConstant]; ring

end CausalLowerbound.UniformLowerBound
