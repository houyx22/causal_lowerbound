import CausalLowerbound.PartB.PartialStability

/-!
# The coded likelihood as a genuine binary probability experiment

The parameter constraints are explicit. Verifying them uniformly for the paper's
smooth nuisance construction remains a separate task.
-/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.PartB

theorem sign_sq (r : Bool) : sign r ^ 2 = 1 := by cases r <;> norm_num [sign]

theorem abs_sign (r : Bool) : |sign r| = 1 := by cases r <;> norm_num [sign]

theorem binary_factor_lower (r : Bool) (z κ : ℝ) (hz : |z| ≤ κ) :
    1 - κ ≤ 1 + sign r * z := by
  rcases abs_le.mp hz with ⟨hl, hu⟩
  cases r <;> simp only [sign] <;> linarith

/-- Explicit binary cell lower bound used later in Hellinger comparisons. -/
theorem binary_cell_lower (r t : Bool) (p y τ κ : ℝ) (hκ : κ ≤ 1)
    (hp : |p| ≤ κ) (hy : |y + τ * (1 + sign r)| ≤ κ) :
    (1 - κ) ^ 2 / 4 ≤ codedLikelihood (sign r) (sign t) p y τ / 4 := by
  rw [codedLikelihood_eq_factors _ _ _ _ _ (sign_sq r)]
  have h₁ := binary_factor_lower r p κ hp
  have h₂ := binary_factor_lower t (y + τ * (1 + sign r)) κ hy
  have hbase : 0 ≤ 1 - κ := sub_nonneg.mpr hκ
  have hprod := mul_le_mul h₁ h₂ hbase (hbase.trans h₁)
  nlinarith

def BinaryLegal (p y τ : ℝ) : Prop :=
  |p| ≤ 1 ∧ ∀ r : Bool, |y + τ * (1 + sign r)| ≤ 1

/-- Cell probabilities are L/4; their nonnegativity and normalization are proved. -/
def binaryLaw (p y τ : ℝ) (h : BinaryLegal p y τ) : FiniteLaw (Bool × Bool) where
  weight z := codedLikelihood (sign z.1) (sign z.2) p y τ / 4
  nonneg z := by
    simpa using binary_cell_lower z.1 z.2 p y τ 1 le_rfl h.1 (h.2 z.1)
  total := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, sign, codedLikelihood]
    ring

def walshCharacter (χ : WalshCharacter) (z : Bool × Bool) : ℝ :=
  match χ with
  | .constant => 1
  | .propensity => sign z.1
  | .outcome => sign z.2
  | .interaction => sign z.1 * sign z.2

theorem abs_walshCharacter (χ : WalshCharacter) (z : Bool × Bool) :
    |walshCharacter χ z| = 1 := by
  cases χ <;> simp [walshCharacter, abs_sign, abs_mul]

/-- The algebraic Walsh coefficients are actual expectations of binary characters. -/
theorem binary_walsh_expect (p y τ : ℝ) (h : BinaryLegal p y τ) (χ : WalshCharacter) :
    (binaryLaw p y τ h).expect (walshCharacter χ) = walshCoefficient χ p y τ := by
  cases χ <;>
    simp only [FiniteLaw.expect, binaryLaw, Fintype.sum_prod_type, Fintype.sum_bool,
      walshCharacter, walshCoefficient, codedLikelihood, sign] <;> ring

theorem walshCoefficient_abs_le_one (p y τ : ℝ) (h : BinaryLegal p y τ)
    (χ : WalshCharacter) : |walshCoefficient χ p y τ| ≤ 1 := by
  rw [← binary_walsh_expect p y τ h χ]
  exact (binaryLaw p y τ h).abs_expect_le_bound _ 1
    (fun z => le_of_eq (abs_walshCharacter χ z))

/-- Mixtures of legal binary experiments also have coefficients in [-1,1]. -/
theorem averaged_walsh_abs_le_one {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (p y τ : Ω → ℝ) (h : ∀ ω, BinaryLegal (p ω) (y ω) (τ ω))
    (χ : WalshCharacter) :
    |μ.expect (fun ω => walshCoefficient χ (p ω) (y ω) (τ ω))| ≤ 1 :=
  μ.abs_expect_le_bound _ 1 (fun ω => walshCoefficient_abs_le_one _ _ _ (h ω) χ)

end CausalLowerbound.PartB
