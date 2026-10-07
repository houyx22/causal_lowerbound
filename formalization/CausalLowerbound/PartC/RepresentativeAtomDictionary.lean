import CausalLowerbound.PartC.RepresentativeAverage

/-! The complete finite positive-atom stencil in representative factors.
This dictionary is independent of the target being polarized. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartC.Representative

open PartB.Polarization

abbrev Masks (ι : Type*) := (ι → Bool) × (ι → Bool)
abbrev PolynomialBasis (d ι : Type*) (D : ℕ) := ι → Fin (D + 1) × ((d → ℤ) × Bool)
abbrev PolynomialAtom (d ι : Type*) (D : ℕ) := PolynomialBasis d ι D × Masks ι

variable {d ι J : Type*} [Fintype d] [Fintype ι] [Fintype J]
  [DecidableEq ι] [DecidableEq J] {D : ℕ}

def affineFactor (g : ι → Factor d J D) (θ : ℝ) (b : ι → Bool) (i : ι) : Factor d J D :=
  if b i then positiveFactor θ (g i) else factorUnit

def atomFactor (g : ι → Factor d J D) (θ : ℝ) (m : Masks ι) : Factor d J D :=
  averageFactor (affineFactor g θ m.1) m.2

theorem affineFactor_re (g : ι → Factor d J D) (θ : ℝ) (b : ι → Bool) (i : ι)
    (x : Wiener.Torus d) (z : ℝ) (ζ : J → Bool) :
    (factorValue x z ζ (affineFactor g θ b i)).re =
      if b i then 1 + θ * (factorValue x z ζ (g i)).re else 1 := by
  unfold affineFactor
  split_ifs <;> simp only [positiveFactor_value, factorUnit_value, Complex.add_re, Complex.one_re,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem atomFactor_re (g : ι → Factor d J D) (θ : ℝ) (m : Masks ι)
    (x : Wiener.Torus d) (z : ℝ) (ζ : J → Bool) :
    (factorValue x z ζ (atomFactor g θ m)).re =
      stencilAtom (fun i (p : Wiener.Torus d × ℝ) => (factorValue p.1 p.2 ζ (g i)).re) θ m (x, z) := by
  rw [atomFactor, averageFactor_re]
  simp only [affineFactor_re, stencilAtom, averageAtom, affineDensity]

theorem atomFactor_real (g : ι → Factor d J D) (θ : ℝ) (m : Masks ι)
    (x : Wiener.Torus d) (z : ℝ) (ζ : J → Bool)
    (hg : ∀ i, (factorValue x z ζ (g i)).im = 0) :
    (factorValue x z ζ (atomFactor g θ m)).im = 0 := by
  apply averageFactor_real
  intro i
  unfold affineFactor
  split_ifs
  · exact positiveFactor_real θ _ x z ζ (hg i)
  · simp

theorem atomFactor_norm (g : ι → Factor d J D) (hg : ∀ i, ‖g i‖ ≤ 1) (θ : ℝ) (m : Masks ι) :
    ‖atomFactor g θ m‖ ≤ 1 + |θ| := by
  apply averageFactor_norm _ _ _ (le_add_of_nonneg_right (abs_nonneg θ))
  intro i
  unfold affineFactor
  split_ifs
  · exact positiveFactor_norm θ _ (hg i)
  · rw [factorUnit_norm]
    exact le_add_of_nonneg_right (abs_nonneg θ)

theorem atomFactor_symbol_bound (g : ι → Factor d J D) (θ : ℝ) (m : Masks ι) (j : J)
    (σ : ℝ) (hσ : 0 ≤ σ) (hg : ∀ i, ‖factorSymbol j (g i)‖ ≤ σ) :
    ‖factorSymbol j (atomFactor g θ m)‖ ≤ |θ| * σ := by
  apply averageFactor_symbol_bound _ _ _ _ (mul_nonneg (abs_nonneg _) hσ)
  intro i
  unfold affineFactor
  split_ifs
  · rw [positiveFactor_symbol]
    exact mul_le_mul_of_nonneg_left (hg i) (abs_nonneg _)
  · simp only [factorSymbol_factorUnit, norm_zero]
    positivity

theorem atomFactor_linearMean (L : Factor d J D →ₗ[ℝ] ℝ) (hL : L factorUnit = 1)
    (g : ι → Factor d J D) (hg : ∀ i, L (g i) = 0) (θ : ℝ) (m : Masks ι) : L (atomFactor g θ m) = 1 := by
  apply averageFactor_linearMean L hL
  intro i
  unfold affineFactor
  split_ifs
  · simp [positiveFactor, hL, hg]
  · exact hL

theorem atomFactor_range (g : ι → Factor d J D) (hg : ∀ i, ‖g i‖ ≤ 1)
    (θ : ℝ) (hθ : 0 ≤ θ) (m : Masks ι) (x : Wiener.Torus d) (z : ℝ) (hz : |z| ≤ 1) (ζ : J → Bool) :
    1 - θ ≤ (factorValue x z ζ (atomFactor g θ m)).re ∧
      (factorValue x z ζ (atomFactor g θ m)).re ≤ 1 + θ := by
  apply averageFactor_range _ _ _ _ θ hθ
  intro i
  unfold affineFactor
  split_ifs
  · simpa only [abs_of_nonneg hθ] using positiveFactor_range θ (g i) (hg i) x z hz ζ
  · simp only [factorUnit_value, Complex.one_re]
    constructor <;> linarith

theorem atomFactor_positive (g : ι → Factor d J D) (hg : ∀ i, ‖g i‖ ≤ 1)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (m : Masks ι)
    (x : Wiener.Torus d) (z : ℝ) (hz : |z| ≤ 1) (ζ : J → Bool) :
    0 < (factorValue x z ζ (atomFactor g θ m)).re :=
  (sub_pos.mpr hθ1).trans_le (atomFactor_range g hg θ hθ m x z hz ζ).1

theorem polynomialAtom_countable : Countable (PolynomialAtom d ι D) := inferInstance

end CausalLowerbound.PartC.Representative
