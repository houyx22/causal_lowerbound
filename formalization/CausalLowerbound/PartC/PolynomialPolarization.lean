import CausalLowerbound.PartC.RepresentativeAtomDictionary
import CausalLowerbound.PartC.RepresentativeSymTensor
import CausalLowerbound.PartC.WalshPolarizationWeights

/-! Exact positive polarization of each polynomial--trigonometric tensor.
The coefficients are actual Walsh arrays and are bounded before sign evaluation. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartC.Representative

open PartB.Polarization

variable {d ι J : Type*} [Fintype d] [Fintype ι] [Fintype J]
  [DecidableEq ι] [DecidableEq J] {D : ℕ}

def polynomialBasisTensor (w : PolynomialBasis d ι D) : Array d ι J D :=
  symTensor (fun i => basisFactor (w i).1 (w i).2.1 (w i).2.2)

def polynomialDictionary (w : PolynomialBasis d ι D) (a : ι → Walsh.Coefficients J)
    (θ : ℝ) (m : Masks ι) : Factor d J D :=
  atomFactor (fun i => centeredFactor (w i).1 (w i).2.1 (w i).2.2 (a i)) θ m

def polynomialAtomTensor (w : PolynomialBasis d ι D) (a : ι → Walsh.Coefficients J)
    (θ : ℝ) (m : Masks ι) : Array d ι J D :=
  tensor (fun _ : ι => polynomialDictionary w a θ m)

theorem polynomialBasisTensor_norm (w : PolynomialBasis d ι D) :
    ‖(polynomialBasisTensor w : Array d ι J D)‖ ≤ 1 := by
  apply (symTensor_norm _).trans
  simpa using Finset.prod_le_prod (s := (Finset.univ : Finset ι))
    (fun i _ => norm_nonneg (basisFactor (w i).1 (w i).2.1 (w i).2.2 : Factor d J D))
    (fun i _ => basisFactor_norm (J := J) (w i).1 (w i).2.1 (w i).2.2)

theorem polynomialDictionary_norm (w : PolynomialBasis d ι D) (a : ι → Walsh.Coefficients J)
    (ha : ∀ i, ‖a i‖ ≤ 1) (θ : ℝ) (m : Masks ι) : ‖polynomialDictionary w a θ m‖ ≤ 1 + |θ| :=
  atomFactor_norm _ (fun i => centeredFactor_norm _ _ _ _ (ha i)) θ m

theorem polynomialDictionary_real (w : PolynomialBasis d ι D) (a : ι → Walsh.Coefficients J)
    (θ : ℝ) (m : Masks ι) (x : Wiener.Torus d) (z : ℝ) (ζ : J → Bool) :
    (factorValue x z ζ (polynomialDictionary w a θ m)).im = 0 :=
  atomFactor_real _ θ m x z ζ (fun i => centeredFactor_real _ _ _ _ x z ζ)

theorem polynomialAtomTensor_norm (w : PolynomialBasis d ι D) (a : ι → Walsh.Coefficients J)
    (ha : ∀ i, ‖a i‖ ≤ 1) (θ : ℝ) (m : Masks ι) :
    ‖polynomialAtomTensor w a θ m‖ ≤ (1 + |θ|) ^ Fintype.card ι := by
  apply (tensor_norm _).trans
  simpa using Finset.prod_le_prod (s := (Finset.univ : Finset ι))
    (fun _ _ => norm_nonneg (polynomialDictionary w a θ m))
    (fun _ _ => polynomialDictionary_norm w a ha θ m)

theorem basisFactor_real_decomposition (e : Fin (D + 1)) (q : d → ℤ) (b : Bool)
    (a : Walsh.Coefficients J) (x : Wiener.Torus d) (z : ℝ) (ζ : J → Bool) :
    (factorValue x z ζ (basisFactor e q b : Factor d J D)).re = Walsh.evaluate ζ a +
      2 * (factorValue x z ζ (centeredFactor e q b a)).re := by
  rw [basisFactor_value, centeredFactor_value]
  simp only [Complex.real_smul, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem stencilAtom_half_double {X : Type*} (g : ι → X → ℝ) (θ : ℝ) (m : Masks ι) (x : X) :
    stencilAtom (fun i y => 2 * g i y) (θ / 2) m x = stencilAtom g θ m x := by
  unfold stencilAtom averageAtom affineDensity
  split_ifs
  · rfl
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring

theorem polynomial_basis_polarization [Nonempty ι] (w : PolynomialBasis d ι D)
    (a : ι → Walsh.Coefficients J) (θ : ℝ) (hθ : θ ≠ 0)
    (x : Wiener.Torus (ι × d)) (z : ι → ℝ) (ζ : J → Bool) :
    pointValue x z ζ (polynomialBasisTensor w : Array d ι J D) =
      ∑ m : Masks ι, Walsh.evaluate ζ (Walsh.polarizationWeight a (θ / 2) m) *
        pointValue x z ζ (polynomialAtomTensor w a θ m) := by
  let g : ι → (Wiener.Torus d × ℝ) → ℝ := fun i p =>
    (factorValue p.1 p.2 ζ (centeredFactor (w i).1 (w i).2.1 (w i).2.2 (a i))).re
  let c : ι → ℝ := fun i => Walsh.evaluate ζ (a i)
  let args : ι → Wiener.Torus d × ℝ := fun i => (fun j => x (i, j), z i)
  have hreal (i : ι) (y : Wiener.Torus d) (t : ℝ) :
      (factorValue y t ζ (basisFactor (w i).1 (w i).2.1 (w i).2.2 : Factor d J D)).im = 0 := by
    rw [basisFactor_value]
    simp only [Complex.real_smul, Complex.mul_im, Complex.ofReal_im,
      Wiener.trigSeries_real, mul_zero, zero_mul, add_zero]
  have hleft : pointValue x z ζ (polynomialBasisTensor w : Array d ι J D) =
      symProduct (fun i p => c i + 2 * g i p) args := by
    rw [polynomialBasisTensor, symTensor_value _ x z ζ hreal]
    apply congrArg (fun f => symProduct f args)
    funext i p
    exact basisFactor_real_decomposition _ _ _ _ p.1 p.2 ζ
  have hright (m : Masks ι) : pointValue x z ζ (polynomialAtomTensor w a θ m) =
      ∏ i, stencilAtom g θ m (args i) := by
    rw [polynomialAtomTensor, tensor_value_real _ x z ζ
      (fun _ => polynomialDictionary_real w a θ m _ _ ζ)]
    simp only [polynomialDictionary, atomFactor_re]
    rfl
  rw [hleft, positive_polarization c (fun i p => 2 * g i p) (θ / 2)
    (div_ne_zero hθ (by norm_num)) args]
  apply Finset.sum_congr rfl
  intro m _
  rw [Walsh.evaluate_polarizationWeight, hright]
  simp only [stencilAtom_half_double]
  rfl

end CausalLowerbound.PartC.Representative
