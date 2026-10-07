import CausalLowerbound.WienerSymmetric
import CausalLowerbound.PartB.CarrierConstruction

/-!
# Positive polarization on the full symmetric real Wiener algebra

The coefficient map takes a Wiener function, rather than an externally
supplied expansion. The dictionary, its natural-number indexing, and all
coefficient and reconstruction bounds are constructed here.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartB.PositiveWiener
open Wiener Polarization
open MeasureTheory UnitAddTorus

attribute [local instance] Real.fact_zero_lt_one
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d ι : Type*} [Fintype d] [Fintype ι] [DecidableEq ι]

theorem atomTensor_mem (θ : ℝ) (m : AtomIndex d ι) :
    atomTensor θ m ∈ symmetricRealSubalgebra (d := d) (ι := ι) := by
  have hr (y : Torus d) : toContinuous (dictionary θ m) y =
      ((toContinuous (dictionary θ m) y).re : ℂ) := by
    apply Complex.ext <;> simp [dictionary_real]
  constructor
  · intro x
    rw [atomTensor, tensor_value]
    have hp : (∏ i : ι, toContinuous (dictionary θ m) (fun j => x (i, j))) =
        ((∏ i : ι, (toContinuous (dictionary θ m) (fun j => x (i, j))).re : ℝ) : ℂ) := by
      rw [Complex.ofReal_prod]
      exact Finset.prod_congr rfl (fun i _ => hr _)
    rw [hp, Complex.ofReal_im]
  · intro σ x
    simp only [atomTensor, tensor_value, permuteSlots]
    exact Equiv.prod_comp σ (fun i => toContinuous (dictionary θ m) (fun j => x (i, j)))

def symmetricAtom (θ : ℝ) (m : AtomIndex d ι) : SymmetricReal d ι :=
  ⟨atomTensor θ m, atomTensor_mem θ m⟩

theorem symmetricAtom_bound (θ : ℝ) (hθ : 0 ≤ θ) (m : AtomIndex d ι) :
    ‖symmetricAtom θ m‖ ≤ (1 + θ) ^ Fintype.card ι := atomTensor_bound θ hθ m

def polarizationBound (θ : ℝ) : ℝ := stencilBound (ι := ι) θ * (2 : ℝ) ^ Fintype.card ι

theorem stencilBound_nonneg (θ : ℝ) : 0 ≤ stencilBound (ι := ι) θ := by
  unfold stencilBound
  positivity

theorem polarizationBound_nonneg (θ : ℝ) : 0 ≤ polarizationBound (ι := ι) θ :=
  mul_nonneg (stencilBound_nonneg θ) (by positivity)

def functionCoefficients (θ : ℝ) : SymmetricReal d ι →L[ℝ] Series (AtomIndex d ι) ℝ :=
  (coefficientOperator θ).comp symmetricExpansion

theorem functionCoefficients_bound (θ : ℝ) (a : SymmetricReal d ι) :
    ‖functionCoefficients θ a‖ ≤ polarizationBound (ι := ι) θ * ‖a‖ := by
  calc
    _ = ∑' m, |coefficientOperator θ (symmetricExpansion a) m| := by
      rw [norm_eq_tsum]; rfl
    _ ≤ stencilBound (ι := ι) θ * ‖symmetricExpansion a‖ := coefficientOperator_bound θ _
    _ ≤ stencilBound (ι := ι) θ * ((2 : ℝ) ^ Fintype.card ι * ‖a‖) :=
      mul_le_mul_of_nonneg_left (symmetricExpansion_bound a) (stencilBound_nonneg θ)
    _ = _ := by rw [polarizationBound, mul_assoc]

theorem functionCoefficients_reconstruction [Nonempty ι] (θ : ℝ) (hθ : 0 < θ)
    (a : SymmetricReal d ι) :
    HasSum (fun m => functionCoefficients θ a m • symmetricAtom θ m) a := by
  have hs := synthesis_hasSum (symmetricAtom (d := d) (ι := ι) θ) ((1 + θ) ^ Fintype.card ι)
    (symmetricAtom_bound (d := d) (ι := ι) θ hθ.le) (functionCoefficients θ a)
  have hm := (symmetricInclusion (d := d) (ι := ι)).hasSum hs
  have hraw := coefficientOperator_reconstruction θ hθ (symmetricExpansion a)
  rw [symmetricExpansion_reconstruction] at hraw
  have he : synthesis (symmetricAtom (d := d) (ι := ι) θ) ((1 + θ) ^ Fintype.card ι)
      (symmetricAtom_bound (d := d) (ι := ι) θ hθ.le) (functionCoefficients θ a) = a := by
    apply Subtype.ext
    exact hm.unique hraw
  rwa [he] at hs

local instance atomEncodable : Encodable (AtomIndex d ι) := Encodable.ofCountable _

def naturalAtom (θ : ℝ) (n : ℕ) : SymmetricReal d ι :=
  match Encodable.decode (α := AtomIndex d ι) n with
  | some m => symmetricAtom θ m
  | none => 1

theorem naturalAtom_encode (θ : ℝ) (m : AtomIndex d ι) :
    naturalAtom θ (Encodable.encode m) = symmetricAtom θ m := by
  simp [naturalAtom, Encodable.encodek]

theorem naturalAtom_bound (θ : ℝ) (hθ : 0 ≤ θ) (n : ℕ) :
    ‖naturalAtom (d := d) (ι := ι) θ n‖ ≤ (1 + θ) ^ Fintype.card ι := by
  unfold naturalAtom
  split
  · exact symmetricAtom_bound θ hθ _
  · rw [norm_one]
    exact one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + θ)

theorem naturalAtom_sub_one_bound (θ : ℝ) (hθ : 0 ≤ θ) (n : ℕ) :
    ‖naturalAtom (d := d) (ι := ι) θ n - 1‖ ≤ (1 + θ) ^ Fintype.card ι + 1 := by
  calc
    _ ≤ ‖naturalAtom (d := d) (ι := ι) θ n‖ + ‖(1 : SymmetricReal d ι)‖ := norm_sub_le _ _
    _ ≤ _ := by
      simpa only [norm_one] using
        add_le_add_right (naturalAtom_bound (d := d) (ι := ι) θ hθ n) 1

def naturalCoefficients (θ : ℝ) : SymmetricReal d ι →L[ℝ] Series ℕ ℝ :=
  (regroup (Encodable.encode : AtomIndex d ι → ℕ)).comp (functionCoefficients θ)

theorem naturalCoefficients_bound (θ : ℝ) (a : SymmetricReal d ι) :
    ‖naturalCoefficients θ a‖ ≤ polarizationBound (ι := ι) θ * ‖a‖ :=
  (regroup_bound _ _).trans (functionCoefficients_bound θ a)

theorem naturalCoefficients_reconstruction [Nonempty ι] (θ : ℝ) (hθ : 0 < θ)
    (a : SymmetricReal d ι) :
    HasSum (fun n => naturalCoefficients θ a n • naturalAtom θ n) a := by
  have hs := synthesis_hasSum (naturalAtom (d := d) (ι := ι) θ) ((1 + θ) ^ Fintype.card ι)
    (naturalAtom_bound (d := d) (ι := ι) θ hθ.le) (naturalCoefficients θ a)
  have he := synthesis_regroup (Encodable.encode : AtomIndex d ι → ℕ)
    (naturalAtom (d := d) (ι := ι) θ) ((1 + θ) ^ Fintype.card ι)
    (naturalAtom_bound (d := d) (ι := ι) θ hθ.le)
    (functionCoefficients θ a)
  simp_rw [naturalAtom_encode] at he
  have hr := (functionCoefficients_reconstruction θ hθ a).tsum_eq
  change synthesis (naturalAtom (d := d) (ι := ι) θ) ((1 + θ) ^ Fintype.card ι)
      (naturalAtom_bound (d := d) (ι := ι) θ hθ.le) (naturalCoefficients θ a) = _ at he
  change synthesis (naturalAtom (d := d) (ι := ι) θ) ((1 + θ) ^ Fintype.card ι)
      (naturalAtom_bound (d := d) (ι := ι) θ hθ.le) (naturalCoefficients θ a) =
      ∑' m, functionCoefficients θ a m • symmetricAtom θ m at he
  rw [hr] at he
  rwa [he] at hs

/-- The one-slot density whose Q-fold tensor is the carrier's labeled atom. -/
def naturalDensity (θ : ℝ) (n : ℕ) : Fourier d :=
  match Encodable.decode (α := AtomIndex d ι) n with
  | some m => dictionary θ m
  | none => 1

theorem naturalDensity_integral (θ : ℝ) (n : ℕ) :
    (∫ x : Torus d, toContinuous (naturalDensity (ι := ι) θ n) x) = 1 := by
  unfold naturalDensity
  split
  · exact dictionary_integral θ _
  · simp

theorem naturalDensity_real (θ : ℝ) (n : ℕ) (x : Torus d) :
    (toContinuous (naturalDensity (ι := ι) θ n) x).im = 0 := by
  unfold naturalDensity
  split
  · exact dictionary_real θ _ x
  · simp

theorem naturalDensity_bounds (θ : ℝ) (hθ : 0 ≤ θ) (n : ℕ) (x : Torus d) :
    1 - θ ≤ (toContinuous (naturalDensity (ι := ι) θ n) x).re ∧
      (toContinuous (naturalDensity (ι := ι) θ n) x).re ≤ 1 + θ := by
  unfold naturalDensity
  split
  · exact dictionary_bounds θ hθ _ x
  · simp only [toContinuous_one, ContinuousMap.one_apply, Complex.one_re]
    constructor <;> linarith

theorem naturalDensity_positive (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (n : ℕ) (x : Torus d) : 0 < (toContinuous (naturalDensity (ι := ι) θ n) x).re := by
  have h := (naturalDensity_bounds (ι := ι) θ hθ n x).1
  linarith

theorem naturalDensity_norm (θ : ℝ) (hθ : 0 ≤ θ) (n : ℕ) :
    ‖naturalDensity (d := d) (ι := ι) θ n‖ ≤ 1 + θ := by
  unfold naturalDensity
  split
  · exact dictionary_norm θ hθ _
  · rw [norm_one]; linarith

theorem naturalAtom_factorization (θ : ℝ) (n : ℕ) :
    (naturalAtom (d := d) (ι := ι) θ n : Fourier (ι × d)) =
      tensor (fun _ : ι => naturalDensity (ι := ι) θ n) := by
  unfold naturalAtom naturalDensity
  split
  · rfl
  · apply toContinuous_injective; ext x
    simp [tensor_value]

variable {I : Type*} [Fintype I]

def vectorCoefficients (θ : ℝ) : (I → SymmetricReal d ι) →ₗ[ℝ] (ℕ → I → ℝ) where
  toFun T n i := naturalCoefficients θ (T i) n
  map_add' T U := by
    funext n i
    change naturalCoefficients θ (T i + U i) n = _
    rw [map_add]; rfl
  map_smul' r T := by
    funext n i
    change naturalCoefficients θ (r • T i) n = _
    rw [map_smul]; rfl

theorem vectorCoefficients_point_bound (θ : ℝ) (T : I → SymmetricReal d ι) (n : ℕ) :
    ‖vectorCoefficients θ T n‖ ≤ ∑ i, ‖naturalCoefficients θ (T i) n‖ := by
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)).mpr
  intro i
  exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i)

theorem vectorCoefficients_summable (θ : ℝ) (T : I → SymmetricReal d ι) :
    Summable (fun n => ‖vectorCoefficients θ T n‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (vectorCoefficients_point_bound θ T)
  exact summable_sum (fun i _ => summable_norm (naturalCoefficients θ (T i)))

theorem vectorCoefficients_bound (θ : ℝ) (T : I → SymmetricReal d ι) :
    (∑' n, ‖vectorCoefficients θ T n‖) ≤
      ((Fintype.card I : ℝ) * polarizationBound (ι := ι) θ) * ‖T‖ := by
  calc
    _ ≤ ∑' n, ∑ i, ‖naturalCoefficients θ (T i) n‖ :=
      Summable.tsum_le_tsum (vectorCoefficients_point_bound θ T)
        (vectorCoefficients_summable θ T)
        (summable_sum (fun i _ => summable_norm (naturalCoefficients θ (T i))))
    _ = ∑ i, ‖naturalCoefficients θ (T i)‖ := by
      rw [Summable.tsum_finsetSum (fun i _ => summable_norm (naturalCoefficients θ (T i)))]
      simp only [← norm_eq_tsum]
    _ ≤ ∑ _i : I, polarizationBound (ι := ι) θ * ‖T‖ := by
      apply Finset.sum_le_sum; intro i _
      exact (naturalCoefficients_bound θ (T i)).trans
        (mul_le_mul_of_nonneg_left (norm_le_pi_norm T i) (polarizationBound_nonneg θ))
    _ = _ := by simp [mul_assoc]

/-- An actual instance of the carrier interface on the complete, symmetric,
real Wiener algebra. No polarization or Fourier expansion is assumed. -/
def carrierPolarization [Nonempty ι] (θ : ℝ) (hθ : 0 < θ) :
    CarrierPolarization (SymmetricReal d ι) I 1
      ((Fintype.card I : ℝ) * polarizationBound (ι := ι) θ)
      ((1 + θ) ^ Fintype.card ι + 1) where
  atom := naturalAtom (d := d) (ι := ι) θ
  atom_bound := naturalAtom_sub_one_bound (d := d) (ι := ι) θ hθ.le
  coefficients := vectorCoefficients θ
  summable_norm := vectorCoefficients_summable θ
  norm_bound := vectorCoefficients_bound θ
  reconstruction T i := naturalCoefficients_reconstruction θ hθ (T i)

open Filter
open scoped Topology

/-- The former polarization input has been discharged for the actual Wiener
algebra. Only the ideal-increment estimate and finite moment data remain. -/
theorem eventually_hasPositiveWienerCarrier [Nonempty ι] [DecidableEq I]
    {Γ : Type*} [Fintype Γ]
    (J : ℕ → I → SymmetricReal d ι) (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) (hJ : ∀ n, ‖J n‖ ≤ δ n)
    (feature : I → Γ → ℝ) (μ : FiniteLaw Γ) (hμ : ∀ x, 0 < μ.weight x)
    (R : MomentRightInverse feature) :
    ∀ᶠ n in atTop, HasPositiveCarrier 1 (naturalAtom (d := d) (ι := ι) (1 / 4))
      (multiplicationIncrement (J n)) feature μ := by
  let P := carrierPolarization (d := d) (ι := ι) (I := I) (1 / 4) (by norm_num)
  exact P.eventually_hasPositiveCarrier
    (mul_nonneg (Nat.cast_nonneg _) (polarizationBound_nonneg _))
    (by positivity) (by simp)
    (fun n => multiplicationIncrement (J n)) δ hδ0 hδ
    (fun n D => multiplicationIncrement_bound (J n) (δ n) (hδ0 n) (hJ n) D)
    feature μ hμ R

end CausalLowerbound.PartB.PositiveWiener
