import CausalLowerbound.PartC.RepresentativeArray

/-! Contractive real evaluation of normalized representatives. The rough
variables are supplied separately from the Fourier chart; consequently this
evaluation needs no Wiener norm estimate on an individual rough packet. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal

namespace CausalLowerbound.PartC.Representative

variable {d ι J : Type*} [Fintype d] [Fintype ι] [Fintype J]
  [DecidableEq ι] [DecidableEq J] {D : ℕ}

def monomial (e : Degree ι D) (z : ι → ℝ) : ℝ := ∏ i, z i ^ (e i).val

theorem monomial_abs_le_one (e : Degree ι D) (z : ι → ℝ) (hz : ∀ i, |z i| ≤ 1) :
    |monomial e z| ≤ 1 := by
  simp only [monomial, Finset.abs_prod, abs_pow]
  exact Finset.prod_le_one (fun _ _ => by positivity)
    (fun i _ => pow_le_one₀ (abs_nonneg _) (hz i))

def rowWeight (r : Row ι J D) (z : ι → ℝ) (ζ : J → Bool) : ℝ :=
  monomial r.1 z * Walsh.character r.2 ζ

theorem rowWeight_abs_le_one (r : Row ι J D) (z : ι → ℝ) (hz : ∀ i, |z i| ≤ 1)
    (ζ : J → Bool) : |rowWeight r z ζ| ≤ 1 := by
  simpa only [rowWeight, abs_mul, Walsh.abs_character, mul_one] using monomial_abs_le_one r.1 z hz

def pointValue (x : Wiener.Torus (ι × d)) (z : ι → ℝ) (ζ : J → Bool)
    (a : Array d ι J D) : ℝ := ∑ r, rowWeight r z ζ * (Wiener.toContinuous (a r) x).re

@[simp] theorem pointValue_zero (x : Wiener.Torus (ι × d)) (z : ι → ℝ) (ζ : J → Bool) :
    pointValue x z ζ (0 : Array d ι J D) = 0 := by
  simp [pointValue]

theorem pointValue_add (x : Wiener.Torus (ι × d)) (z : ι → ℝ) (ζ : J → Bool)
    (a b : Array d ι J D) : pointValue x z ζ (a + b) = pointValue x z ζ a + pointValue x z ζ b := by
  simp only [pointValue, lp.coeFn_add, Pi.add_apply, map_add, ContinuousMap.add_apply,
    Complex.add_re, mul_add, Finset.sum_add_distrib]

theorem pointValue_sum {A : Type*} (s : Finset A) (f : A → Array d ι J D)
    (x : Wiener.Torus (ι × d)) (z : ι → ℝ) (ζ : J → Bool) :
    pointValue x z ζ (∑ i ∈ s, f i) = ∑ i ∈ s, pointValue x z ζ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, pointValue_add, ih]

theorem pointValue_smul (x : Wiener.Torus (ι × d)) (z : ι → ℝ) (ζ : J → Bool)
    (c : ℝ) (a : Array d ι J D) : pointValue x z ζ (c • a) = c • pointValue x z ζ a := by
  simp only [pointValue, lp.coeFn_smul, Pi.smul_apply, Wiener.toContinuous_real_smul,
    ContinuousMap.smul_apply, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem pointValue_bound (x : Wiener.Torus (ι × d)) (z : ι → ℝ) (hz : ∀ i, |z i| ≤ 1)
    (ζ : J → Bool) (a : Array d ι J D) : |pointValue x z ζ a| ≤ ‖a‖ := by
  calc
    _ ≤ ∑ r, |rowWeight r z ζ * (Wiener.toContinuous (a r) x).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r, ‖a r‖ := by
      apply Finset.sum_le_sum
      intro r _
      rw [abs_mul]
      calc
        _ ≤ 1 * |(Wiener.toContinuous (a r) x).re| :=
          mul_le_mul_of_nonneg_right (rowWeight_abs_le_one r z hz ζ) (abs_nonneg _)
        _ ≤ ‖a r‖ := by
          rw [one_mul]
          exact (Complex.abs_re_le_norm _).trans (Wiener.evaluate_bound _ _)
    _ = ‖a‖ := (norm_eq_sum a).symm

def pointEvaluation (x : Wiener.Torus (ι × d)) (z : ι → ℝ) (hz : ∀ i, |z i| ≤ 1)
    (ζ : J → Bool) : Array d ι J D →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := pointValue x z ζ
      map_add' := pointValue_add x z ζ
      map_smul' := pointValue_smul x z ζ }
    1 (fun a => by simpa only [one_mul] using pointValue_bound x z hz ζ a)

@[simp] theorem pointEvaluation_apply (x : Wiener.Torus (ι × d)) (z : ι → ℝ)
    (hz : ∀ i, |z i| ≤ 1) (ζ : J → Bool) (a : Array d ι J D) :
    pointEvaluation x z hz ζ a = pointValue x z ζ a := rfl

theorem pointValue_single (x : Wiener.Torus (ι × d)) (z : ι → ℝ) (ζ : J → Bool)
    (r : Row ι J D) (a : Wiener.Fourier (ι × d)) :
    pointValue x z ζ (lp.single 1 r a) = rowWeight r z ζ * (Wiener.toContinuous a x).re := by
  unfold pointValue
  rw [Finset.sum_eq_single r]
  · rw [lp.single_apply_self]
  · intro s _ hsr
    rw [lp.single_apply_ne _ _ _ hsr, map_zero]
    simp
  · simp

@[simp] theorem pointValue_unit (x : Wiener.Torus (ι × d)) (z : ι → ℝ) (ζ : J → Bool) :
    pointValue x z ζ (unit : Array d ι J D) = 1 := by
  rw [unit, pointValue_single]
  simp [rowWeight, zeroRow, monomial, Wiener.toContinuous_one]

theorem continuous_pointValue {K : Type*} [TopologicalSpace K]
    (x : K → Wiener.Torus (ι × d)) (hx : Continuous x) (z : ι → K → ℝ)
    (hz : ∀ i, Continuous (z i)) (ζ : J → Bool) (a : Array d ι J D) :
    Continuous (fun u => pointValue (x u) (fun i => z i u) ζ a) := by
  apply continuous_finset_sum
  intro r _
  have hm : Continuous (fun u => monomial r.1 (fun i => z i u)) :=
    continuous_finset_prod _ (fun i _ => (hz i).pow _)
  exact (hm.mul continuous_const).mul
    (Complex.continuous_re.comp ((Wiener.toContinuous (a r)).continuous.comp hx))

def chartEvaluation {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (x : K → Wiener.Torus (ι × d)) (hx : Continuous x) (z : ι → K → ℝ)
    (hz : ∀ i, Continuous (z i)) (hb : ∀ i u, |z i u| ≤ 1) (ζ : J → Bool) :
    Array d ι J D →L[ℝ] C(K, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun a => ⟨fun u => pointValue (x u) (fun i => z i u) ζ a,
        continuous_pointValue x hx z hz ζ a⟩
      map_add' := by intro a b; ext u; exact pointValue_add _ _ _ a b
      map_smul' := by intro c a; ext u; exact pointValue_smul _ _ _ c a }
    1 (fun a => (ContinuousMap.norm_le _ (by positivity)).mpr (fun u => by
      simpa only [one_mul] using pointValue_bound (x u) (fun i => z i u) (fun i => hb i u) ζ a))

@[simp] theorem chartEvaluation_apply {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (x : K → Wiener.Torus (ι × d)) (hx : Continuous x) (z : ι → K → ℝ)
    (hz : ∀ i, Continuous (z i)) (hb : ∀ i u, |z i u| ≤ 1) (ζ : J → Bool)
    (a : Array d ι J D) (u : K) : chartEvaluation x hx z hz hb ζ a u =
      pointValue (x u) (fun i => z i u) ζ a := rfl

theorem chartEvaluation_bound {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (x : K → Wiener.Torus (ι × d)) (hx : Continuous x) (z : ι → K → ℝ)
    (hz : ∀ i, Continuous (z i)) (hb : ∀ i u, |z i u| ≤ 1) (ζ : J → Bool)
    (a : Array d ι J D) : ‖chartEvaluation x hx z hz hb ζ a‖ ≤ ‖a‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg a)).mpr (fun u => pointValue_bound _ _ (fun i => hb i u) ζ a)

end CausalLowerbound.PartC.Representative
