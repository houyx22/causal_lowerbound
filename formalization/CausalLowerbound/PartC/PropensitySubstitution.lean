import CausalLowerbound.PartC.RepresentativeSubstitution
import CausalLowerbound.WienerTensor

/-! The degree-one design-weighted substitution. Selected zero-degree
slots receive a jitter variable; selected degree-one slots are replaced
by their normalized correction. This is an explicit array operation. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartC.Representative

variable {d ι J : Type*} [Fintype d] [Fintype ι] [Fintype J]
  [DecidableEq ι] [DecidableEq J]

def propensityOutputDegree (S : Finset ι) (a : Degree ι 1) : Degree ι 1 :=
  fun i => if i ∈ S then if a i = 0 then 1 else 0 else a i

def propensityCorrection (S : Finset ι) (k : ι → Wiener.Fourier (ι × d))
    (a : Degree ι 1) : Wiener.Fourier (ι × d) :=
  ∏ i, if i ∈ S ∧ a i ≠ 0 then k i else 1

theorem propensityCorrection_norm (S : Finset ι) (k : ι → Wiener.Fourier (ι × d))
    (hk : ∀ i, ‖k i‖ ≤ 1) (a : Degree ι 1) : ‖propensityCorrection S k a‖ ≤ 1 := by
  apply (Finset.norm_prod_le _ _).trans
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro i _
  split_ifs
  · exact hk i
  · exact norm_one.le

theorem propensityCorrection_value (S : Finset ι) (k : ι → Wiener.Fourier (ι × d))
    (a : Degree ι 1) (x : Wiener.Torus (ι × d))
    (hk : ∀ i, (Wiener.toContinuous (k i) x).im = 0) :
    Wiener.toContinuous (propensityCorrection S k a) x =
      ((∏ i, if i ∈ S ∧ a i ≠ 0 then (Wiener.toContinuous (k i) x).re else 1 : ℝ) : ℂ) := by
  rw [propensityCorrection, Wiener.toContinuous_prod, ContinuousMap.prod_apply, Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs
  · exact Complex.ext rfl (by simpa using hk i)
  · simp only [Wiener.toContinuous_one, ContinuousMap.one_apply, Complex.ofReal_one]

def propensitySlotFactor (S : Finset ι) (κ z : ι → ℝ) (a : Degree ι 1) (i : ι) : ℝ :=
  if i ∈ S then if a i = 0 then z i else κ i else z i ^ (a i).val

theorem propensity_monomial_substitution (S : Finset ι) (κ z : ι → ℝ) (a : Degree ι 1) :
    monomial (propensityOutputDegree S a) z * (∏ i, if i ∈ S ∧ a i ≠ 0 then κ i else 1) =
      ∏ i, propensitySlotFactor S κ z a i := by
  rw [monomial, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S
  · by_cases ha : a i = 0
    · simp [propensityOutputDegree, propensitySlotFactor, hi, ha]
    · simp [propensityOutputDegree, propensitySlotFactor, hi, ha]
  · simp [propensityOutputDegree, propensitySlotFactor, hi]

theorem propensityPattern_multiplier_bound (S : Finset ι) (k : ι → Wiener.Fourier (ι × d))
    (hk : ∀ i, ‖k i‖ ≤ 1) (b : Wiener.Fourier (ι × d)) (a : Degree ι 1) :
    ‖b * propensityCorrection S k a‖ ≤ ‖b‖ :=
  (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left (propensityCorrection_norm S k hk a)
    (norm_nonneg b)).trans_eq (mul_one _))

def propensityPattern (S : Finset ι) (k : ι → Wiener.Fourier (ι × d))
    (hk : ∀ i, ‖k i‖ ≤ 1) (b : Wiener.Fourier (ι × d)) : Array d ι J 1 →L[ℝ] Array d ι J 1 :=
  degreeSubstitution (propensityOutputDegree S) (fun a => b * propensityCorrection S k a) ‖b‖
    (propensityPattern_multiplier_bound S k hk b)

theorem propensityPattern_bound (S : Finset ι) (k : ι → Wiener.Fourier (ι × d))
    (hk : ∀ i, ‖k i‖ ≤ 1) (b : Wiener.Fourier (ι × d)) (a : Array d ι J 1) :
    ‖propensityPattern S k hk b a‖ ≤ ‖b‖ * ‖a‖ := degreeSubstitution_bound _ _ _ _ a

theorem propensityPattern_symbol_bound (S : Finset ι) (k : ι → Wiener.Fourier (ι × d))
    (hk : ∀ i, ‖k i‖ ≤ 1) (b : Wiener.Fourier (ι × d)) (a : Array d ι J 1) (j : J) :
    ‖symbolPart j (propensityPattern S k hk b a)‖ ≤ ‖b‖ * ‖symbolPart j a‖ :=
  degreeSubstitution_symbol_bound _ _ _ _ a j

theorem propensityPattern_remove (S : Finset ι) (k : ι → Wiener.Fourier (ι × d))
    (hk : ∀ i, ‖k i‖ ≤ 1) (b : Wiener.Fourier (ι × d)) (a : Array d ι J 1) (U : Finset J) :
    remove U (propensityPattern S k hk b a) = propensityPattern S k hk b (remove U a) :=
  degreeSubstitution_remove _ _ _ _ a U

theorem propensityPattern_value (S : Finset ι) (k : ι → Wiener.Fourier (ι × d))
    (hk : ∀ i, ‖k i‖ ≤ 1) (b : Wiener.Fourier (ι × d)) (a : Array d ι J 1)
    (x : Wiener.Torus (ι × d)) (z : ι → ℝ) (ζ : J → Bool)
    (hbre : (Wiener.toContinuous b x).im = 0)
    (hkre : ∀ i, (Wiener.toContinuous (k i) x).im = 0) :
    pointValue x z ζ (propensityPattern S k hk b a) = (Wiener.toContinuous b x).re *
      ∑ r : Row ι J 1, Walsh.character r.2 ζ * (Wiener.toContinuous (a r) x).re *
        ∏ i, propensitySlotFactor S (fun j => (Wiener.toContinuous (k j) x).re) z r.1 i := by
  have he (e : Degree ι 1) : Wiener.toContinuous (b * propensityCorrection S k e) x =
      (((Wiener.toContinuous b x).re *
        ∏ i, if i ∈ S ∧ e i ≠ 0 then (Wiener.toContinuous (k i) x).re else 1 : ℝ) : ℂ) := by
    rw [Wiener.toContinuous_mul, ContinuousMap.mul_apply, propensityCorrection_value S k e x hkre]
    have hb : Wiener.toContinuous b x = ((Wiener.toContinuous b x).re : ℂ) :=
      Complex.ext rfl (by simpa using hbre)
    rw [hb, Complex.ofReal_mul, Complex.ofReal_re]
  rw [propensityPattern, degreeSubstitution_value _ _ _ _ x z ζ (fun e => by rw [he]; rfl), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [he, Complex.ofReal_re, rowWeight]
  have hm := propensity_monomial_substitution S (fun i => (Wiener.toContinuous (k i) x).re) z r.1
  rw [← hm]
  ring

def propensityTarget (k : ι → Wiener.Fourier (ι × d)) (hk : ∀ i, ‖k i‖ ≤ 1)
    (b : Finset ι → Wiener.Fourier (ι × d)) : Array d ι J 1 →L[ℝ] Array d ι J 1 :=
  ∑ S : Finset ι, propensityPattern S k hk (b S)

theorem propensityTarget_bound (k : ι → Wiener.Fourier (ι × d)) (hk : ∀ i, ‖k i‖ ≤ 1)
    (b : Finset ι → Wiener.Fourier (ι × d)) (a : Array d ι J 1) :
    ‖propensityTarget k hk b a‖ ≤ (∑ S, ‖b S‖) * ‖a‖ := by
  simp only [propensityTarget, ContinuousLinearMap.sum_apply]
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun S _ => propensityPattern_bound S k hk (b S) a)).trans_eq
    (Finset.sum_mul _ _ _).symm)

end CausalLowerbound.PartC.Representative
