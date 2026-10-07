import CausalLowerbound.PartC.RepresentativeSubstitution
import CausalLowerbound.PartC.SingleSiteBridge
import CausalLowerbound.WienerTensor

/-! The degree-three design-weighted substitution. At every selected
slot the input degree is averaged using the first three rough moments,
and the output degree is the selected Taylor degree. The operation acts
on the full coefficient array and preserves its Walsh projections. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace CausalLowerbound.PartC.Representative
variable {d ι J Ω : Type*} [Fintype d] [Fintype ι] [Fintype J]
  [DecidableEq ι] [DecidableEq J] [Fintype Ω]

def outcomeMoment (v : ℝ) (f : Fin 4) : ℝ :=
  if f = 0 then 1 else if f = 2 then v else 0

theorem outcomeMoment_eq_expect (μ : FiniteLaw Ω) (X : Ω → ℝ) (v : ℝ)
    (hmean : μ.expect X = 0) (hvar : μ.expect (fun ω => X ω ^ 2) = v)
    (hthird : μ.expect (fun ω => X ω ^ 3) = 0) (f : Fin 4) :
    outcomeMoment v f = μ.expect (fun ω => X ω ^ f.val) := by
  fin_cases f <;> simp [outcomeMoment, hmean, hvar, hthird, FiniteLaw.expect_const]

def outcomeMomentFourier (k : Wiener.Fourier (ι × d)) (f : Fin 4) : Wiener.Fourier (ι × d) :=
  if f = 0 then 1 else if f = 2 then k else 0

theorem outcomeMomentFourier_norm (k : Wiener.Fourier (ι × d)) (K : ℝ)
    (hK : 1 ≤ K) (hk : ‖k‖ ≤ K) (f : Fin 4) : ‖outcomeMomentFourier k f‖ ≤ K := by
  unfold outcomeMomentFourier
  split_ifs
  · simpa only [norm_one] using hK
  · exact hk
  · simpa only [norm_zero] using zero_le_one.trans hK

theorem outcomeMomentFourier_value (k : Wiener.Fourier (ι × d)) (f : Fin 4)
    (x : Wiener.Torus (ι × d)) (hk : (Wiener.toContinuous k x).im = 0) :
    Wiener.toContinuous (outcomeMomentFourier k f) x =
      (outcomeMoment (Wiener.toContinuous k x).re f : ℂ) := by
  unfold outcomeMomentFourier outcomeMoment
  split_ifs
  · simp only [Wiener.toContinuous_one, ContinuousMap.one_apply, Complex.ofReal_one]
  · exact Complex.ext rfl (by simpa using hk)
  · simp only [map_zero, ContinuousMap.zero_apply, Complex.ofReal_zero]

def outcomeOutputDegree (e a : Degree ι 3) : Degree ι 3 :=
  fun i => if e i = 0 then a i else e i

def outcomeCorrection (e : Degree ι 3) (k : ι → Wiener.Fourier (ι × d))
    (a : Degree ι 3) : Wiener.Fourier (ι × d) :=
  ∏ i, if e i = 0 then 1 else outcomeMomentFourier (k i) (a i)

theorem outcomeCorrection_norm (e : Degree ι 3) (k : ι → Wiener.Fourier (ι × d))
    (K : ℝ) (hK : 1 ≤ K) (hk : ∀ i, ‖k i‖ ≤ K) (a : Degree ι 3) :
    ‖outcomeCorrection e k a‖ ≤ K ^ Fintype.card ι := by
  apply (Finset.norm_prod_le _ _).trans
  calc
    _ ≤ ∏ _i : ι, K := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro i _
      split_ifs
      · simpa only [norm_one] using hK
      · exact outcomeMomentFourier_norm (k i) K hK (hk i) (a i)
    _ = _ := by simp

theorem outcomeCorrection_value (e : Degree ι 3) (k : ι → Wiener.Fourier (ι × d))
    (a : Degree ι 3) (x : Wiener.Torus (ι × d)) (hk : ∀ i, (Wiener.toContinuous (k i) x).im = 0) :
    Wiener.toContinuous (outcomeCorrection e k a) x =
      ((∏ i, if e i = 0 then 1 else outcomeMoment (Wiener.toContinuous (k i) x).re (a i) : ℝ) : ℂ) := by
  rw [outcomeCorrection, Wiener.toContinuous_prod, ContinuousMap.prod_apply, Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs
  · simp only [Wiener.toContinuous_one, ContinuousMap.one_apply, Complex.ofReal_one]
  · exact outcomeMomentFourier_value (k i) (a i) x (hk i)

def outcomeSlotFactor (e : Degree ι 3) (v z : ι → ℝ) (a : Degree ι 3) (i : ι) : ℝ :=
  if e i = 0 then z i ^ (a i).val else outcomeMoment (v i) (a i) * z i ^ (e i).val

theorem outcome_monomial_substitution (e : Degree ι 3) (v z : ι → ℝ) (a : Degree ι 3) :
    monomial (outcomeOutputDegree e a) z *
      (∏ i, if e i = 0 then 1 else outcomeMoment (v i) (a i)) = ∏ i, outcomeSlotFactor e v z a i := by
  rw [monomial, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases he : e i = 0
  · simp only [outcomeOutputDegree, outcomeSlotFactor, he, if_true, mul_one]
  · simp only [outcomeOutputDegree, outcomeSlotFactor, he, if_false]
    ring

theorem outcomePattern_multiplier_bound (e : Degree ι 3) (k : ι → Wiener.Fourier (ι × d))
    (K : ℝ) (hK : 1 ≤ K) (hk : ∀ i, ‖k i‖ ≤ K) (b : Wiener.Fourier (ι × d)) (a : Degree ι 3) :
    ‖b * outcomeCorrection e k a‖ ≤ ‖b‖ * K ^ Fintype.card ι :=
  (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (outcomeCorrection_norm e k K hK hk a) (norm_nonneg b))

def outcomePattern (e : Degree ι 3) (k : ι → Wiener.Fourier (ι × d))
    (K : ℝ) (hK : 1 ≤ K) (hk : ∀ i, ‖k i‖ ≤ K) (b : Wiener.Fourier (ι × d)) :
    Array d ι J 3 →L[ℝ] Array d ι J 3 :=
  degreeSubstitution (outcomeOutputDegree e) (fun a => b * outcomeCorrection e k a)
    (‖b‖ * K ^ Fintype.card ι) (outcomePattern_multiplier_bound e k K hK hk b)

theorem outcomePattern_bound (e : Degree ι 3) (k : ι → Wiener.Fourier (ι × d))
    (K : ℝ) (hK : 1 ≤ K) (hk : ∀ i, ‖k i‖ ≤ K) (b : Wiener.Fourier (ι × d)) (a : Array d ι J 3) :
    ‖outcomePattern e k K hK hk b a‖ ≤ (‖b‖ * K ^ Fintype.card ι) * ‖a‖ :=
  degreeSubstitution_bound _ _ _ _ a

theorem outcomePattern_symbol_bound (e : Degree ι 3) (k : ι → Wiener.Fourier (ι × d))
    (K : ℝ) (hK : 1 ≤ K) (hk : ∀ i, ‖k i‖ ≤ K) (b : Wiener.Fourier (ι × d))
    (a : Array d ι J 3) (j : J) :
    ‖symbolPart j (outcomePattern e k K hK hk b a)‖ ≤ (‖b‖ * K ^ Fintype.card ι) * ‖symbolPart j a‖ :=
  degreeSubstitution_symbol_bound _ _ _ _ a j

theorem outcomePattern_remove (e : Degree ι 3) (k : ι → Wiener.Fourier (ι × d))
    (K : ℝ) (hK : 1 ≤ K) (hk : ∀ i, ‖k i‖ ≤ K) (b : Wiener.Fourier (ι × d))
    (a : Array d ι J 3) (U : Finset J) :
    remove U (outcomePattern e k K hK hk b a) = outcomePattern e k K hK hk b (remove U a) :=
  degreeSubstitution_remove _ _ _ _ a U

theorem outcomePattern_value (e : Degree ι 3) (k : ι → Wiener.Fourier (ι × d))
    (K : ℝ) (hK : 1 ≤ K) (hk : ∀ i, ‖k i‖ ≤ K) (b : Wiener.Fourier (ι × d))
    (a : Array d ι J 3) (x : Wiener.Torus (ι × d)) (z : ι → ℝ) (ζ : J → Bool)
    (hbre : (Wiener.toContinuous b x).im = 0)
    (hkre : ∀ i, (Wiener.toContinuous (k i) x).im = 0) :
    pointValue x z ζ (outcomePattern e k K hK hk b a) = (Wiener.toContinuous b x).re *
      ∑ r : Row ι J 3, Walsh.character r.2 ζ * (Wiener.toContinuous (a r) x).re *
        ∏ i, outcomeSlotFactor e (fun j => (Wiener.toContinuous (k j) x).re) z r.1 i := by
  have he (f : Degree ι 3) : Wiener.toContinuous (b * outcomeCorrection e k f) x =
      (((Wiener.toContinuous b x).re *
        ∏ i, if e i = 0 then 1 else outcomeMoment (Wiener.toContinuous (k i) x).re (f i) : ℝ) : ℂ) := by
    rw [Wiener.toContinuous_mul, ContinuousMap.mul_apply, outcomeCorrection_value e k f x hkre]
    have hb : Wiener.toContinuous b x = ((Wiener.toContinuous b x).re : ℂ) :=
      Complex.ext rfl (by simpa using hbre)
    rw [hb, Complex.ofReal_mul, Complex.ofReal_re]
  rw [outcomePattern, degreeSubstitution_value _ _ _ _ x z ζ (fun f => by rw [he]; rfl), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [he, Complex.ofReal_re, rowWeight]
  rw [← outcome_monomial_substitution e (fun i => (Wiener.toContinuous (k i) x).re) z r.1]
  ring

end CausalLowerbound.PartC.Representative
