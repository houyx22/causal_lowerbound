import CausalLowerbound.PartB.PhysicalDesign

/-! Global designs from uniformly bounded carrier charts. The overlap bound
depends only on the dimension, and permits a shared sign configuration in
all charts. No independence of the carrier densities is required. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal Classical
open MeasureTheory

namespace CausalLowerbound.PartC
open PartB.ShellGeometry
variable {d : Type*} [Fintype d] [DecidableEq d] {θ : ℝ}

structure CarrierProfile (d : Type*) [Fintype d] (θ : ℝ) where
  density : (d → ℤ) → (d → ℝ) → ℝ
  measurable : ∀ k, Measurable (density k)
  bounds : ∀ k u, 1 - θ ≤ density k u ∧ density k u ≤ 1 + θ

namespace CarrierProfile

def factor (F : CarrierProfile d θ) (x₀ : d → ℝ) (r : ℝ)
    (k : d → ℤ) (x : d → ℝ) : ℝ :=
  if x ∈ carrierBox x₀ r k then
    F.density k (carrierCoordinate (localCoordinate x₀ r k x)) else 1

theorem factor_measurable (F : CarrierProfile d θ) (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ) :
    Measurable (F.factor x₀ r k) := by
  apply Measurable.ite (carrierBox_measurable x₀ r k) _ measurable_const
  exact (F.measurable k).comp
    (carrierCoordinate_smooth.continuous.comp (localCoordinate_continuous x₀ r k)).measurable

theorem factor_bounds (F : CarrierProfile d θ) (hθ : 0 ≤ θ) (x₀ : d → ℝ)
    (r : ℝ) (k : d → ℤ) (x : d → ℝ) :
    1 - θ ≤ F.factor x₀ r k x ∧ F.factor x₀ r k x ≤ 1 + θ := by
  unfold factor
  split
  · exact F.bounds k _
  · constructor <;> linarith

def product (F : CarrierProfile d θ) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (r : ℝ) (x : d → ℝ) : ℝ :=
  ∏ k ∈ S, F.factor x₀ r k x

theorem product_measurable (F : CarrierProfile d θ) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (r : ℝ) : Measurable (F.product S x₀ r) :=
  Finset.measurable_prod _ (fun k _ => F.factor_measurable x₀ r k)

theorem product_bounds (F : CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (x : d → ℝ) :
    (1 - θ) ^ (5 ^ Fintype.card d) ≤ F.product S x₀ r x ∧
      F.product S x₀ r x ≤ (1 + θ) ^ (5 ^ Fintype.card d) := by
  let T := S ∩ carrierNeighbors (fun i => (x i - x₀ i) / r)
  have hcard : T.card ≤ 5 ^ Fintype.card d :=
    (Finset.card_le_card Finset.inter_subset_right).trans_eq (carrierNeighbors_card _)
  have he : F.product S x₀ r x = ∏ k ∈ T, F.factor x₀ r k x := by
    symm
    apply Finset.prod_subset Finset.inter_subset_left
    intro k hk hkT
    have hn : x ∉ carrierBox x₀ r k := fun hx =>
      hkT (Finset.mem_inter.mpr ⟨hk, carrierBox_overlap _ _ _ _ hx⟩)
    simp only [factor, if_neg hn]
  rw [he]
  have hlo : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1.le
  constructor
  · calc
      _ ≤ (1 - θ) ^ T.card := pow_le_pow_of_le_one hlo (by linarith) hcard
      _ = ∏ _k ∈ T, (1 - θ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => hlo)
        (fun k _ => (F.factor_bounds hθ x₀ r k x).1)
  · calc
      _ ≤ ∏ _k ∈ T, (1 + θ) := Finset.prod_le_prod
        (fun k _ => hlo.trans (F.factor_bounds hθ x₀ r k x).1)
        (fun k _ => (F.factor_bounds hθ x₀ r k x).2)
      _ = (1 + θ) ^ T.card := by simp
      _ ≤ _ := pow_le_pow_right₀ (by linarith) hcard

def normalizer (F : CarrierProfile d θ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) : ℝ :=
  ∫ x, F.product S x₀ r x ∂cubeMeasure d

def normalized (F : CarrierProfile d θ) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (r : ℝ) (x : d → ℝ) : ℝ :=
  F.product S x₀ r x / F.normalizer S x₀ r

theorem product_integrable (F : CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) :
    Integrable (F.product S x₀ r) (cubeMeasure d) := by
  refine ⟨(F.product_measurable S x₀ r).aestronglyMeasurable,
    hasFiniteIntegral_of_bounded (C := (1 + θ) ^ (5 ^ Fintype.card d)) (ae_of_all _ ?_)⟩
  intro x
  have hb := F.product_bounds hθ hθ1 S x₀ r x
  rw [Real.norm_eq_abs, abs_of_nonneg ((pow_nonneg (sub_nonneg.mpr hθ1.le) _).trans hb.1)]
  exact hb.2

theorem normalizer_bounds (F : CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) :
    (1 - θ) ^ (5 ^ Fintype.card d) ≤ F.normalizer S x₀ r ∧
      F.normalizer S x₀ r ≤ (1 + θ) ^ (5 ^ Fintype.card d) := by
  have hi := F.product_integrable hθ hθ1 S x₀ r
  constructor
  · simpa only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using
      integral_mono (integrable_const ((1 - θ) ^ (5 ^ Fintype.card d))) hi
        (fun x => (F.product_bounds hθ hθ1 S x₀ r x).1)
  · simpa only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using
      integral_mono hi (integrable_const ((1 + θ) ^ (5 ^ Fintype.card d)))
        (fun x => (F.product_bounds hθ hθ1 S x₀ r x).2)

theorem normalized_legal (F : CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) :
    Measurable (F.normalized S x₀ r) ∧
    (∫ x, F.normalized S x₀ r x ∂cubeMeasure d) = 1 ∧
    ∀ x, (1 - θ) ^ (5 ^ Fintype.card d) / (1 + θ) ^ (5 ^ Fintype.card d) ≤ F.normalized S x₀ r x ∧
      F.normalized S x₀ r x ≤ (1 + θ) ^ (5 ^ Fintype.card d) / (1 - θ) ^ (5 ^ Fintype.card d) := by
  have hz := F.normalizer_bounds hθ hθ1 S x₀ r
  have hl : 0 < (1 - θ) ^ (5 ^ Fintype.card d) := pow_pos (sub_pos.mpr hθ1) _
  have hZ : 0 < F.normalizer S x₀ r := hl.trans_le hz.1
  refine ⟨(F.product_measurable S x₀ r).div_const _, ?_, ?_⟩
  · simp only [normalized, integral_div]
    exact div_self hZ.ne'
  · intro x
    have hx := F.product_bounds hθ hθ1 S x₀ r x
    exact ⟨div_le_div₀ (hl.le.trans hx.1) hx.1 hZ hz.2,
      div_le_div₀ (by positivity) hx.2 hl hz.1⟩

theorem normalized_nonneg (F : CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (x : d → ℝ) :
    0 ≤ F.normalized S x₀ r x :=
  (div_nonneg (pow_nonneg (sub_nonneg.mpr hθ1.le) _) (by positivity)).trans
    ((F.normalized_legal hθ hθ1 S x₀ r).2.2 x).1

def measure (F : CarrierProfile d θ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) : Measure (d → ℝ) :=
  (cubeMeasure d).withDensity (fun x => ENNReal.ofReal (F.normalized S x₀ r x))

theorem measure_probability (F : CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) : IsProbabilityMeasure (F.measure S x₀ r) := by
  have hi : Integrable (F.normalized S x₀ r) (cubeMeasure d) :=
    (F.product_integrable hθ hθ1 S x₀ r).div_const _
  constructor
  rw [measure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (F.normalized_nonneg hθ hθ1 S x₀ r)),
    (F.normalized_legal hθ hθ1 S x₀ r).2.1, ENNReal.ofReal_one]

def sampleMeasure (F : CarrierProfile d θ) (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (r : ℝ) (n : ℕ) : Measure (Fin n → d → ℝ) :=
  Measure.pi (fun _ : Fin n => F.measure S x₀ r)

theorem sampleMeasure_probability (F : CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (n : ℕ) :
    IsProbabilityMeasure (F.sampleMeasure S x₀ r n) := by
  letI := F.measure_probability hθ hθ1 S x₀ r
  exact inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Fin n => F.measure S x₀ r)))

end CarrierProfile
end CausalLowerbound.PartC
