import CausalLowerbound.PartC.ModelComparison
import CausalLowerbound.PartC.MixedObservationLocality
import CausalLowerbound.PartB.PhysicalFiniteExperiment

/-! Normalize a finite collection of observations by its actual design
likelihood. Labels, signs, and coefficients are tilted jointly; the common
denominator depends only on the carrier law, not the coefficient kernel. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d I K J Ω : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]
  [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J] [Fintype Ω]
  {θ : ℝ} {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}

theorem CarrierProfile.observation_product_bounds (F : CarrierProfile d θ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (x : I → d → ℝ) :
    ((1 - θ) ^ (5 ^ Fintype.card d)) ^ Fintype.card I ≤ ∏ i, F.product S x₀ r (x i) ∧
      (∏ i, F.product S x₀ r (x i)) ≤ ((1 + θ) ^ (5 ^ Fintype.card d)) ^ Fintype.card I := by
  have hlo : 0 ≤ (1 - θ) ^ (5 ^ Fintype.card d) := pow_nonneg (sub_nonneg.mpr hθ1.le) _
  constructor
  · calc
      _ = ∏ _i : I, (1 - θ) ^ (5 ^ Fintype.card d) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => hlo) (fun i _ => (F.product_bounds hθ hθ1 S x₀ r (x i)).1)
  · calc
      _ ≤ ∏ _i : I, (1 + θ) ^ (5 ^ Fintype.card d) := Finset.prod_le_prod
        (fun i _ => hlo.trans (F.product_bounds hθ hθ1 S x₀ r (x i)).1)
        (fun i _ => (F.product_bounds hθ hθ1 S x₀ r (x i)).2)
      _ = _ := by simp

def rawCarrierDesignMarginal
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (H : K → DiscreteLaw ℕ)
    (x : I → d → ℝ) : ℝ :=
  (sharedSignPrior H).expect (fun z => ∏ i, (F z).product S x₀ r (x i))

theorem rawCarrierDesignMarginal_bounds
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (H : K → DiscreteLaw ℕ) (x : I → d → ℝ) :
    ((1 - θ) ^ (5 ^ Fintype.card d)) ^ Fintype.card I ≤ rawCarrierDesignMarginal F S x₀ r H x ∧
      rawCarrierDesignMarginal F S x₀ r H x ≤ ((1 + θ) ^ (5 ^ Fintype.card d)) ^ Fintype.card I :=
  (sharedSignPrior H).expect_bounds _ _ _ (pow_nonneg (pow_nonneg (sub_nonneg.mpr hθ1.le) _) _)
    (fun z => (F z).observation_product_bounds hθ hθ1 S x₀ r x)

def rawCarrierConditional
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (H : K → DiscreteLaw ℕ) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω)
    (fields : (((K → ℕ) × (J → Bool)) × (K → Ω)) → NuisanceFields d)
    (hlegal : ∀ z, (fields z).Legal α β γ Lπ L₀ Lτ κ) (hκ : 0 ≤ κ)
    (x : I → d → ℝ) : FiniteLaw (I → Bool × Bool) :=
  ((signBlockPrior H kernel).tilt (fun z => ∏ i, (F z.1).product S x₀ r (x i))
    (((1 - θ) ^ (5 ^ Fintype.card d)) ^ Fintype.card I)
    (((1 + θ) ^ (5 ^ Fintype.card d)) ^ Fintype.card I)
    (pow_pos (pow_pos (sub_pos.mpr hθ1) _) _)
    (fun z => (F z.1).observation_product_bounds hθ hθ1 S x₀ r x)).mixFinite
      (fun z => FiniteLaw.independent (fun i => (fields z).conditionalLaw (hlegal z) hκ (x i)))

theorem rawCarrierConditional_weight
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (H : K → DiscreteLaw ℕ) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω)
    (fields : (((K → ℕ) × (J → Bool)) × (K → Ω)) → NuisanceFields d)
    (hlegal : ∀ z, (fields z).Legal α β γ Lπ L₀ Lτ κ) (hκ : 0 ≤ κ)
    (x : I → d → ℝ) (y : I → Bool × Bool) :
    (rawCarrierConditional F hθ hθ1 S x₀ r H kernel fields hlegal hκ x).weight y =
      (signBlockPrior H kernel).expect (fun z => ∏ i,
        (F z.1).product S x₀ r (x i) * nuisanceCellMass (fields z) (x i) (y i)) /
          rawCarrierDesignMarginal F S x₀ r H x := by
  have hb (z : (K → ℕ) × (J → Bool)) :
      |∏ i, (F z).product S x₀ r (x i)| ≤ ((1 + θ) ^ (5 ^ Fintype.card d)) ^ Fintype.card I := by
    have he := (F z).observation_product_bounds hθ hθ1 S x₀ r x
    rw [abs_of_nonneg ((pow_nonneg (pow_nonneg (sub_nonneg.mpr hθ1.le) _) _).trans he.1)]
    exact he.2
  have hd := DiscreteLaw.joint_expect_label (sharedSignPrior H) (signBlockKernel kernel)
    (fun z => ∏ i, (F z).product S x₀ r (x i)) _ hb
  change (signBlockPrior H kernel).expect (fun z => ∏ i, (F z.1).product S x₀ r (x i)) =
    rawCarrierDesignMarginal F S x₀ r H x at hd
  dsimp only [rawCarrierConditional, DiscreteLaw.mixFinite]
  rw [DiscreteLaw.tilt_expect, hd]
  simp only [FiniteLaw.independent, Finset.prod_mul_distrib]
  change (rawCarrierDesignMarginal F S x₀ r H x)⁻¹ *
    (signBlockPrior H kernel).expect (fun z => (∏ i, (F z.1).product S x₀ r (x i)) *
      ∏ i, nuisanceCellMass (fields z) (x i) (y i)) = _
  ring

theorem rawCarrierConditional_lower
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (H : K → DiscreteLaw ℕ) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω)
    (fields : (((K → ℕ) × (J → Bool)) × (K → Ω)) → NuisanceFields d)
    (hlegal : ∀ z, (fields z).Legal α β γ Lπ L₀ Lτ κ) (hκ : 0 ≤ κ)
    (x : I → d → ℝ) (y : I → Bool × Bool) :
    (κ ^ 2) ^ Fintype.card I ≤ (rawCarrierConditional F hθ hθ1 S x₀ r H kernel fields hlegal hκ x).weight y := by
  unfold rawCarrierConditional DiscreteLaw.mixFinite
  apply (DiscreteLaw.expect_bounds _ _ ((κ ^ 2) ^ Fintype.card I) 1 (by positivity) _).1
  intro z
  constructor
  · change (κ ^ 2) ^ Fintype.card I ≤ ∏ i, _
    calc
      _ = ∏ _i : I, κ ^ 2 := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => sq_nonneg κ)
        (fun i _ => (fields z).conditionalLaw_lower (hlegal z) hκ (x i) (y i))
  · exact FiniteLaw.weight_le_one _ _

theorem rawCarrierConditional_eq_model
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (H : K → DiscreteLaw ℕ) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω)
    {lower upper : ℝ} (n : ℕ)
    (M : (((K → ℕ) × (J → Bool)) × (K → Ω)) → StatisticalModel d α β γ Lπ L₀ Lτ κ lower upper)
    (hκ : 0 ≤ κ) (x : Fin n → d → ℝ) :
    rawCarrierConditional (I := Fin n) F hθ hθ1 S x₀ r H kernel (fun z => (M z).fields) (fun z => (M z).legal.1) hκ x =
      carrierModelConditional F hθ hθ1 S x₀ r H kernel n M hκ x := by
  apply FiniteLaw.ext
  intro y
  rw [rawCarrierConditional_weight, carrierModelConditional_raw_weight]
  simp only [StatisticalModel.sampleConditional, FiniteLaw.independent, Finset.prod_mul_distrib]
  rfl

theorem rawCarrierConditional_hellinger_of_raw_bound
    (F : ((K → ℕ) × (J → Bool)) → CarrierProfile d θ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (H : K → DiscreteLaw ℕ) (kernel : Bool → K → (J → Bool) → ℕ → FiniteLaw Ω)
    (fields : Bool → (((K → ℕ) × (J → Bool)) × (K → Ω)) → NuisanceFields d)
    (hlegal : ∀ side z, (fields side z).Legal α β γ Lπ L₀ Lτ κ) (hκ : 0 < κ)
    (x : I → d → ℝ) (E : ℝ)
    (hraw : ∀ y : I → Bool × Bool,
      |(signBlockPrior H (kernel false)).expect (fun z => ∏ i,
          (F z.1).product S x₀ r (x i) * nuisanceCellMass (fields false z) (x i) (y i)) -
        (signBlockPrior H (kernel true)).expect (fun z => ∏ i,
          (F z.1).product S x₀ r (x i) * nuisanceCellMass (fields true z) (x i) (y i))| ≤ E) :
    (rawCarrierConditional F hθ hθ1 S x₀ r H (kernel false) (fields false) (hlegal false) hκ.le x).hellingerSq
      (rawCarrierConditional F hθ hθ1 S x₀ r H (kernel true) (fields true) (hlegal true) hκ.le x) ≤
      (Fintype.card (I → Bool × Bool) : ℝ) *
        (E / ((1 - θ) ^ (5 ^ Fintype.card d)) ^ Fintype.card I) ^ 2 / (κ ^ 2) ^ Fintype.card I := by
  let P := fun side => rawCarrierConditional F hθ hθ1 S x₀ r H (kernel side) (fields side) (hlegal side) hκ.le x
  let D := rawCarrierDesignMarginal F S x₀ r H x
  let L := ((1 - θ) ^ (5 ^ Fintype.card d)) ^ Fintype.card I
  have hL : 0 < L := pow_pos (pow_pos (sub_pos.mpr hθ1) _) _
  have hLD : L ≤ D := (rawCarrierDesignMarginal_bounds F hθ hθ1 S x₀ r H x).1
  have hD : 0 < D := hL.trans_le hLD
  have hE : 0 ≤ E := (abs_nonneg _).trans (hraw (fun _ => (false, false)))
  have herr y : |(P false).weight y - (P true).weight y| ≤ E / L := by
    dsimp only [P]
    rw [rawCarrierConditional_weight, rawCarrierConditional_weight, ← sub_div, abs_div, abs_of_pos hD]
    exact (div_le_div_of_nonneg_right (hraw y) hD.le).trans (div_le_div_of_nonneg_left hE hL hLD)
  apply FiniteLaw.hellingerSq_le_of_sq_error (P false) (P true) ((κ ^ 2) ^ Fintype.card I) ((E / L) ^ 2)
    (pow_pos (sq_pos_of_pos hκ) _)
    (rawCarrierConditional_lower F hθ hθ1 S x₀ r H (kernel false) (fields false) (hlegal false) hκ.le x)
  intro y
  simpa only [sq_abs] using (pow_le_pow_left₀ (abs_nonneg _) (herr y) 2)

end CausalLowerbound.PartC
