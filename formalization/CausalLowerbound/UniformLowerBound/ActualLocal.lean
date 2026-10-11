import CausalLowerbound.UniformLowerBound.LikelihoodBridge
import CausalLowerbound.UniformLowerBound.Moments
import CausalLowerbound.UniformLowerBound.Risk

/-! Actual binary sampling laws and their component comparison. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.UniformLowerBound
open PartB PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}

def actualFamily (regime : Bool) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ h a b : ℝ)
    (hlegal : ∀ (side : Bool) (ζ : S → Bool),
      (fields regime side S (extendBlockSample S ζ) x₀ ℓ h a b).Legal α β γ Lπ L₀ Lτ κ) :
    Bool → (S → Bool) → UniformModel d α β γ Lπ L₀ Lτ κ :=
  fun side ζ => uniformStatisticalModel regime side S (extendBlockSample S ζ)
    x₀ ℓ h a b (hlegal side ζ) le_rfl le_rfl

def actualKernel (regime side : Bool) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ h a b : ℝ)
    (hlegal : ∀ ζ : S → Bool,
      (fields regime side S (extendBlockSample S ζ) x₀ ℓ h a b).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) (x : d → ℝ) (ζ : S → Bool) : FiniteLaw (Bool × Bool) :=
  (fields regime side S (extendBlockSample S ζ) x₀ ℓ h a b).conditionalLaw (hlegal ζ) hκ x

abbrev actualSampleConditional (regime side : Bool) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ h a b : ℝ)
    (hlegal : ∀ (side : Bool) (ζ : S → Bool),
      (fields regime side S (extendBlockSample S ζ) x₀ ℓ h a b).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) {m : ℕ} (x : Fin m → d → ℝ) : FiniteLaw (Fin m → Bool × Bool) :=
  uniformMixtureConditional (signPrior S) (actualFamily regime S x₀ ℓ h a b hlegal side) hκ x

theorem actualSampleConditional_eq_mixture (regime side : Bool) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ h a b : ℝ)
    (hlegal : ∀ (side : Bool) (ζ : S → Bool),
      (fields regime side S (extendBlockSample S ζ) x₀ ℓ h a b).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) {m : ℕ} (x : Fin m → d → ℝ) :
    actualSampleConditional regime side S x₀ ℓ h a b hlegal hκ x =
      (signPrior S).mixture (fun ζ => FiniteLaw.independent
        (fun i => actualKernel regime side S x₀ ℓ h a b (hlegal side) hκ (x i) ζ)) := rfl

theorem actual_kernel_incident_local (regime side : Bool) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ h a b : ℝ)
    (hlegal : ∀ ζ : S → Bool,
      (fields regime side S (extendBlockSample S ζ) x₀ ℓ h a b).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) (x : d → ℝ) (ζ ζ' : S → Bool)
    (he : ∀ k : S, x ∈ carrierBox x₀ ℓ k.val → ζ k = ζ' k) :
    actualKernel regime side S x₀ ℓ h a b hlegal hκ x ζ =
      actualKernel regime side S x₀ ℓ h a b hlegal hκ x ζ' := by
  apply FiniteLaw.ext
  intro w
  unfold actualKernel
  rw [conditionalLaw_weight_eq, conditionalLaw_weight_eq,
    signedField_incident_local S x₀ ℓ h x ζ ζ' he]

def fairSampleLaw (m : ℕ) : FiniteLaw (Fin m → Bool × Bool) :=
  FiniteLaw.independent (fun _ => rademacher.prod rademacher)

theorem fairSampleLaw_weight (m : ℕ) (w : Fin m → Bool × Bool) :
    (fairSampleLaw m).weight w = (1/4 : ℝ)^m := by
  simp only [fairSampleLaw, FiniteLaw.independent, FiniteLaw.prod, rademacher]
  norm_num
  rw [one_div, inv_pow]

theorem actualSampleConditional_density (regime side : Bool) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ h a b : ℝ)
    (hlegal : ∀ (side : Bool) (ζ : S → Bool),
      (fields regime side S (extendBlockSample S ζ) x₀ ℓ h a b).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) {m : ℕ} (x : Fin m → d → ℝ) (w : Fin m → Bool × Bool) :
    (actualSampleConditional regime side S x₀ ℓ h a b hlegal hκ x).weight w =
      (fairSampleLaw m).weight w * (signPrior S).expect (fun ζ => ∏ i,
        if side then likelihoodP regime a b (sign (w i).1) (sign (w i).2)
          (signedField S (extendBlockSample S ζ) x₀ ℓ h (x i)) (coarseBump x₀ h (x i)^2)
        else likelihoodQ a b (sign (w i).1) (sign (w i).2)
          (signedField S (extendBlockSample S ζ) x₀ ℓ h (x i))) := by
  rw [actualSampleConditional_eq_mixture]
  change (signPrior S).expect (fun ζ => ∏ i, (actualKernel regime side S x₀ ℓ h a b
    (hlegal side) hκ (x i) ζ).weight (w i)) = _
  simp only [actualKernel, conditionalLaw_weight_eq, Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_eq_mul_inv,
    Finset.prod_mul_distrib, FiniteLaw.expect_mul_const, fairSampleLaw_weight, one_div, inv_pow]
  ring_nf
  norm_num

theorem actual_sample_eq_of_card_le_one (regime : Bool) (x₀ : d → ℝ) (ℓ h a b : ℝ)
    (hlegal : ∀ (side : Bool) (ζ : activeBlocks (d := d) ℓ h → Bool),
      (fields regime side (activeBlocks ℓ h) (extendBlockSample (activeBlocks ℓ h) ζ)
        x₀ ℓ h a b).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) (hℓ : 0 < ℓ) (hh : 0 < h) {m : ℕ} (hm : m ≤ 1)
    (x : Fin m → d → ℝ) :
    actualSampleConditional regime true (activeBlocks ℓ h) x₀ ℓ h a b hlegal hκ x =
      actualSampleConditional regime false (activeBlocks ℓ h) x₀ ℓ h a b hlegal hκ x := by
  apply FiniteLaw.ext
  intro w
  rw [actualSampleConditional_density, actualSampleConditional_density]
  simp only [↓reduceIte, Bool.false_eq_true]
  congr 1
  cases m with
  | zero => simp
  | succ k =>
    have hk : k = 0 := by omega
    subst k
    simp only [Fin.prod_univ_succ, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    exact one_observation_mixture_equality (signPrior (activeBlocks ℓ h)) regime _ a b
      (sign (w 0).1) (sign (w 0).2) (coarseBump x₀ h (x 0)^2)
      (signPrior_mean _ x₀ ℓ h (x 0)) (signPrior_secondMoment x₀ ℓ h hℓ hh (x 0))

theorem actual_sample_hellinger_le_cutoff (regime : Bool) (x₀ : d → ℝ) (ℓ h a b : ℝ)
    (hlegal : ∀ (side : Bool) (ζ : activeBlocks (d := d) ℓ h → Bool),
      (fields regime side (activeBlocks ℓ h) (extendBlockSample (activeBlocks ℓ h) ζ)
        x₀ ℓ h a b).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 < κ) (hℓ : 0 < ℓ) (hh : 0 < h)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    {m : ℕ} (cutoff : ℕ) (hm : m ≤ cutoff) (x : Fin m → d → ℝ) :
    (actualSampleConditional regime true (activeBlocks ℓ h) x₀ ℓ h a b hlegal hκ.le x).hellingerSq
      (actualSampleConditional regime false (activeBlocks ℓ h) x₀ ℓ h a b hlegal hκ.le x) ≤
        componentHellingerConstant ((2 : ℝ)^Fintype.card d) (4*κ^2) cutoff *
          (a^2*b^2 + (if regime then b^4 else a^4)) := by
  have hfloor : 0 < 4*κ^2 := by positivity
  apply component_hellinger_bound_cutoff _ _ regime ((2 : ℝ)^Fintype.card d) (4*κ^2)
    a b m cutoff (by positivity) hfloor hm
  have hp := component_hellinger_bound (signPrior (activeBlocks (d := d) ℓ h)) (fairSampleLaw m)
    (actualSampleConditional regime true (activeBlocks ℓ h) x₀ ℓ h a b hlegal hκ.le x)
    (actualSampleConditional regime false (activeBlocks ℓ h) x₀ ℓ h a b hlegal hκ.le x)
    regime (Finset.univ : Finset (Fin m))
    (fun w i => sign (w i).1) (fun w i => sign (w i).2)
    (fun i => coarseBump x₀ h (x i)^2)
    (fun i ζ => signedField (activeBlocks ℓ h) (extendBlockSample (activeBlocks ℓ h) ζ)
      x₀ ℓ h (x i)) a b ((2 : ℝ)^Fintype.card d) (4*κ^2)
    ha ha1 hb hb1 (by positivity) hfloor
    (fun w i _ => (abs_sign _).le) (fun w i _ => (abs_sign _).le)
    (fun i _ => ?_) (fun i _ ζ => signedField_abs_le _ _ _ _ _ _)
    (fun i _ => signPrior_mean _ x₀ ℓ h (x i))
    (fun i _ => signPrior_secondMoment x₀ ℓ h hℓ hh (x i))
    (fun w i _ ζ => ?_) (fun w i _ ζ => ?_)
    (fun w => ?_) (fun w => ?_)
  · simpa only [Finset.card_univ, Fintype.card_fin] using hp
  · dsimp only
    rw [abs_of_nonneg (sq_nonneg _)]
    have hg := coarseBump_range x₀ h (x i)
    nlinarith only [hg.1, hg.2]
  · have hbnd := conditionalLaw_cell_lower _ (hlegal true ζ) hκ.le (x i) (w i)
    rw [conditionalLaw_weight_eq] at hbnd
    simp only [↓reduceIte] at hbnd
    linarith only [hbnd]
  · have hbnd := ((fields regime false (activeBlocks ℓ h)
      (extendBlockSample (activeBlocks ℓ h) ζ) x₀ ℓ h a b).conditionalLaw
        (hlegal false ζ) hκ.le (x i)).nonneg (w i)
    rw [conditionalLaw_weight_eq] at hbnd
    simp only [Bool.false_eq_true, ↓reduceIte] at hbnd
    linarith only [hbnd]
  · simpa only [↓reduceIte] using actualSampleConditional_density regime true _ x₀ ℓ h a b hlegal hκ.le x w
  · simpa only [Bool.false_eq_true, ↓reduceIte] using actualSampleConditional_density regime false _ x₀ ℓ h a b hlegal hκ.le x w

end CausalLowerbound.UniformLowerBound
