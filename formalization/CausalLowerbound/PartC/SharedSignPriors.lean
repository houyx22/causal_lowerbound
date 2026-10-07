import CausalLowerbound.DiscreteTilt
import CausalLowerbound.PartB.SignMonomials

/-! Countable global priors with block-dependent label laws and a single
shared sign field. Only the coefficient variables are conditionally
independent given the labels and signs. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
open MeasureTheory

namespace CausalLowerbound.PartC
open PartB
variable {K J Ω : Type*} [Fintype K] [DecidableEq K]
  [Fintype J] [DecidableEq J] [Fintype Ω]

def sharedSignPrior (H : K → DiscreteLaw ℕ) : DiscreteLaw ((K → ℕ) × (J → Bool)) :=
  (DiscreteLaw.independent H).joint (fun _ => independentSigns)

def signBlockKernel (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω)
    (z : (K → ℕ) × (J → Bool)) : FiniteLaw (K → Ω) :=
  FiniteLaw.independent (fun k => kernel k z.2 (z.1 k))

def signBlockPrior (H : K → DiscreteLaw ℕ) (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) :
    DiscreteLaw (((K → ℕ) × (J → Bool)) × (K → Ω)) :=
  (sharedSignPrior H).joint (signBlockKernel kernel)

theorem signBlockPrior_weight (H : K → DiscreteLaw ℕ)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω)
    (z : ((K → ℕ) × (J → Bool)) × (K → Ω)) :
    (signBlockPrior H kernel).weight z =
      independentSigns.weight z.1.2 *
        ∏ k, (H k).weight (z.1.1 k) * (kernel k z.1.2 (z.1.1 k)).weight (z.2 k) := by
  change ((DiscreteLaw.independent H).weight z.1.1 * independentSigns.weight z.1.2) *
    (FiniteLaw.independent (fun k => kernel k z.1.2 (z.1.1 k))).weight z.2 = _
  rw [DiscreteLaw.independent_weight]
  simp only [FiniteLaw.independent, Finset.prod_mul_distrib]
  ring

theorem signBlockPrior_common_environment [MeasurableSpace Ω]
    (H : K → DiscreteLaw ℕ) (P Q : K → (J → Bool) → ℕ → FiniteLaw Ω) :
    (signBlockPrior H P).toMeasure.map Prod.fst =
      (signBlockPrior H Q).toMeasure.map Prod.fst := by
  exact (DiscreteLaw.joint_measure_label (sharedSignPrior H) (signBlockKernel P)).trans
    (DiscreteLaw.joint_measure_label (sharedSignPrior H) (signBlockKernel Q)).symm

theorem sharedSignPrior_expect (H : K → DiscreteLaw ℕ)
    (f : ((K → ℕ) × (J → Bool)) → ℝ) (B : ℝ) (hf : ∀ z, |f z| ≤ B) :
    (sharedSignPrior H).expect f =
      (DiscreteLaw.independent H).expect (fun labels =>
        independentSigns.expect (fun ζ => f (labels, ζ))) :=
  DiscreteLaw.expect_joint _ _ f B hf

theorem signBlockPrior_expect (H : K → DiscreteLaw ℕ)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω)
    (f : (((K → ℕ) × (J → Bool)) × (K → Ω)) → ℝ) (B : ℝ) (hf : ∀ z, |f z| ≤ B) :
    (signBlockPrior H kernel).expect f =
      (sharedSignPrior H).expect (fun z => (signBlockKernel kernel z).expect (fun U => f (z, U))) :=
  DiscreteLaw.expect_joint _ _ f B hf

/-- A common positive tilt preserves the conditional coefficient kernel,
but generally changes the joint distribution of labels and shared signs. -/
theorem signBlockPrior_tilt (H : K → DiscreteLaw ℕ)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω)
    (w : ((K → ℕ) × (J → Bool)) → ℝ) (lo hi : ℝ) (hlo : 0 < lo)
    (hw : ∀ z, lo ≤ w z ∧ w z ≤ hi) :
    (signBlockPrior H kernel).tilt (fun z => w z.1) lo hi hlo (fun z => hw z.1) =
      ((sharedSignPrior H).tilt w lo hi hlo hw).joint (signBlockKernel kernel) :=
  DiscreteLaw.tilt_joint _ _ w lo hi hlo hw

theorem signBlockPrior_tilt_common_environment [MeasurableSpace Ω]
    (H : K → DiscreteLaw ℕ) (P Q : K → (J → Bool) → ℕ → FiniteLaw Ω)
    (w : ((K → ℕ) × (J → Bool)) → ℝ) (lo hi : ℝ) (hlo : 0 < lo)
    (hw : ∀ z, lo ≤ w z ∧ w z ≤ hi) :
    ((signBlockPrior H P).tilt (fun z => w z.1) lo hi hlo (fun z => hw z.1)).toMeasure.map Prod.fst =
      ((signBlockPrior H Q).tilt (fun z => w z.1) lo hi hlo (fun z => hw z.1)).toMeasure.map Prod.fst :=
  DiscreteLaw.tilted_common_label (sharedSignPrior H) (signBlockKernel P) (signBlockKernel Q)
    w lo hi hlo hw

end CausalLowerbound.PartC
