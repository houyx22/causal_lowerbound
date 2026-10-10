import CausalLowerbound.UpperBound.TaylorCancellation
import CausalLowerbound.UpperBound.LocalHolderTaylor
import CausalLowerbound.UpperBound.StencilTemplate

/-! Quantitative nuisance cancellation for the weights actually constructed
from the auxiliary boxes.  Smoothness is required only along local Taylor
segments, so the result applies to extensions on a fixed neighborhood. -/

noncomputable section
set_option autoImplicit false
open Set
open scoped BigOperators Classical

namespace CausalLowerbound.UpperBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem frechetTaylor_self (f : E → ℝ) (q : ℕ) (x : E) : frechetTaylor f q x x = f x := by
  unfold frechetTaylor
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hk)
    simp only [sub_self]
    change (k.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ k f x 0 = 0
    rw [ContinuousMultilinearMap.map_zero, mul_zero]
  · simp

theorem local_taylor_remainder_le_power {f : E → ℝ} {q : ℕ} {C θ R : ℝ}
    {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ q f U)
    (hholder : HolderControlOn q θ C f U) (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (x y : E) (hsegment : ∀ t ∈ Icc (0 : ℝ) 1, x + t • (y - x) ∈ U)
    (hdist : ‖y - x‖ ≤ R) :
    |f y - frechetTaylor f q x y| ≤ C * R ^ ((q : ℝ) + θ) := by
  have hfac : (1 : ℝ) ≤ q.factorial := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos q)
  calc
    _ ≤ C * ‖y - x‖ ^ ((q : ℝ) + θ) / q.factorial :=
      holder_frechetTaylor_remainder_on hU hf hholder hC hθ x y hsegment
    _ ≤ C * ‖y - x‖ ^ ((q : ℝ) + θ) :=
      div_le_self (by positivity) hfac
    _ ≤ C * R ^ ((q : ℝ) + θ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hdist (by positivity)) hC

variable {d : Type*} [Fintype d]

theorem tensor_stencil_contrast_bound (p q : ℕ) (hqp : q ≤ p)
    (T : StencilTemplate d p) (z : TensorIndex d p → d → ℝ) (v : d → ℝ)
    (hz : ∀ j, z j ∈ T.box j) {C θ ℓ r : ℝ}
    (hC : 0 ≤ C) (hθ : 0 ≤ θ) (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r)
    (hv : ∀ i, |v i| ≤ ℓ / r)
    (f : E → ℝ) (x : E) (L : (d → ℝ) →L[ℝ] E) {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ q f U) (hholder : HolderControlOn q θ C f U)
    (hsegments : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1,
      x + t • L (tensorStencilNode p z v i) ∈ U)
    (hclose : ‖L v‖ ≤ ℓ) (haux : ∀ j, ‖L (z j)‖ ≤ r) :
    |∑ i, tensorContrastWeights p z v i * f (x + L (tensorStencilNode p z v i))| ≤
      C * (1 + Fintype.card (TensorIndex d p) * T.inverseBound) *
        twoScaleModulus ((q : ℝ) + θ) ℓ r := by
  have hr : 0 < r := hℓ.trans_le hℓr
  have hη : 0 ≤ ℓ / r := div_nonneg hℓ.le hr.le
  have hη1 : ℓ / r ≤ 1 := (div_le_one hr).mpr hℓr
  have ht := T.valid_of_mem_boxes z hz
  have hc := tensorContrastWeights_cancel_taylor p q hqp z v ht.2.1 f x L
  simp only [Fintype.sum_option, tensorStencilNode, Option.elim'_none,
    Option.elim'_some, map_zero, add_zero] at hc
  have hrem (i : Option (Option (TensorIndex d p))) (R : ℝ)
      (hi : ‖L (tensorStencilNode p z v i)‖ ≤ R) :
      |f (x + L (tensorStencilNode p z v i)) -
        frechetTaylor f q x (x + L (tensorStencilNode p z v i))| ≤
        C * R ^ ((q : ℝ) + θ) := by
    apply local_taylor_remainder_le_power hU hf hholder hC hθ
    · simpa only [add_sub_cancel_left] using hsegments i
    · simpa only [add_sub_cancel_left] using hi
  have hb := contrast_le_twoScaleModulus
    (tensorContrastWeights p z v (some none)) (tensorContrastWeights p z v none)
    (f x) (f (x + L v)) (frechetTaylor f q x x) (frechetTaylor f q x (x + L v))
    (fun j => tensorContrastWeights p z v (some (some j)))
    (fun j => f (x + L (z j))) (fun j => frechetTaylor f q x (x + L (z j)))
    C T.inverseBound ((q : ℝ) + θ) ℓ r hC T.inverseBound_pos.le hℓ hℓr
    (by linarith) (frechetTaylor_self f q x).symm
    (completedStencil_partner_bound _)
    (tensorContrastWeights_auxiliary_bound p z v ht.2.2 hη hη1 hv)
    (hrem none ℓ hclose) (fun j => hrem (some (some j)) r (haux j))
  calc
    _ = |tensorContrastWeights p z v (some none) * f x +
        tensorContrastWeights p z v none * f (x + L v) +
        ∑ j, tensorContrastWeights p z v (some (some j)) * f (x + L (z j))| := by
      simp only [Fintype.sum_option, tensorStencilNode, Option.elim'_none,
        Option.elim'_some, map_zero, add_zero]
      congr 1
      ring
    _ ≤ _ := hb

end CausalLowerbound.UpperBound
