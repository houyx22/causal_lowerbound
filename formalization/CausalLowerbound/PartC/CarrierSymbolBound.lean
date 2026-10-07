import CausalLowerbound.PartB.CarrierProbability

/-! A symbol projection of the fixed point is bounded by its atom projections
times the total nonconstant label mass. This argument does not require a
separate contraction estimate in the symbol seminorm. -/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.PartC

open PartB

variable {E V F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem carrier_symbol_bound {L : ℝ} (A : CarrierCoefficients E V L)
    (K : ℝ) (hK : 0 ≤ K) (e D : E) (atom : ℕ → E) (M : ℝ)
    (hatom : ∀ m, ‖atom m - e‖ ≤ M) (hfixed : A.update K e atom D = D)
    (P : E →L[ℝ] F) (he : P e = 0) (σ : ℝ)
    (hsymbol : ∀ m, ‖P (atom m)‖ ≤ σ) :
    ‖P D‖ ≤ σ * A.mass K D := by
  have hsum := A.update_summable K hK e atom M hatom D
  have heq : P D = ∑' m, A.weight K D m • P (atom m) := by
    calc
      P D = P (A.update K e atom D) := congrArg P hfixed.symm
      _ = _ := by
        rw [CarrierCoefficients.update, map_add, he, zero_add, P.map_tsum hsum]
        simp only [map_smul, map_sub, he, sub_zero]
  rw [heq]
  have hb := norm_bounded_synthesis (A.weight K D) (A.weight_abs_summable K hK D)
    (fun m => P (atom m)) σ hsymbol
  simpa only [abs_of_nonneg (A.weight_nonneg K hK D _), CarrierCoefficients.mass] using hb

/-- When atom symbol mass is O(t^d), this gives the desired O(L t^d)
fixed-point symbol bound; L is the small polarization/increment constant. -/
theorem carrier_symbol_bound_of_norm {L : ℝ} (A : CarrierCoefficients E V L)
    (K : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L) (e D : E) (atom : ℕ → E) (M : ℝ)
    (hatom : ∀ m, ‖atom m - e‖ ≤ M) (hfixed : A.update K e atom D = D)
    (hD : ‖D‖ ≤ 2) (P : E →L[ℝ] F) (he : P e = 0) (σ : ℝ) (hσ : 0 ≤ σ)
    (hsymbol : ∀ m, ‖P (atom m)‖ ≤ σ) :
    ‖P D‖ ≤ 2 * K * L * σ := by
  calc
    _ ≤ σ * A.mass K D := carrier_symbol_bound A K hK e D atom M hatom hfixed P he σ hsymbol
    _ ≤ σ * (K * L * ‖D‖) := mul_le_mul_of_nonneg_left (A.mass_bound K hK D) hσ
    _ ≤ σ * (K * L * 2) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hD (mul_nonneg hK hL)) hσ
    _ = _ := by ring

end CausalLowerbound.PartC
