import CausalLowerbound.PartB.CarrierProbability

/-! Equal label weights on involution pairs force the carrier update,
and hence its actual fixed point, to be invariant. -/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.PartC

open PartB

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] {L : ℝ}

theorem carrier_update_invariant (A : CarrierCoefficients E V L) (K : ℝ) (hK : 0 ≤ K)
    (e : E) (atom : ℕ → E) (M : ℝ) (hatom : ∀ n, ‖atom n - e‖ ≤ M)
    (R : E →L[ℝ] E) (he : R e = e) (σ : Equiv.Perm ℕ)
    (hpair : ∀ n, R (atom n) = atom (σ n))
    (hweight : ∀ D n, ‖A.coeff D (σ n)‖ = ‖A.coeff D n‖) (D : E) :
    R (A.update K e atom D) = A.update K e atom D := by
  rw [CarrierCoefficients.update, map_add, he,
    R.map_tsum (A.update_summable K hK e atom M hatom D)]
  simp only [map_smul, map_sub, he, hpair]
  congr 1
  calc
    _ = ∑' n, A.weight K D (σ n) • (atom (σ n) - e) := by
      apply tsum_congr
      intro n
      simp only [CarrierCoefficients.weight, hweight]
    _ = ∑' n, A.weight K D n • (atom n - e) := σ.tsum_eq (fun n => A.weight K D n • (atom n - e))

theorem carrier_fixed_point_invariant (A : CarrierCoefficients E V L) (K : ℝ) (hK : 0 ≤ K)
    (e : E) (atom : ℕ → E) (M : ℝ) (hatom : ∀ n, ‖atom n - e‖ ≤ M)
    (R : E →L[ℝ] E) (he : R e = e) (σ : Equiv.Perm ℕ)
    (hpair : ∀ n, R (atom n) = atom (σ n))
    (hweight : ∀ D n, ‖A.coeff D (σ n)‖ = ‖A.coeff D n‖)
    (D : E) (hfixed : A.update K e atom D = D) : R D = D := by
  simpa only [hfixed] using carrier_update_invariant A K hK e atom M hatom R he σ hpair hweight D

end CausalLowerbound.PartC
