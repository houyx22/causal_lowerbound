import CausalLowerbound.PartB.CarrierMarginal
import CausalLowerbound.PartB.CarrierLikelihood
import CausalLowerbound.PartB.TorusTaper

/-! The actual evaluated projectivity identity for every retained component
with at most Q sites. The activation is the density-weighted ghost average
of the actual complete-graph taper, rather than an assumed scalar. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Filter MeasureTheory
open scoped BigOperators Classical
namespace CausalLowerbound.PartB.ShellGeometry
open Wiener ConfigurationShells
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d K G : Type*} [Fintype d] [DecidableEq d] [Fintype K] [Fintype G]

def completedTorusTaper (Q : ℕ) (e : K ⊕ G ≃ Fin Q) (ε : ℝ)
    (x : (K → Torus d) × (G → Torus d)) : ℝ :=
  torusTaper Q ε (Sum.elim x.1 x.2 ∘ e.symm)

theorem completedTorusTaper_continuous (Q : ℕ) (e : K ⊕ G ≃ Fin Q) (ε : ℝ) :
    Continuous (completedTorusTaper (d := d) Q e ε) := by
  apply (torusTaper_continuous Q ε).comp
  apply continuous_pi
  intro i
  change Continuous (fun x : (K → Torus d) × (G → Torus d) => Sum.elim x.1 x.2 (e.symm i))
  cases e.symm i with
  | inl k => exact (continuous_apply k).comp continuous_fst
  | inr g => exact (continuous_apply g).comp continuous_snd

theorem completedTorusTaper_bounds (Q : ℕ) (e : K ⊕ G ≃ Fin Q) (ε : ℝ)
    (x : (K → Torus d) × (G → Torus d)) :
    0 ≤ completedTorusTaper Q e ε x ∧ completedTorusTaper Q e ε x ≤ 1 :=
  torusTaper_bounds Q ε _

def completedRealConfiguration (Q : ℕ) (e : K ⊕ G ≃ Fin Q)
    (u : K → d → ℝ) (z : G → Torus d) : Fin Q × d → ℝ :=
  fun a => (Sum.elim u (fun g => torusRepresentative (z g)) (e.symm a.1)) a.2

theorem completedRealConfiguration_keep (Q : ℕ) (e : K ⊕ G ≃ Fin Q)
    (u : K → d → ℝ) (z : G → Torus d) (i : K) :
    configurationSite (completedRealConfiguration Q e u z) (e (Sum.inl i)) = u i := by
  change (fun a => Sum.elim u (fun g => torusRepresentative (z g)) (e.symm (e (Sum.inl i))) a) = u i
  rw [e.symm_apply_apply]
  rfl

theorem completedRealConfiguration_projection (Q : ℕ) (e : K ⊕ G ≃ Fin Q)
    (u : K → d → ℝ) (z : G → Torus d) :
    (fun i => torusProjection (configurationSite (completedRealConfiguration Q e u z) i)) =
      Sum.elim (fun k => torusProjection (u k)) z ∘ e.symm := by
  funext i
  change torusProjection (Sum.elim u (fun g => torusRepresentative (z g)) (e.symm i)) =
    Sum.elim (fun k => torusProjection (u k)) z (e.symm i)
  cases he : e.symm i with
  | inl k => rfl
  | inr g =>
    exact torusProjection_representative (z g)

theorem completedRealConfiguration_taper (Q : ℕ) (e : K ⊕ G ≃ Fin Q)
    (u : K → d → ℝ) (z : G → Torus d) (ε : ℝ) :
    completeTaper Q ε (completedRealConfiguration Q e u z) =
      completedTorusTaper Q e ε ((fun k => torusProjection (u k)), z) := by
  rw [← torusTaper_lift, completedRealConfiguration_projection]
  rfl

/-- Closed carrier-to-likelihood identity: the same constructed H and kernel
work for all retained sites, binary outcomes and physical coefficients. -/
theorem paper_evaluated_posterior_likelihood (Q : ℕ) [NeZero Q]
    (e : K ⊕ G ≃ Fin Q) (ρ θ p B : ℝ) (hρ : 0 < ρ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hp : 0 < p) (hB : ((Q.choose 2 : ℝ) + 2) / 2 < B) :
    ∀ᶠ n : ℕ in atTop, ∃ (H : DiscreteLaw ℕ)
      (kernel : ℕ → FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q))),
      0 < H.weight 0 ∧ (∀ label z, 0 < (kernel label).weight z) ∧
      ∀ (u : K → d → ℝ) (side : Bool) (R T : K → ℝ) (a b : ℝ) (η δ offset ψ : K → ℝ),
        let f := fun z => retainedLikelihood Q side R T a b η δ offset ψ u (paperCoefficientAtoms Q ρ z)
        let χ := ghostActivation H Q θ (completedTorusTaper Q e (logarithmicThreshold p B (n + 1)))
          (fun i => torusProjection (u i))
        (coefficientPosterior H kernel Q θ hθ.le hθ1 (fun i => torusProjection (u i))).expect f -
          (paperCoefficientLaw Q).expect f = χ *
            (((paperCoefficientLaw Q).prod (independentSigns (ι := Fin Q))).expect (fun z =>
              jitteredRetainedLikelihood Q side R T a b η δ offset ψ u (paperCoefficientAtoms Q ρ z.1)
                (polynomialAmplitude p (n + 1)) (fun i => sign (z.2 (e (Sum.inl i))))) -
              (paperCoefficientLaw Q).expect f) := by
  have hK : Fintype.card K ≤ Q := by
    have hc := Fintype.card_congr e
    simp only [Fintype.card_sum, Fintype.card_fin] at hc
    omega
  filter_upwards [paper_posterior_retained_likelihood (d := d) (I := K)
    Q hK ρ θ p B hρ hθ hθ1 hp hB] with n hn
  obtain ⟨H, kernel, h0, hk, hm⟩ := hn
  refine ⟨H, kernel, h0, hk, ?_⟩
  intro u side R T a b η δ offset ψ
  dsimp only
  let f := fun z => retainedLikelihood Q side R T a b η δ offset ψ u (paperCoefficientAtoms Q ρ z)
  let up := fun i => torusProjection (u i)
  rw [← coefficientPosterior_constant_expect H (paperCoefficientLaw Q) Q θ hθ.le hθ1 up f]
  apply coefficientPosterior_ghost_interpolation
  intro z
  rw [coefficientPosterior_constant_expect]
  have h := hm (completedRealConfiguration Q e u z) (fun i => e (Sum.inl i)) side R T a b η δ offset ψ
  simp_rw [completedRealConfiguration_keep] at h
  rw [completedRealConfiguration_projection] at h
  have hr := coefficientPosterior_difference_equiv H (fun _ => paperCoefficientLaw Q)
    kernel Q θ hθ.le hθ1 e.symm (Sum.elim up z) f
  simp_rw [coefficientPosterior_constant_expect] at hr
  rw [← hr]
  change _ = completedTorusTaper Q e (logarithmicThreshold p B (n + 1)) (up, z) * _
  rw [← completedRealConfiguration_taper]
  rw [coefficientPosterior_constant_expect]
  exact h

end CausalLowerbound.PartB.ShellGeometry
