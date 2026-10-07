import CausalLowerbound.PartB.CompleteGraph
import CausalLowerbound.PartB.IdealIncrementLimit
import CausalLowerbound.WienerSymmetric

/-! The actual ideal increment is real and invariant under every permutation
of the configuration slots. Thus it belongs to the complete algebra on which
the explicit positive polarization operator acts. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Topology

namespace CausalLowerbound.PartB

section Signs
variable {V : Type*} [Fintype V] [DecidableEq V]

def signPermutation (σ : Equiv.Perm V) : (V → Bool) ≃ (V → Bool) where
  toFun ζ := ζ ∘ σ
  invFun ζ := ζ ∘ σ.symm
  left_inv ζ := by funext i; simp
  right_inv ζ := by funext i; simp

theorem independentSigns_permute (σ : Equiv.Perm V) (f : (V → Bool) → ℝ) :
    independentSigns.expect (fun ζ => f (ζ ∘ σ)) = independentSigns.expect f := by
  simp only [FiniteLaw.expect, independentSigns, FiniteLaw.independent, rademacher]
  exact Equiv.sum_comp (signPermutation σ) (fun ζ => (∏ _i : V, (1 / 2 : ℝ)) * f ζ)

theorem idealMonomialMoment_permute {Ω K : Type*} [Fintype Ω] [Fintype K] [DecidableEq K]
    (μ : FiniteLaw Ω) (U : Ω → K → ℝ) (c : K → V → ℝ) (amp : ℝ) (σ : Equiv.Perm V) :
    idealMonomialMoment μ U (fun k i => c k (σ i)) amp = idealMonomialMoment μ U c amp := by
  unfold idealMonomialMoment
  rw [FiniteLaw.expect_prod, FiniteLaw.expect_prod]
  apply μ.expect_congr
  intro ω
  have he (ζ : V → Bool) (k : K) :
      (∑ i, c k (σ i) * sign (ζ i)) = ∑ i, c k i * sign ((ζ ∘ σ.symm) i) := by
    simpa using Equiv.sum_comp σ (fun i => c k i * sign (ζ (σ.symm i)))
  simp_rw [he]
  exact independentSigns_permute σ.symm (fun ζ => ∏ k, (U ω k + amp * ∑ i, c k i * sign (ζ i)))

end Signs
namespace ShellGeometry
open Wiener Filter

variable {Ω K V d : Type*} [Fintype Ω] [Fintype K] [DecidableEq K]
  [Fintype V] [LinearOrder V] [Fintype d] [DecidableEq d]

theorem complete_idealIncrement_permute (μ : FiniteLaw Ω) (U : Ω → K → ℝ)
    (ν : K → d × Bool →₀ ℕ) (amp t : ℝ) (σ : Equiv.Perm V) (u : V × d → ℝ) :
    idealIncrement edgeLeft edgeRight μ U ν amp t (permuteConfiguration σ u) =
      idealIncrement edgeLeft edgeRight μ U ν amp t u := by
  simp only [idealIncrement, complete_graphTaper_permute, complete_lagrangeCoefficient_permute]
  rw [idealMonomialMoment_permute μ U (fun k i => lagrangeCoefficient edgeLeft edgeRight i (ν k) u) amp σ]

theorem idealWiener_mem_symmetricReal (μ : FiniteLaw Ω) (U : Ω → K → ℝ)
    (ν : K → d × Bool →₀ ℕ) (amp t : ℝ) (hamp : 0 ≤ amp) (ht : 0 < t) :
    idealWiener (V := V) edgeLeft edgeRight μ U ν amp t hamp ht ∈
      symmetricRealSubalgebra (d := d) (ι := V) := by
  constructor
  · intro x
    obtain ⟨u, rfl⟩ := torusProjection_quotient.surjective x
    rw [idealWiener_value, Complex.ofReal_im]
  · intro σ x
    obtain ⟨u, rfl⟩ := torusProjection_quotient.surjective x
    change toContinuous _ (torusProjection (permuteConfiguration σ u)) = _
    rw [idealWiener_value, idealWiener_value, complete_idealIncrement_permute]

def symmetricIdealSequence (μ : FiniteLaw Ω) (U : Ω → K → ℝ)
    (ν : K → d × Bool →₀ ℕ) (p B : ℝ) (n : ℕ) : SymmetricReal d V :=
  ⟨idealWienerSequence edgeLeft edgeRight μ U ν p B n,
    idealWiener_mem_symmetricReal μ U ν _ _ _ _⟩

theorem symmetricIdealSequence_value (μ : FiniteLaw Ω) (U : Ω → K → ℝ)
    (ν : K → d × Bool →₀ ℕ) (p B : ℝ) (n : ℕ) (u : V × d → ℝ) :
    toContinuous (symmetricIdealSequence (V := V) μ U ν p B n) (torusProjection u) =
      (idealIncrement edgeLeft edgeRight μ U ν (polynomialAmplitude p (n + 1))
        (logarithmicThreshold p B (n + 1)) u : ℝ) :=
  idealWiener_value _ _ _ _ _ _ _ (polynomialAmplitude_pos p (by positivity)).le
    (logarithmicThreshold_pos p B (le_add_of_nonneg_left (Nat.cast_nonneg n))) u

theorem symmetricIdealSequence_norm_tendsto (μ : FiniteLaw Ω) (U : Ω → K → ℝ)
    (ν : K → d × Bool →₀ ℕ) (p B : ℝ) (hp : 0 < p)
    (hB : (Fintype.card (CompleteEdge V) : ℝ) < 2 * B) :
    Tendsto (fun n => ‖symmetricIdealSequence (V := V) μ U ν p B n‖) atTop (𝓝 0) :=
  idealWienerSequence_norm_tendsto edgeLeft edgeRight μ U ν p B hp hB

end ShellGeometry
end CausalLowerbound.PartB
