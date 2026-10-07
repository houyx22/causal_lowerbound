import CausalLowerbound.PartC.NaturalPolynomialPolarization
import CausalLowerbound.PartC.RepresentativeReflection
import CausalLowerbound.PartC.WalshReflection
import CausalLowerbound.PartC.VectorSeriesMap

/-! The reflected half of the concrete moment polarization. Its
reconstruction uses the actual sign-flip realization of the representative
involution, and its norm bound is the same as the original half. -/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.PartC.Representative

variable {d ι J I : Type*} [Fintype d] [Fintype ι] [Fintype J] [Fintype I]
  [DecidableEq ι] [DecidableEq J] {D : ℕ}

def momentReflection : (I → Array d ι J D) →L[ℝ] (I → Array d ι J D) :=
  ContinuousLinearMap.pi (fun i => reflection.comp (ContinuousLinearMap.proj i))

@[simp] theorem momentReflection_apply (a : I → Array d ι J D) (i : I) :
    momentReflection a i = reflection (a i) := rfl

@[simp] theorem momentReflection_norm (a : I → Array d ι J D) : ‖momentReflection a‖ = ‖a‖ := by
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg a)).mpr (fun i => by
      simpa only [momentReflection_apply, reflection_norm] using norm_le_pi_norm a i)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (momentReflection a))).mpr
    intro i
    simpa only [momentReflection_apply, reflection_norm] using norm_le_pi_norm (momentReflection a) i

def reflectedMomentCoefficients (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) :
    (I → Array d ι J D) →L[ℝ] VectorSeries.Family ℕ (I → Walsh.Coefficients J) :=
  (VectorSeries.mapEntries Walsh.vectorReflection 1 (fun a => by rw [Walsh.vectorReflection_norm, one_mul])).comp
    ((naturalMomentCoefficients center hc θ).comp momentReflection)

@[simp] theorem reflectedMomentCoefficients_apply
    (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) (a : I → Array d ι J D) (n : ℕ) (i : I) :
    reflectedMomentCoefficients center hc θ a n i =
      Walsh.reflection (naturalPolynomialCoefficients center hc θ (reflection (a i)) n) := rfl

theorem reflectedMomentCoefficients_bound
    (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) (a : I → Array d ι J D) :
    ‖reflectedMomentCoefficients center hc θ a‖ ≤
      ((Fintype.card I : ℝ) * polarizationBound ι θ) * ‖a‖ := by
  have hm := VectorSeries.mapEntries_bound Walsh.vectorReflection 1
    (fun a : I → Walsh.Coefficients J => by rw [Walsh.vectorReflection_norm, one_mul])
    (naturalMomentCoefficients center hc θ (momentReflection a))
  rw [one_mul] at hm
  apply hm.trans
  simpa only [momentReflection_norm] using
    naturalMomentCoefficients_bound center hc θ (momentReflection a)

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

theorem signChart_reflection (x : K → Wiener.Torus (ι × d)) (hx : Continuous x)
    (z : (J → Bool) → ι → K → ℝ) (hz : ∀ ζ i, Continuous (z ζ i)) (hb : ∀ ζ i u, |z ζ i u| ≤ 1)
    (hflip : ∀ ζ i u, z (Walsh.flip ζ) i u = -z ζ i u) (ζ : J → Bool) (a : Array d ι J D) :
    chartEvaluation x hx (z ζ) (hz ζ) (hb ζ) ζ (reflection a) =
      chartEvaluation x hx (z (Walsh.flip ζ)) (hz (Walsh.flip ζ)) (hb (Walsh.flip ζ)) (Walsh.flip ζ) a := by
  ext u
  simp only [chartEvaluation_apply, pointValue_reflection, hflip]

theorem reflectedMomentCoefficients_chart_hasSum [Nonempty ι]
    (center : PolynomialBasis d ι D → ι → Walsh.Coefficients J)
    (hc : ∀ v i, ‖center v i‖ ≤ 1) (θ : ℝ) (hθ : θ ≠ 0)
    (x : K → Wiener.Torus (ι × d)) (hx : Continuous x)
    (z : (J → Bool) → ι → K → ℝ) (hz : ∀ ζ i, Continuous (z ζ i)) (hb : ∀ ζ i u, |z ζ i u| ≤ 1)
    (hflip : ∀ ζ i u, z (Walsh.flip ζ) i u = -z ζ i u)
    (ζ : J → Bool) (a : I → Array d ι J D) (i : I)
    (hsym : ∀ u (σ : Equiv.Perm ι), pointValue (Wiener.permuteSlots σ.symm (x u))
      (fun j => z ζ (σ.symm j) u) ζ (a i) = pointValue (x u) (fun j => z ζ j u) ζ (a i)) :
    HasSum (fun n => Walsh.evaluateCoordinate ζ i (reflectedMomentCoefficients center hc θ a n) •
      chartEvaluation x hx (z ζ) (hz ζ) (hb ζ) ζ (reflection (naturalPolynomialAtom center θ n)))
      (chartEvaluation x hx (z ζ) (hz ζ) (hb ζ) ζ (a i)) := by
  have hsymR : ∀ u (σ : Equiv.Perm ι),
      pointValue (Wiener.permuteSlots σ.symm (x u))
        (fun j => z (Walsh.flip ζ) (σ.symm j) u) (Walsh.flip ζ) (reflection (a i)) =
      pointValue (x u) (fun j => z (Walsh.flip ζ) j u) (Walsh.flip ζ) (reflection (a i)) := by
    intro u σ
    simpa only [pointValue_reflection, hflip, neg_neg, Walsh.flip_flip] using hsym u σ
  have hs := naturalPolynomialCoefficients_chart_hasSum center hc θ hθ x hx
    (z (Walsh.flip ζ)) (hz (Walsh.flip ζ)) (hb (Walsh.flip ζ)) (Walsh.flip ζ) (reflection (a i)) hsymR
  have he (b : Array d ι J D) :
      chartEvaluation x hx (z (Walsh.flip ζ)) (hz (Walsh.flip ζ)) (hb (Walsh.flip ζ)) (Walsh.flip ζ) b =
        chartEvaluation x hx (z ζ) (hz ζ) (hb ζ) ζ (reflection b) :=
    (signChart_reflection x hx z hz hb hflip ζ b).symm
  change HasSum (fun n => Walsh.evaluate ζ
    (Walsh.reflection (naturalPolynomialCoefficients center hc θ (reflection (a i)) n)) •
      chartEvaluation x hx (z ζ) (hz ζ) (hb ζ) ζ (reflection (naturalPolynomialAtom center θ n))) _
  simpa only [Walsh.evaluate_reflection, he, reflection_involution] using hs

end CausalLowerbound.PartC.Representative
