import CausalLowerbound.PartC.PaperOutcomeTarget
import CausalLowerbound.PartC.PhysicalOutcomeVariance

/-! The complete cubic target with the actual normalized variance.
The fixed variance Fourier bound is absorbed into the target constant,
uniformly over sample size, rough signs, and physical carrier blocks. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d]

def paperPhysicalOutcomeValue {J : Type*} [Fintype J] [DecidableEq J]
    (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (r h : ℝ) (k : d → ℤ) (c w N t τ : ℝ)
    (v : Representative.Array d (Fin Q) J 3) (η : MomentExponent (CoefficientExponent d Q) (4 * Q))
    (u : Fin Q × d → ℝ) (z : Fin Q → ℝ) (ζ : J → Bool) : ℝ :=
  (Fintype.card (Equiv.Perm (Fin Q)) : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin Q),
    outcomeChoiceValue edgeLeft edgeRight (paperCoefficientLaw Q)
      (fun ω (j : MomentPositions η) => paperCoefficientAtoms Q ρ ω j.1)
      (fun j : MomentPositions η => polynomialBasisDegree j.1) (t * N) τ
      (fun i => normalizedRoughVariance x₀ r h k c w N (fun j => u (σ i, j)))
      v (fun p => u (σ p.1, p.2)) (fun i => z (σ i)) ζ

theorem paperOutcomeTargetValue_eq_physical {J : Type*} [Fintype J] [DecidableEq J]
    (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (r h : ℝ) (k : d → ℤ) (c w N t τ : ℝ)
    (κ : Fin Q → Fourier (Fin Q × d))
    (hκ : ∀ i u, u ∈ Set.Icc (0 : Fin Q × d → ℝ) 1 →
      toContinuous (κ i) (torusProjection u) =
        (normalizedRoughVariance x₀ r h k c w N (fun j => u (i, j)) : ℂ))
    (v : Representative.Array d (Fin Q) J 3) (η : MomentExponent (CoefficientExponent d Q) (4 * Q))
    (u : Fin Q × d → ℝ) (hu : u ∈ Set.Icc 0 1) (z : Fin Q → ℝ) (ζ : J → Bool) :
    paperOutcomeTargetValue Q ρ (t * N) τ κ v η u z ζ =
      paperPhysicalOutcomeValue Q ρ x₀ r h k c w N t τ v η u z ζ := by
  unfold paperOutcomeTargetValue symmetricOutcomeChoiceValue paperPhysicalOutcomeValue
  apply congrArg (fun s : ℝ => (Fintype.card (Equiv.Perm (Fin Q)) : ℝ)⁻¹ * s)
  apply Finset.sum_congr rfl
  intro σ _
  have hperm : (fun p => u (σ p.1, p.2)) ∈ Set.Icc (0 : Fin Q × d → ℝ) 1 :=
    ⟨fun p => hu.1 (σ p.1, p.2), fun p => hu.2 (σ p.1, p.2)⟩
  have he : (fun i => (toContinuous (κ i) (torusProjection (fun p => u (σ p.1, p.2)))).re) =
      (fun i => normalizedRoughVariance x₀ r h k c w N (fun j => u (σ i, j))) := by
    funext i
    rw [hκ i _ hperm, Complex.ofReal_re]
  rw [he]

theorem exists_physical_paperOutcomeTarget (Q : ℕ) (ρ : ℝ) :
    ∃ C ≥ 0, ∀ (J : Type*) [Fintype J] [DecidableEq J],
      ∀ (x₀ : d → ℝ) (r h : ℝ), 0 < r → r ≤ h → ∀ k : activeBlocks (d := d) r h,
      ∀ (c w N t τ : ℝ), 0 < w → w ≤ 1 / 2 → 0 < N → 0 < t → 0 < τ →
      ∀ M : Fourier d, ‖M‖ ≤ N →
      (∀ u ∈ Set.Icc (0 : d → ℝ) 1, toContinuous M (torusProjection u) =
        (assignmentMultiplier c w (fun j => 4 * u j - 2) : ℂ)) →
      ∃ T : Representative.Array d (Fin Q) J 3 →L[ℝ]
          (MomentExponent (CoefficientExponent d Q) (4 * Q) → Representative.Array d (Fin Q) J 3),
        (∀ v, ‖T v‖ ≤ (C * ((levelBudget 2 τ + 1 : ℕ) : ℝ) ^ Q.choose 2 *
          ∑ j ∈ Finset.Icc 1 (4 * Q), ((t * N) / τ) ^ j) * ‖v‖) ∧
        (∀ v i x z ζ (σ : Equiv.Perm (Fin Q)),
          pointValue (permuteSlots σ x) (fun j => z (σ j)) ζ (T v i) = pointValue x z ζ (T v i)) ∧
        (∀ v i S, remove S (T v i) = T (remove S v) i) ∧
        ∀ v i u, u ∈ Set.Icc (0 : Fin Q × d → ℝ) 1 → ∀ z ζ,
          pointValue (torusProjection u) z ζ (T v i) =
            paperPhysicalOutcomeValue Q ρ x₀ r h k.val c w N t τ v i u z ζ := by
  obtain ⟨C, hC, htarg⟩ := exists_paperOutcomeTarget (d := d) Q ρ
  obtain ⟨L, hL, hvar⟩ := exists_physicalOutcomeVariance (d := d) (V := Fin Q)
  refine ⟨C * L ^ Q, mul_nonneg hC (pow_nonneg (zero_le_one.trans hL) _),
    fun J _ _ x₀ r h hr hrh k c w N t τ hw hw1 hN ht hτ M hM hMv => ?_⟩
  obtain ⟨κ, hκ, hκr, hκv⟩ := hvar x₀ r h hr hrh k c w N hw hw1 hN M hM hMv
  obtain ⟨T, hT, hsym, hrem, hvalue⟩ := htarg J (t * N) (mul_pos ht hN).le τ hτ L hL κ hκ
  refine ⟨T, fun v => (hT v).trans_eq (by ring), hsym, hrem, fun v i u hu z ζ => ?_⟩
  rw [hvalue v i u z ζ (fun u j => hκr j _)]
  exact paperOutcomeTargetValue_eq_physical Q ρ x₀ r h k.val c w N t τ κ hκv v i u hu z ζ

end CausalLowerbound.PartC
