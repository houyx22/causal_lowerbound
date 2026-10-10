import CausalLowerbound.UpperBound.TaylorCoefficients

/-! The concrete Taylor vector approximates the effect at every accepted
node, using the fixed neighborhood of the closed cube only. -/

noncomputable section
set_option autoImplicit false
open Set
open scoped BigOperators Classical

namespace CausalLowerbound.UpperBound

variable {d : Type*} [Fintype d]

theorem acceptedStencil_distance_le (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4)
    (X : StencilRole d p → d → ℝ) (hX : X ∈ acceptedStencil p T x₀ h ℓ r)
    (i : StencilRole d p) : ‖X i - x₀‖ ≤ h := by
  have hg := physicalStencil_geometry p T x₀ (observedAnchorCoordinate p x₀ h X)
    (observedAuxiliaryCoordinates p x₀ r X) (observedPartnerCoordinate p x₀ ℓ X)
    hx hh hhsmall hℓ hℓr hrh
    (fun a => ⟨hX.1.1 a, hX.1.2 a⟩)
    (fun a => ⟨hX.2.1.1 a, hX.2.1.2 a⟩) hX.2.2 i
  rw [observedStencil_reconstruct p x₀ h ℓ r hh.ne' hℓ.ne' (hℓ.trans_le hℓr).ne' X] at hg
  exact hg.2

theorem cube_segment_mem {x y : d → ℝ} (hx : x ∈ Icc (0 : d → ℝ) 1)
    (hy : y ∈ Icc (0 : d → ℝ) 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    x + t • (y - x) ∈ Icc (0 : d → ℝ) 1 := by
  have hc : Convex ℝ (Icc (0 : d → ℝ) 1) := by
    rw [← pi_univ_Icc]
    exact convex_pi (fun _ _ => convex_Icc (𝕜 := ℝ) 0 1)
  exact hc.add_smul_sub_mem hx hy ht

theorem frechetTaylor_cube_remainder {f : (d → ℝ) → ℝ} {q : ℕ} {θ C h : ℝ}
    {U : Set (d → ℝ)} (hU : IsOpen U) (hcube : Icc (0 : d → ℝ) 1 ⊆ U)
    (hf : ContDiffOn ℝ q f U) (hholder : HolderControlOn q θ C f U) (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (x y : d → ℝ) (hx : x ∈ Icc (0 : d → ℝ) 1) (hy : y ∈ Icc (0 : d → ℝ) 1)
    (hxy : ‖y - x‖ ≤ h) : |f y - frechetTaylor f q x y| ≤ C * h ^ ((q : ℝ) + θ) := by
  have he := holder_frechetTaylor_remainder_on hU hf hholder hC hθ x y
    (fun t ht => hcube (cube_segment_mem hx hy ht))
  have hfac : (1 : ℝ) ≤ q.factorial := by exact_mod_cast Nat.factorial_pos q
  calc
    _ ≤ C * ‖y - x‖ ^ ((q : ℝ) + θ) / q.factorial := he
    _ ≤ C * ‖y - x‖ ^ ((q : ℝ) + θ) :=
      div_le_self (mul_nonneg hC (Real.rpow_nonneg (norm_nonneg _) _)) hfac
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hxy (add_nonneg (Nat.cast_nonneg _) hθ)) hC

theorem acceptedStencil_taylor_error (p q : ℕ) (hqp : q ≤ p) (T : StencilTemplate d p)
    (f : (d → ℝ) → ℝ) (x₀ : d → ℝ) {h ℓ r C θ : ℝ}
    (hx : ∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) (hh : 0 < h) (hhsmall : h ≤ 1 / 2)
    (hℓ : 0 < ℓ) (hℓr : ℓ ≤ r) (hrh : r ≤ h / 4)
    {U : Set (d → ℝ)} (hU : IsOpen U) (hcube : Icc (0 : d → ℝ) 1 ⊆ U)
    (hf : ContDiffOn ℝ q f U) (hholder : HolderControlOn q θ C f U) (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (X : StencilRole d p → d → ℝ) (hX : X ∈ acceptedStencil p T x₀ h ℓ r) (i : StencilRole d p) :
    |f (X i) - ∑ ν, stencilTaylorCoefficients p q hqp f x₀ h ν * stencilFeature p x₀ h X i ν| ≤
      C * h ^ ((q : ℝ) + θ) := by
  rw [stencilTaylorCoefficients_eval p q hqp f x₀ hh.ne']
  apply frechetTaylor_cube_remainder hU hcube hf hholder hC hθ x₀ (X i)
    ⟨fun a => (hx a).1, fun a => (hx a).2⟩
  · exact acceptedStencil_in_cube p T x₀ hx hh hhsmall hℓ hℓr hrh hX i (Set.mem_univ i)
  · exact acceptedStencil_distance_le p T x₀ hx hh hhsmall hℓ hℓr hrh X hX i

theorem stencilTaylorCoefficients_local_bound (p q : ℕ) (hqp : q ≤ p) (f : (d → ℝ) → ℝ)
    (x₀ : d → ℝ) {h C θ : ℝ} {U : Set (d → ℝ)} (hx : x₀ ∈ U)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hC : 0 ≤ C) (hholder : HolderControlOn q θ C f U) :
    ‖stencilTaylorCoefficients p q hqp f x₀ h‖ ≤
      C * ∑ k : Fin (q + 1), (Fintype.card d : ℝ) ^ k.val :=
  stencilTaylorCoefficients_bound p q hqp f x₀ hh hh1 hC (fun k hk => hholder.1 k hk x₀ hx)

end CausalLowerbound.UpperBound
