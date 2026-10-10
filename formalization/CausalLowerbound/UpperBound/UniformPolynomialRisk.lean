import CausalLowerbound.UpperBound.PolynomialRisk

/-! Uniform risk for the actual sample estimator at polynomial bandwidths.
The estimator and both uniform constants are selected before the model and
the target point.  The only exponent premises are numerical inequalities. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology BigOperators Classical

namespace CausalLowerbound.UpperBound

variable {d : Type*} [Fintype d]

def polynomialStencilEstimate (p : ℕ) (T : StencilTemplate d p)
    (a b cutoff L : ℝ) (hcutoff : 0 < cutoff) (x₀ : d → ℝ) (n : ℕ) :
    (Fin n → (d → ℝ) × (Bool × ℝ)) → ℝ :=
  sampleStencilEstimate p T x₀ (polynomialBandwidth a n) (polynomialBandwidth b n)
    (polynomialBandwidth (1 / Fintype.card d) n) n
    (cutoff * stencilMass p T (polynomialBandwidth a n) (polynomialBandwidth b n)
      (polynomialBandwidth (1 / Fintype.card d) n))
    (mul_pos hcutoff (stencilMass_pos p T (polynomialBandwidth_pos _ _)
      (polynomialBandwidth_pos _ _) (polynomialBandwidth_pos _ _))) L

theorem polynomialStencilEstimate_measurable (p : ℕ) (T : StencilTemplate d p)
    (a b cutoff L : ℝ) (hcutoff : 0 < cutoff) (x₀ : d → ℝ) (n : ℕ) :
    Measurable (polynomialStencilEstimate p T a b cutoff L hcutoff x₀ n) :=
  sampleStencilEstimate_measurable p T x₀ _ _ _ n _ L

theorem exists_uniform_polynomial_upper_bound [Nonempty d]
    {ε lower upper M₂ θα θβ θγ Lπ L₀ Lτ : ℝ}
    (p qα qβ qγ : ℕ) (hαp : qα ≤ p) (hβp : qβ ≤ p) (hγp : qγ ≤ p)
    (T : StencilTemplate d p)
    (hε : 0 < ε) (hε1 : ε < 1) (hlower : 0 < lower) (hupper : 0 ≤ upper) (hM : 0 ≤ M₂)
    {U : Set (d → ℝ)} (hU : IsOpen U) (hcube : Icc (0 : d → ℝ) 1 ⊆ U)
    (hLπ : 0 ≤ Lπ) (hL₀ : 0 ≤ L₀) (hLτ : 0 ≤ Lτ)
    (hθα : 0 ≤ θα) (hθβ : 0 ≤ θβ) (hθγ : 0 ≤ θγ)
    (hα : 0 < (qα : ℝ) + θα) (a b ρ : ℝ)
    (ha : 0 < a) (hac : a < 1 / Fintype.card d) (hcb : 1 / (Fintype.card d : ℝ) ≤ b)
    (htarget : ρ ≤ a * ((qγ : ℝ) + θγ))
    (hnuisance : ρ ≤ b * (min ((qα : ℝ) + θα) 1 + min ((qβ : ℝ) + θβ) 1) +
      (1 / Fintype.card d) * ((qα : ℝ) + θα + ((qβ : ℝ) + θβ) -
        (min ((qα : ℝ) + θα) 1 + min ((qβ : ℝ) + θβ) 1)))
    (hordinary : 2 * ρ ≤ 1 - a * Fintype.card d)
    (hpair : 2 * ρ ≤ 2 - (a + b) * Fintype.card d) :
    ∃ est : (d → ℝ) → (n : ℕ) → (Fin n → (d → ℝ) × (Bool × ℝ)) → ℝ,
      (∀ x₀ n, Measurable (est x₀ n)) ∧ ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
        ∀ n, N ≤ n → ∀ M : RealOutcomeModel d ε lower upper M₂,
          M.LocalRegularity U qα qβ qγ θα θβ θγ Lπ L₀ Lτ →
          ∀ x₀ : d → ℝ, (∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) →
            (∫ z, |est x₀ n z - M.effect x₀| ∂M.sampleLaw (Fin n)) ≤
              C * ((n : ℝ) + 1) ^ (-ρ) := by
  let κ := stencilCutoffConstant (M₂ := M₂) p T hε hε1 hlower hupper
  have hκ : 0 < κ := stencilCutoffConstant_pos p T hε hε1 hlower hupper
  let B := stencilCoarseBudget p T upper
  have hB : 1 ≤ B := stencilCoarseBudget_one_le p T upper
  have hUB : upper ≤ B := stencilCoarseBudget_upper_le p T upper
  let H : ℝ := 4 * Fintype.card (StencilRole d p)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  let C₀ := stencilMasterConstant p qγ T Lπ L₀ Lτ upper M₂ B κ
  have hC₀ : 0 < C₀ := stencilMasterConstant_pos p qγ T hLπ hL₀ hLτ hupper hM (zero_le_one.trans hB) hκ
  let C₁ := 2 + Real.sqrt ((4 : ℝ) ^ Fintype.card d * (H + H ^ 2))
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  refine ⟨polynomialStencilEstimate p T a b κ (stencilEffectCoefficientBound (d := d) qγ Lτ) hκ,
    polynomialStencilEstimate_measurable p T a b κ _ hκ, C₀ * C₁, mul_pos hC₀ hC₁, ?_⟩
  have hD : (0 : ℝ) < Fintype.card d := by exact_mod_cast (Fintype.card_pos (α := d))
  have hb : 0 < b := (one_div_pos.mpr hD).trans_le hcb
  have hgeo := eventually_polynomial_geometry ha hac hcb
  have hmat := eventually_polynomial_matrix_small p T Lπ upper hα hb (one_div_pos.mpr hD).le (hac.trans_le hcb) hκ
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hgeo.and hmat)
  refine ⟨max N (max (Fintype.card (StencilRole d p)) 1), ?_⟩
  intro n hn M hreg x₀ hx
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hnM : Fintype.card (StencilRole d p) ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn1 : 1 ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  obtain ⟨hgeom, hsmall⟩ := hN n hnN
  obtain ⟨hh, hhsmall, hℓ, hℓr, hrh⟩ := hgeom
  have hr := polynomialBandwidth_pos (1 / Fintype.card d) n
  have hη : (0 : ℝ) ≤ 2 * Fintype.card (StencilRole d p) / (n : ℝ) := by positivity
  have hηH : 2 * Fintype.card (StencilRole d p) / (n : ℝ) ≤ H * polynomialBandwidth 1 n := by
    have he := mul_le_mul_of_nonneg_left (reciprocal_sampleSize_le_bandwidth hn1)
      (show (0 : ℝ) ≤ 2 * Fintype.card (StencilRole d p) by positivity)
    dsimp [H]
    convert he using 1 <;> ring
  have hfinite := (M.sampleStencilEstimate_risk_bound p qα qβ qγ hαp hβp hγp T x₀
    hε hε1 hlower hupper hx hh hhsmall hℓ hℓr hrh hU hcube hreg hLπ hL₀ hLτ hθα hθβ hθγ
    n hnM hB hUB (stencilCoarseBudget_group_bound p T upper hn1) hsmall).2
  have hroot := sqrt_stencilMseEnvelope_le_master p qγ T ((qα : ℝ) + θα) ((qβ : ℝ) + θβ)
    ((qγ : ℝ) + θγ) (c := κ) hLπ hL₀ hLτ hupper hM (zero_le_one.trans hB) hh.le hℓ.le hr.le hη
  have hterms := polynomial_master_terms_le (d := d) n hH hη hηH htarget hnuisance hordinary hpair
  have he := hfinite.trans (hroot.trans (mul_le_mul_of_nonneg_left hterms hC₀.le))
  simpa only [polynomialStencilEstimate, ← mul_assoc, polynomialBandwidth, C₀, C₁, κ, B] using he

end CausalLowerbound.UpperBound
