import CausalLowerbound.PartB.ProductTaper
import CausalLowerbound.CompactPeriodizedFamily

/-! The actual compact profile times a product taper has a uniform Wiener
realization. The constant is independent of all nonnegative taper scales. -/

noncomputable section
set_option autoImplicit false
open scoped ContDiff BigOperators

namespace CausalLowerbound.PartB

open Wiener

variable {P α V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [Fintype α] [Fintype V]

def taperedProfile (θ : ℝ → ℝ) (q : V → P × (α → ℝ) → ℝ)
    (H : P × (α → ℝ) → ℂ) (lam : V → ℝ) (p : P) (x : α → ℝ) : ℂ :=
  (productTaper θ q lam p x : ℂ) * H (p, x)

theorem taperedProfile_eq_clipped (θ : ℝ → ℝ) (hθ : ∀ r, 2 ≤ r → θ r = 1)
    (q : V → P × (α → ℝ) → ℝ) (H : P × (α → ℝ) → ℂ)
    (K : Set (α → ℝ)) (p : P) (hsupport : tsupport (fun x => H (p, x)) ⊆ K)
    (c : ℝ) (hc : 0 < c) (hlower : ∀ i x, x ∈ K → c ≤ q i (p, x)) (lam : V → ℝ) :
    taperedProfile θ q H lam p = taperedProfile θ q H (fun i => min (lam i) (4 / c)) p := by
  funext x
  by_cases hx : x ∈ K
  · have he : productTaper θ q lam p x =
        productTaper θ q (fun i => min (lam i) (4 / c)) p x :=
      Finset.prod_congr rfl (fun i _ => taper_clip_eq θ hθ hc (by linarith [hlower i x hx]))
    simp only [taperedProfile, he]
  · have hz : H (p, x) = 0 := by
      by_contra hn
      exact hx (hsupport (subset_tsupport _ hn))
    simp only [taperedProfile, hz, mul_zero]

theorem taperedProfile_family_smooth (θ : ℝ → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (q : V → P × (α → ℝ) → ℝ) (H : P × (α → ℝ) → ℂ)
    (lam : V → ℝ) (p : P) (x : α → ℝ)
    (hq : ∀ i, ContDiffAt ℝ ∞ (q i) (p, x)) (hH : ContDiffAt ℝ ∞ H (p, x)) :
    ContDiffAt ℝ ∞ (fun y : ((V → ℝ) × P) × (α → ℝ) =>
      taperedProfile θ q H y.1.1 y.1.2 y.2) ((lam, p), x) := by
  have ht : ContDiffAt ℝ ∞ (fun y : ((V → ℝ) × P) × (α → ℝ) =>
      productTaper θ q y.1.1 y.1.2 y.2) ((lam, p), x) := by
    apply contDiffAt_prod
    intro i _
    exact hθ.contDiffAt.comp ((lam, p), x)
      (((contDiff_apply ℝ ℝ i).comp contDiff_fst.fst).contDiffAt.mul
        ((hq i).comp ((lam, p), x) (contDiffAt_fst.snd.prodMk contDiffAt_snd)))
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp ((lam, p), x) ht).mul
    (hH.comp ((lam, p), x) (contDiffAt_fst.snd.prodMk contDiffAt_snd))

/-- Uniformity in the unbounded taper scales is proved by exact clipping,
followed by the compact-family periodization theorem. -/
theorem tapered_family_wiener (θ : ℝ → ℝ) (hθsmooth : ContDiff ℝ ∞ θ)
    (hθone : ∀ r, 2 ≤ r → θ r = 1) (q : V → P × (α → ℝ) → ℝ)
    (H : P × (α → ℝ) → ℂ) (Kp : Set P) (Kx : Set (α → ℝ))
    (hKp : IsCompact Kp) (hKx : IsCompact Kx)
    (hsupport : ∀ p ∈ Kp, tsupport (fun x => H (p, x)) ⊆ Kx)
    (hH : ∀ p ∈ Kp, ∀ x ∈ Kx, ContDiffAt ℝ ∞ H (p, x))
    (hq : ∀ i p x, p ∈ Kp → x ∈ Kx → ContDiffAt ℝ ∞ (q i) (p, x))
    (c : ℝ) (hc : 0 < c) (hlower : ∀ i p x, p ∈ Kp → x ∈ Kx → c ≤ q i (p, x)) :
    ∃ C ≥ 0, ∀ lam : V → ℝ, (∀ i, 0 ≤ lam i) → ∀ p ∈ Kp,
      ∀ N : α → ℕ, (∀ i, N i ≠ 0) → ∃ A : Fourier α,
        (∀ x, toContinuous A x = periodizedTorus (taperedProfile θ q H lam p) N x) ∧ ‖A‖ ≤ C := by
  let B : Set (V → ℝ) := Set.Icc 0 (fun _ => 4 / c)
  let F : ((V → ℝ) × P) × (α → ℝ) → ℂ :=
    fun y => taperedProfile θ q H y.1.1 y.1.2 y.2
  have hs : ∀ p ∈ B ×ˢ Kp, tsupport (fun x => F (p, x)) ⊆ Kx := by
    rintro ⟨lam, p⟩ hp
    exact tsupport_mul_subset_right.trans (hsupport p hp.2)
  have hf : ∀ p ∈ B ×ˢ Kp, ∀ x ∈ Kx, ContDiffAt ℝ ∞ F (p, x) := by
    rintro ⟨lam, p⟩ hp x hx
    exact taperedProfile_family_smooth θ hθsmooth q H lam p x
      (fun i => hq i p x hp.2 hx) (hH p hp.2 x hx)
  obtain ⟨C, hC, hb⟩ := compact_family_periodized_wiener F (B ×ˢ Kp) Kx
    (isCompact_Icc.prod hKp) hKx hs hf
  refine ⟨C, hC, ?_⟩
  intro lam hlam p hp N hN
  let lam' : V → ℝ := fun i => min (lam i) (4 / c)
  have hlam' : lam' ∈ B := ⟨fun i => le_min (hlam i) (by positivity), fun i => min_le_right _ _⟩
  obtain ⟨A, hA, hnorm⟩ := hb (lam', p) ⟨hlam', hp⟩ N hN
  refine ⟨A, ?_, hnorm⟩
  intro x
  rw [hA, taperedProfile_eq_clipped θ hθone q H Kx p (hsupport p hp) c hc
    (fun i x hx => hlower i p x hp hx) lam]

end CausalLowerbound.PartB
