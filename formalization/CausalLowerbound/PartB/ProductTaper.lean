import CausalLowerbound.SmoothCompact
import Mathlib.Topology.Order.Compact

/-! A product taper has uniformly bounded profile derivatives even when its
nonnegative scale parameters are unbounded. Large parameters can be clipped
locally because the taper is exactly one beyond its transition interval. -/

noncomputable section
set_option autoImplicit false
open scoped ContDiff BigOperators Topology
open Filter

namespace CausalLowerbound.PartB

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {V : Type*} [Fintype V]

def productTaper (θ : ℝ → ℝ) (q : V → P × E → ℝ) (lam : V → ℝ) (p : P) (x : E) : ℝ :=
  ∏ i, θ (lam i * q i (p, x))

theorem taper_clip_eq (θ : ℝ → ℝ) (hθ : ∀ r, 2 ≤ r → θ r = 1)
    {c q lam : ℝ} (hc : 0 < c) (hq : c / 2 < q) :
    θ (lam * q) = θ (min lam (4 / c) * q) := by
  by_cases hlam : lam ≤ 4 / c
  · rw [min_eq_left hlam]
  · rw [min_eq_right (le_of_not_ge hlam)]
    have hq0 : 0 < q := lt_trans (by positivity) hq
    have hcap : 2 ≤ 4 / c * q := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc]
      linarith
    rw [hθ _ (hcap.trans (mul_le_mul_of_nonneg_right (le_of_not_ge hlam) hq0.le)), hθ _ hcap]

theorem productTaper_locally_clipped (θ : ℝ → ℝ) (hθ : ∀ r, 2 ≤ r → θ r = 1)
    (q : V → P × E → ℝ) (p : P) (x : E) (lam : V → ℝ) (c : ℝ) (hc : 0 < c)
    (hq : ∀ i, ContinuousAt (fun y => q i (p, y)) x)
    (hlower : ∀ i, c ≤ q i (p, x)) :
    (fun y => productTaper θ q lam p y) =ᶠ[𝓝 x]
      (fun y => productTaper θ q (fun i => min (lam i) (4 / c)) p y) := by
  have he : ∀ᶠ y in 𝓝 x, ∀ i, c / 2 < q i (p, y) :=
    Filter.eventually_all.mpr (fun i => (hq i).eventually
      (Ioi_mem_nhds (show c / 2 < q i (p, x) by linarith [hlower i])))
  filter_upwards [he] with y hy
  exact Finset.prod_congr rfl (fun i _ => taper_clip_eq θ hθ hc (hy i))

/-- All derivatives in the profile variables are bounded by one constant on
the fixed compact sets. The constant is independent of every taper scale. -/
theorem productTaper_uniform_derivatives (θ : ℝ → ℝ) (hθsmooth : ContDiff ℝ ∞ θ)
    (hθone : ∀ r, 2 ≤ r → θ r = 1) (q : V → P × E → ℝ)
    (Kp : Set P) (Kx : Set E) (hKp : IsCompact Kp) (hKx : IsCompact Kx)
    (hq : ∀ i p x, p ∈ Kp → x ∈ Kx → ContDiffAt ℝ ∞ (q i) (p, x))
    (c : ℝ) (hc : 0 < c) (hlower : ∀ i p x, p ∈ Kp → x ∈ Kx → c ≤ q i (p, x))
    (M : ℕ) :
    ∃ C > 0, ∀ j ≤ M, ∀ lam : V → ℝ, (∀ i, 0 ≤ lam i) → ∀ p ∈ Kp, ∀ x ∈ Kx,
      ‖iteratedFDeriv ℝ j (productTaper θ q lam p) x‖ ≤ C := by
  let B : Set (V → ℝ) := Set.Icc 0 (fun _ => 4 / c)
  let K : Set (((V → ℝ) × P) × E) := (B ×ˢ Kp) ×ˢ Kx
  let F : ((V → ℝ) × P) × E → ℝ := fun y => productTaper θ q y.1.1 y.1.2 y.2
  have hK : IsCompact K := (isCompact_Icc.prod hKp).prod hKx
  have hF : ∀ y ∈ K, ContDiffAt ℝ ∞ F y := by
    rintro ⟨⟨lam, p⟩, x⟩ hy
    change ContDiffAt ℝ ∞ (fun y : ((V → ℝ) × P) × E =>
      ∏ i, θ (y.1.1 i * q i (y.1.2, y.2))) ((lam, p), x)
    apply contDiffAt_prod
    intro i _
    exact hθsmooth.contDiffAt.comp ((lam, p), x)
      (((contDiff_apply ℝ ℝ i).comp contDiff_fst.fst).contDiffAt.mul
        ((hq i p x hy.1.2 hy.2).comp ((lam, p), x)
          (contDiffAt_fst.snd.prodMk contDiffAt_snd)))
  obtain ⟨C, hC, hb⟩ := compact_slice_derivative_bound F K hK hF M
  refine ⟨C, hC, ?_⟩
  intro j hj lam hlam p hp x hx
  let lam' : V → ℝ := fun i => min (lam i) (4 / c)
  have hlam' : lam' ∈ B := by
    constructor
    · intro i; exact le_min (hlam i) (by positivity)
    · intro i; exact min_le_right _ _
  have he := productTaper_locally_clipped θ hθone q p x lam c hc
    (fun i => (hq i p x hp hx).continuousAt.comp (continuousAt_const.prodMk continuousAt_id))
    (fun i => hlower i p x hp hx)
  have he' : (fun y => productTaper θ q lam p y) =ᶠ[𝓝[Set.univ] x]
      (fun y => productTaper θ q lam' p y) := by simpa only [nhdsWithin_univ] using he
  have hd := he'.iteratedFDerivWithin_eq (𝕜 := ℝ) he.self_of_nhds j
  simp only [iteratedFDerivWithin_univ] at hd
  rw [hd]
  exact hb j hj (lam', p) x ⟨⟨hlam', hp⟩, hx⟩

end CausalLowerbound.PartB
