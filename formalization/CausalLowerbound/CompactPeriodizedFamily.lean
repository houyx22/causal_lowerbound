import CausalLowerbound.PeriodizedWiener
import CausalLowerbound.WienerSmoothFamily
import CausalLowerbound.WienerConfiguration

/-! Uniform Wiener realizations of actual periodized compact families and
their simultaneous configuration-graph pullbacks. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory UnitAddTorus
open scoped ContDiff Topology

namespace CausalLowerbound.Wiener

attribute [local instance] Real.fact_zero_lt_one
local instance compactFamilyMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance compactFamilyHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance compactFamilyProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {P α : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [Fintype α]

theorem compact_family_slice_smooth (f : P × (α → ℝ) → ℂ)
    (Kp : Set P) (Kx : Set (α → ℝ))
    (hsupport : ∀ p ∈ Kp, tsupport (fun x => f (p, x)) ⊆ Kx)
    (hf : ∀ p ∈ Kp, ∀ x ∈ Kx, ContDiffAt ℝ ∞ f (p, x)) (p : P) (hp : p ∈ Kp) :
    ContDiff ℝ ∞ (fun x => f (p, x)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ Kx
  · exact (hf p hp x hx).comp x (contDiffAt_const.prodMk contDiffAt_id)
  · have hx' : x ∉ tsupport (fun y => f (p, y)) := fun h => hx (hsupport p hp h)
    exact contDiffAt_const.congr_of_eventuallyEq (not_mem_tsupport_iff_eventuallyEq.mp hx')

/-- One constant controls every actual periodized function in the compact
family, for all independent positive integer periods. -/
theorem compact_family_periodized_wiener
    (f : P × (α → ℝ) → ℂ) (Kp : Set P) (Kx : Set (α → ℝ))
    (hKp : IsCompact Kp) (hKx : IsCompact Kx)
    (hsupport : ∀ p ∈ Kp, tsupport (fun x => f (p, x)) ⊆ Kx)
    (hf : ∀ p ∈ Kp, ∀ x ∈ Kx, ContDiffAt ℝ ∞ f (p, x)) :
    ∃ C ≥ 0, ∀ p ∈ Kp, ∀ N : α → ℕ, (∀ i, N i ≠ 0) →
      ∃ A : Fourier α, (∀ x, toContinuous A x = periodizedTorus (fun y => f (p, y)) N x) ∧
        ‖A‖ ≤ C := by
  let e := EuclideanSpace.equiv α ℝ
  let K : Set (EuclideanSpace ℝ α) := e.symm '' Kx
  let g : P × EuclideanSpace ℝ α → ℂ := fun y => f (y.1, e y.2)
  have hK : IsCompact K := hKx.image e.symm.continuous
  have hmem (x : EuclideanSpace ℝ α) (hx : x ∈ K) : e x ∈ Kx := by
    rcases hx with ⟨y, hy, rfl⟩
    simpa using hy
  have hgsupport : ∀ p ∈ Kp, tsupport (fun x => g (p, x)) ⊆ K := by
    intro p hp
    apply closure_minimal _ hK.isClosed
    intro x hx
    exact ⟨e x, hsupport p hp (subset_tsupport _ hx), e.symm_apply_apply x⟩
  have hgsmooth : ∀ p ∈ Kp, ∀ x ∈ K, ContDiffAt ℝ ∞ g (p, x) := by
    intro p hp x hx
    exact (hf p hp (e x) (hmem x hx)).comp (p, x)
      (contDiffAt_fst.prodMk (e.contDiff.comp contDiff_snd).contDiffAt)
  obtain ⟨C, hC, hb⟩ := compact_smooth_family_wiener_bound g Kp K hKp hK hgsupport hgsmooth
  refine ⟨C, hC, ?_⟩
  intro p hp N hN
  have hs := compact_family_slice_smooth f Kp Kx hsupport hf p hp
  have hc : HasCompactSupport (fun x => f (p, x)) :=
    hKx.of_isClosed_subset isClosed_closure (hsupport p hp)
  let F := periodizedContinuous (fun x => f (p, x)) hc hs.continuous N hN
  have hcoeff : Summable (fun k => ‖mFourierCoeff F k‖) := by
    simp only [F, periodized_coefficient_eq_sampled]
    exact (hb p hp N hN).1
  refine ⟨ofContinuous F hcoeff, ?_, ?_⟩
  · intro x
    rw [toContinuous_ofContinuous]
    rfl
  · rw [norm_ofContinuous]
    simp only [F, periodized_coefficient_eq_sampled]
    exact (hb p hp N hN).2

variable {V E d : Type*} [Fintype V] [DecidableEq V] [Fintype E] [Fintype d]

/-- The profile estimate survives all edge pullbacks at once, including
cycles and shared vertices, with the same constant. -/
theorem compact_family_configuration_wiener (a b : E → V)
    (f : P × (((V × d) ⊕ (E × d)) → ℝ) → ℂ)
    (Kp : Set P) (Kx : Set (((V × d) ⊕ (E × d)) → ℝ))
    (hKp : IsCompact Kp) (hKx : IsCompact Kx)
    (hsupport : ∀ p ∈ Kp, tsupport (fun x => f (p, x)) ⊆ Kx)
    (hf : ∀ p ∈ Kp, ∀ x ∈ Kx, ContDiffAt ℝ ∞ f (p, x)) :
    ∃ C ≥ 0, ∀ p ∈ Kp, ∀ N : ((V × d) ⊕ (E × d)) → ℕ, (∀ i, N i ≠ 0) →
      ∃ A : Fourier (V × d), (∀ x, toContinuous A x =
        periodizedTorus (fun y => f (p, y)) N (configurationLift a b x)) ∧ ‖A‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := compact_family_periodized_wiener f Kp Kx hKp hKx hsupport hf
  refine ⟨C, hC, ?_⟩
  intro p hp N hN
  obtain ⟨A, hA, hnorm⟩ := hb p hp N hN
  refine ⟨configurationPullback a b A, ?_, (configurationPullback_bound a b A).trans hnorm⟩
  intro x
  rw [configurationPullback_value, hA]

end CausalLowerbound.Wiener
