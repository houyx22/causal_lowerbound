import CausalLowerbound.PartB.ActivePackets
import CausalLowerbound.ScaleControl

/-! Uniform derivative control for finite families of compact profiles on
a lattice. Constants do not depend on the number of active sites, the
draw of profiles, the translation, or the spatial scales. -/
noncomputable section
set_option autoImplicit false
open scoped ContDiff BigOperators
namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [Fintype Ω]

def latticeField (S : Finset (d → ℤ)) (f : Ω → (d → ℝ) → ℝ)
    (sample : (d → ℤ) → Ω) (x₀ : d → ℝ) (r : ℝ) (x : d → ℝ) : ℝ :=
  ∑ k ∈ S, rescaled (f (sample k)) (packetCenter x₀ r k) r x

def localizedLatticeField (S : Finset (d → ℤ)) (f : Ω → (d → ℝ) → ℝ)
    (sample : (d → ℤ) → Ω) (x₀ : d → ℝ) (r h : ℝ) (x : d → ℝ) : ℝ :=
  coarseBump x₀ h x * latticeField S f sample x₀ r x

theorem latticeField_smooth (S : Finset (d → ℤ)) (f : Ω → (d → ℝ) → ℝ)
    (hs : ∀ sampleIndex, ContDiff ℝ ∞ (f sampleIndex)) (sample : (d → ℤ) → Ω) (x₀ : d → ℝ) (r : ℝ) :
    ContDiff ℝ ∞ (latticeField S f sample x₀ r) :=
  ContDiff.sum (fun k hk => rescaled_smooth _ (hs _) _ _)

theorem localizedLatticeField_smooth (S : Finset (d → ℤ)) (f : Ω → (d → ℝ) → ℝ)
    (hs : ∀ sampleIndex, ContDiff ℝ ∞ (f sampleIndex)) (sample : (d → ℤ) → Ω) (x₀ : d → ℝ) (r h : ℝ) :
    ContDiff ℝ ∞ (localizedLatticeField S f sample x₀ r h) :=
  (rescaled_smooth _ quadraticPartition_smooth x₀ h).mul (latticeField_smooth S f hs sample x₀ r)

theorem finite_profile_derivative_bound (f : Ω → (d → ℝ) → ℝ)
    (hs : ∀ sampleIndex, ContDiff ℝ ∞ (f sampleIndex)) (hc : ∀ sampleIndex, HasCompactSupport (f sampleIndex)) (M : ℕ) :
    ∃ B > 0, ∀ sampleIndex j, j ≤ M → ∀ x, ‖iteratedFDeriv ℝ j (f sampleIndex) x‖ ≤ B := by
  have h (sampleIndex : Ω) := compact_smooth_derivatives_bounded (f sampleIndex) (hs sampleIndex) (hc sampleIndex) M
  choose b hb hbound using h
  have hs0 : 0 ≤ ∑ sampleIndex, b sampleIndex := Finset.sum_nonneg (fun sampleIndex hsampleIndex => (hb sampleIndex).le)
  refine ⟨1 + ∑ sampleIndex, b sampleIndex, by linarith, fun sampleIndex j hj x => ?_⟩
  have hle := Finset.single_le_sum (fun sampleIndex hsampleIndex => (hb sampleIndex).le) (Finset.mem_univ sampleIndex)
  exact (hbound sampleIndex j hj x).trans (hle.trans (by linarith))

theorem latticeField_scale_control (f : Ω → (d → ℝ) → ℝ)
    (hs : ∀ sampleIndex, ContDiff ℝ ∞ (f sampleIndex))
    (hbox : ∀ sampleIndex, tsupport (f sampleIndex) ⊆ Set.Icc (fun _ => -1) (fun _ => 1)) (M : ℕ) :
    ∃ C > 0, ∀ (S : Finset (d → ℤ)) (sample : (d → ℤ) → Ω) (x₀ : d → ℝ) (r : ℝ),
      0 < r → ScaleControl M r C (latticeField S f sample x₀ r) := by
  have hc (sampleIndex : Ω) : HasCompactSupport (f sampleIndex) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (hbox sampleIndex)
  obtain ⟨B, hB, hb⟩ := finite_profile_derivative_bound f hs hc M
  refine ⟨((3 : ℝ) ^ Fintype.card d) * B, by positivity, fun S sample x₀ r hr => ?_⟩
  refine ⟨latticeField_smooth S f hs sample x₀ r, hr, by positivity, ?_⟩
  have hh := derivative_scale_bounded_overlap S
    (fun k => rescaled (f (sample k)) (packetCenter x₀ r k) r)
    (fun k hk => rescaled_smooth _ (hs _) _ _) M (3 ^ Fintype.card d) B r hB.le hr
    (fun k hk j hj x => rescaled_derivative_bound _ (hs _) _ r hr j B hB.le (hb _ j hj) x)
    (cube_profile_overlap S (fun k => f (sample k)) (fun k => hbox _) x₀ r hr)
  simpa only [latticeField, Nat.cast_pow, Nat.cast_ofNat] using hh

theorem localizedLatticeField_scale_control (f : Ω → (d → ℝ) → ℝ)
    (hs : ∀ sampleIndex, ContDiff ℝ ∞ (f sampleIndex))
    (hbox : ∀ sampleIndex, tsupport (f sampleIndex) ⊆ Set.Icc (fun _ => -1) (fun _ => 1)) (M : ℕ) :
    ∃ C > 0, ∀ (S : Finset (d → ℤ)) (sample : (d → ℤ) → Ω) (x₀ : d → ℝ) (r h : ℝ),
      0 < r → r ≤ h → ScaleControl M r C (localizedLatticeField S f sample x₀ r h) := by
  obtain ⟨B, hB, hb⟩ := latticeField_scale_control f hs hbox M
  obtain ⟨A, hA, ha⟩ := compact_smooth_derivatives_bounded (quadraticPartition (d := d))
    quadraticPartition_smooth quadraticPartition_compact M
  refine ⟨(2 : ℝ) ^ M * A * B, by positivity, fun S sample x₀ r h hr hrh => ?_⟩
  have hh := hr.trans_le hrh
  have hg : ScaleControl M h A (coarseBump x₀ h) :=
    ⟨rescaled_smooth _ quadraticPartition_smooth _ _, hh, hA.le,
      fun j hj x => rescaled_derivative_bound _ quadraticPartition_smooth _ h hh j A hA.le (ha j hj) x⟩
  exact (hg.finer hr hrh).mul (hb S sample x₀ r hr) hr

theorem latticeField_amplitude_holder (f : Ω → (d → ℝ) → ℝ)
    (hs : ∀ sampleIndex, ContDiff ℝ ∞ (f sampleIndex))
    (hbox : ∀ sampleIndex, tsupport (f sampleIndex) ⊆ Set.Icc (fun _ => -1) (fun _ => 1))
    (m : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ C > 0, ∀ (S : Finset (d → ℤ)) (sample : (d → ℤ) → Ω) (x₀ : d → ℝ) (r c : ℝ),
      0 < r → r ≤ 1 → 0 ≤ c →
        HolderControl m θ (C * c) (fun x => (c * r ^ ((m : ℝ) + θ)) * latticeField S f sample x₀ r x) := by
  obtain ⟨C, hC, hb⟩ := latticeField_scale_control f hs hbox (m + 1)
  refine ⟨2 * C, by positivity, fun S sample x₀ r c hr hr1 hc => ?_⟩
  exact (hb S sample x₀ r hr).amplitude_holder hθ hθ1 hr hr1 c hc

end CausalLowerbound.PartC
