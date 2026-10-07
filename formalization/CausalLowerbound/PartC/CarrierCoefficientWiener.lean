import CausalLowerbound.PartC.AssignmentMultiplier
import CausalLowerbound.PartB.ActivePackets
import CausalLowerbound.CompactChartWiener
import CausalLowerbound.CompactPeriodizedFamily

/-! Uniform Wiener representatives of the actual coarse envelope in a
carrier chart. A fixed cutoff equals one wherever the assignment multiplier
is nonzero, and has compact support strictly inside the chart. -/

noncomputable section
set_option autoImplicit false
open scoped ContDiff BigOperators

namespace CausalLowerbound.PartC

open Wiener PartB PartB.ShellGeometry
variable {d : Type*} [Fintype d] [DecidableEq d]

def carrierCoefficientCutoff (v : d → ℝ) : ℝ :=
  assignmentPartition (1 / 4) (fun i => v i / 2)

theorem carrierCoefficientCutoff_smooth : ContDiff ℝ ∞ (carrierCoefficientCutoff (d := d)) :=
  (assignmentPartition_smooth (1 / 4)).comp
    (contDiff_pi.mpr (fun i => (contDiff_apply ℝ ℝ i).div_const 2))

theorem carrierCoefficientCutoff_support_point (v : d → ℝ) (hv : carrierCoefficientCutoff v ≠ 0) :
    v ∈ Set.Icc (fun _ => -(5 / 4)) (fun _ => 5 / 4) := by
  have h := assignmentPartition_support (d := d) (1 / 4) (by norm_num) (subset_tsupport _ hv)
  constructor <;> intro i
  · have hi := h.1 i
    dsimp at hi ⊢
    linarith
  · have hi := h.2 i
    dsimp at hi ⊢
    linarith

theorem carrierCoefficientCutoff_support : tsupport (carrierCoefficientCutoff (d := d)) ⊆
    Set.Icc (fun _ => -(5 / 4)) (fun _ => 5 / 4) :=
  closure_minimal (fun v hv => carrierCoefficientCutoff_support_point v hv) isClosed_Icc

theorem carrierCoefficientCutoff_compact : HasCompactSupport (carrierCoefficientCutoff (d := d)) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure carrierCoefficientCutoff_support

theorem carrierCoefficientCutoff_one (v : d → ℝ)
    (hv : v ∈ Set.Icc (fun _ => -(3 / 4)) (fun _ => 3 / 4)) : carrierCoefficientCutoff v = 1 := by
  apply assignmentPartition_plateau (1 / 4) (by norm_num)
  constructor <;> intro i
  · have hi := hv.1 i
    dsimp at hi ⊢
    linarith
  · have hi := hv.2 i
    dsimp at hi ⊢
    linarith

theorem carrierCoefficientCutoff_on_assignment (c w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1 / 2)
    (v : d → ℝ) (hv : assignmentMultiplier c w v ≠ 0) : carrierCoefficientCutoff v = 1 := by
  apply carrierCoefficientCutoff_one
  have h := assignmentPartition_support w hw
    (assignmentMultiplier_support c w (subset_tsupport _ hv))
  constructor <;> intro i
  · have hi := h.1 i
    dsimp at hi ⊢
    linarith
  · have hi := h.2 i
    dsimp at hi ⊢
    linarith

def localizedCoarsePower (q : ℕ) (p : (ℝ × (d → ℝ)) × (d → ℝ)) : ℂ :=
  (carrierCoefficientCutoff p.2 * quadraticPartition (fun i => p.1.2 i + p.1.1 * p.2 i) ^ q : ℝ)

theorem localizedCoarsePower_smooth (q : ℕ) : ContDiff ℝ ∞ (localizedCoarsePower (d := d) q) := by
  apply Complex.ofRealCLM.contDiff.comp
  apply (carrierCoefficientCutoff_smooth.comp contDiff_snd).mul
  apply ContDiff.pow
  apply quadraticPartition_smooth.comp
  apply contDiff_pi.mpr
  intro i
  exact ((contDiff_apply ℝ ℝ i).comp (contDiff_snd.comp contDiff_fst)).add
    ((contDiff_fst.comp contDiff_fst).mul ((contDiff_apply ℝ ℝ i).comp contDiff_snd))

theorem localizedCoarsePower_support (q : ℕ) (p : ℝ × (d → ℝ)) :
    tsupport (fun v => localizedCoarsePower q (p, v)) ⊆
      Set.Icc (fun _ => -(5 / 4)) (fun _ => 5 / 4) := by
  apply closure_minimal _ isClosed_Icc
  intro v hv
  apply carrierCoefficientCutoff_support_point v
  intro h
  exact hv (by simp [localizedCoarsePower, h])

theorem exists_localizedCoarsePower_wiener (q : ℕ) :
    ∃ C ≥ 0, ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (fun _ : d => (-3 : ℝ)) (fun _ => 3),
      ∃ A : Fourier d, ‖A‖ ≤ C ∧ (∀ x, (toContinuous A x).im = 0) ∧
        ∀ u ∈ Set.Icc (0 : d → ℝ) 1,
          toContinuous A (torusProjection u) = localizedCoarsePower q ((s, y), fun i => 4 * u i - 2) := by
  let Kp : Set (ℝ × (d → ℝ)) := Set.Icc 0 1 ×ˢ Set.Icc (fun _ => -3) (fun _ => 3)
  let Kx : Set (d → ℝ) := Set.Icc (fun _ => -(5 / 4)) (fun _ => 5 / 4)
  obtain ⟨C, hC, hb⟩ := compact_family_periodized_wiener (localizedCoarsePower (d := d) q) Kp Kx
    (isCompact_Icc.prod isCompact_Icc) isCompact_Icc
    (fun p _ => localizedCoarsePower_support q p) (fun p _ x _ => (localizedCoarsePower_smooth q).contDiffAt)
  refine ⟨C, hC, fun s hs y hy => ?_⟩
  obtain ⟨B, hB, hn⟩ := hb (s, y) ⟨hs, hy⟩ (fun _ => 4) (by simp)
  let f : (d → ℝ) → ℂ := fun v => localizedCoarsePower q ((s, y), v)
  have hf : HasCompactSupport f :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (localizedCoarsePower_support q (s, y))
  have hsmooth : ContDiff ℝ ∞ f := (localizedCoarsePower_smooth q).comp (contDiff_const.prodMk contDiff_id)
  let A := compactChartWiener f hf hsmooth
  have he : periodizedWiener f hf (hsmooth.of_le (WithTop.coe_le_coe.mpr le_top))
      (fun _ => 4) (by simp) = B := by
    apply toContinuous_injective
    apply ContinuousMap.ext
    intro x
    rw [periodizedWiener_value, hB]
  refine ⟨A, ?_, ?_, ?_⟩
  · simpa only [A, compactChartWiener, spatialShift_norm, he] using hn
  · intro x
    simp only [A, compactChartWiener, spatialShift_value, periodizedWiener_value,
      periodizedTorus, periodize, f, localizedCoarsePower, ← Complex.ofReal_tsum, Complex.ofReal_im]
  · intro u hu
    apply compactChartWiener_value f hf hsmooth _ u hu
    intro v hv i
    have hcut : carrierCoefficientCutoff v ≠ 0 := by
      intro h
      exact hv (by simp [f, localizedCoarsePower, h])
    have hh := carrierCoefficientCutoff_support_point v hcut
    have h0 := hh.1 i
    have h1 := hh.2 i
    dsimp at h0 h1
    exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem activeCarrier_normalized_center (r h : ℝ) (hr : 0 < r) (hrh : r ≤ h)
    (k : activeBlocks (d := d) r h) :
    (fun i => (r / h) * (k.val i : ℝ)) ∈ Set.Icc (fun _ => -3) (fun _ => 3) := by
  have hh : 0 < h := hr.trans_le hrh
  have hs : 0 ≤ r / h := div_nonneg hr.le hh.le
  have hs1 : r / h ≤ 1 := (div_le_one hh).mpr hrh
  have he : r / h * (h / r + 2) = 1 + 2 * (r / h) := by field_simp; ring
  have hi (i : d) : |r / h * (k.val i : ℝ)| ≤ 3 := by
    have hk := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp k.property i)
    have hk' : |(k.val i : ℝ)| ≤ (⌈h / r + 1⌉ : ℤ) := abs_le.mpr
      ⟨by exact_mod_cast hk.1, by exact_mod_cast hk.2⟩
    have hceil : ((⌈h / r + 1⌉ : ℤ) : ℝ) ≤ h / r + 2 := by linarith [Int.ceil_lt_add_one (h / r + 1)]
    calc
      _ = (r / h) * |(k.val i : ℝ)| := by rw [abs_mul, abs_of_nonneg hs]
      _ ≤ (r / h) * (h / r + 2) := mul_le_mul_of_nonneg_left (hk'.trans hceil) hs
      _ ≤ 3 := by rw [he]; linarith
  exact ⟨fun i => (abs_le.mp (hi i)).1, fun i => (abs_le.mp (hi i)).2⟩

theorem coarseBump_in_carrier_chart (x₀ : d → ℝ) (r h : ℝ) (k : d → ℤ) (u : d → ℝ) :
    coarseBump x₀ h (fun i => x₀ i + r * (k i + 4 * u i - 2)) =
      quadraticPartition (fun i => (r / h) * k i + (r / h) * (4 * u i - 2)) := by
  unfold coarseBump rescaled
  congr 1
  funext i
  dsimp
  ring

theorem exists_carrier_coarsePower_wiener (q : ℕ) :
    ∃ C ≥ 0, ∀ (x₀ : d → ℝ) (r h : ℝ), 0 < r → r ≤ h →
      ∀ k : activeBlocks (d := d) r h, ∃ A : Fourier d, ‖A‖ ≤ C ∧
        (∀ x, (toContinuous A x).im = 0) ∧
        ∀ u ∈ Set.Icc (0 : d → ℝ) 1,
          toContinuous A (torusProjection u) =
            (carrierCoefficientCutoff (fun i => 4 * u i - 2) *
              coarseBump x₀ h (fun i => x₀ i + r * (k.val i + 4 * u i - 2)) ^ q : ℝ) := by
  obtain ⟨C, hC, hb⟩ := exists_localizedCoarsePower_wiener (d := d) q
  refine ⟨C, hC, fun x₀ r h hr hrh k => ?_⟩
  have hh : 0 < h := hr.trans_le hrh
  obtain ⟨A, hn, hre, hvalue⟩ := hb (r / h) ⟨div_nonneg hr.le hh.le, (div_le_one hh).mpr hrh⟩
    _ (activeCarrier_normalized_center r h hr hrh k)
  refine ⟨A, hn, hre, fun u hu => ?_⟩
  rw [hvalue u hu, coarseBump_in_carrier_chart]
  rfl

end CausalLowerbound.PartC
