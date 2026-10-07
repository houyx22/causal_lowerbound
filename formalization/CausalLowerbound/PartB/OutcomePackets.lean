import CausalLowerbound.PartB.PacketAmplitudes
import CausalLowerbound.ScaleControl

/-! The full cubic regression and its interaction with the target, with
uniform derivative bounds for every actual coefficient draw. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators ContDiff
namespace CausalLowerbound.PartB.ShellGeometry
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [Fintype Ω]

def packetEta (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r h a t : ℝ) (x : d → ℝ) : ℝ :=
  (a ^ 2 * t ^ 2 / 3) * (coarseBump x₀ h x ^ 2 * (3 - 2 * quarticField S x₀ r x))

def normalizedCubic {Q : ℕ} (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h a t : ℝ) (x : d → ℝ) : ℝ :=
  (1 + packetEta S x₀ r h a t x) * packetField S U x₀ r h x -
    (a ^ 2 / 3) * packetField S U x₀ r h x ^ 3

def normalizedPOutcome {Q : ℕ} (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h a t : ℝ) (x : d → ℝ) : ℝ :=
  normalizedCubic S U x₀ r h a t x -
    (2 * a ^ 2 * t ^ 2) * (coarseBump x₀ h x ^ 2 * packetField S U x₀ r h x)

theorem normalizedCubic_eq {Q : ℕ} (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h a b t : ℝ) (ha : a ≠ 0)
    (x : d → ℝ) :
    b * normalizedCubic S U x₀ r h a t x =
      (b / a) * ((1 + packetEta S x₀ r h a t x) * propensityPerturbation S U x₀ r h a x -
        propensityPerturbation S U x₀ r h a x ^ 3 / 3) := by
  simp only [normalizedCubic, propensityPerturbation]
  field_simp
  ring

theorem normalizedPOutcome_eq {Q : ℕ} (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h a b t δ : ℝ)
    (hδ : δ = a * b * t ^ 2) (x : d → ℝ) :
    b * normalizedPOutcome S U x₀ r h a t x - targetField x₀ h δ x =
      b * normalizedCubic S U x₀ r h a t x -
        targetField x₀ h δ x * (1 + 2 * propensityPerturbation S U x₀ r h a x) := by
  simp only [normalizedPOutcome, targetField, propensityPerturbation, hδ]
  ring

theorem outcomePacket_scale_control {Q : ℕ} (U : Ω → CoefficientExponent d Q → ℝ) (M : ℕ) :
    ∃ C > 0, ∀ (S : Finset (d → ℤ)) (sample : (d → ℤ) → Ω)
      (x₀ : d → ℝ) (r h a t : ℝ), 0 < r → r ≤ h → 0 ≤ a → a ≤ 1 → 0 ≤ t → t ≤ 1 →
      ScaleControl M r C (normalizedCubic S (fun k => U (sample k)) x₀ r h a t) ∧
      ScaleControl M r C (normalizedPOutcome S (fun k => U (sample k)) x₀ r h a t) := by
  obtain ⟨A, hA, hAp⟩ := packetField_derivative_bound U M
  obtain ⟨B, hB, hBq⟩ := quarticField_derivative_bound (d := d) M
  obtain ⟨D, hD, hDg⟩ := compact_smooth_derivatives_bounded (targetProfile (d := d))
    targetProfile_smooth targetProfile_compact M
  let Eη := (2 : ℝ) ^ M * D * (3 + 2 * B)
  let E₃ := (2 : ℝ) ^ M * ((2 : ℝ) ^ M * A * A) * A
  let Eκ := (2 : ℝ) ^ M * (1 + Eη) * A + E₃
  let Ex := 2 * ((2 : ℝ) ^ M * D * A)
  have heη : 0 < Eη := by dsimp [Eη]; positivity
  have he₃ : 0 < E₃ := by dsimp [E₃]; positivity
  have heκ : 0 < Eκ := by dsimp [Eκ]; positivity
  have hex : 0 < Ex := by dsimp [Ex]; positivity
  refine ⟨Eκ + Ex, add_pos heκ hex, ?_⟩
  intro S sample x₀ r h a t hr hrh ha ha1 ht ht1
  have hh := hr.trans_le hrh
  have hp : ScaleControl M r A (packetField S (fun k => U (sample k)) x₀ r h) :=
    ⟨packetField_smooth _ _ _ _ _, hr, hA.le, hAp S sample x₀ r h hr hrh⟩
  have hq : ScaleControl M r B (quarticField S x₀ r) :=
    ⟨quarticField_smooth _ _ _, hr, hB.le, hBq S x₀ r hr⟩
  have hg : ScaleControl M r D (fun x => coarseBump x₀ h x ^ 2) := by
    have hg' : ScaleControl M h D (rescaled targetProfile x₀ h) :=
      ⟨rescaled_smooth _ targetProfile_smooth _ _, hh, hD.le,
        fun j hj x => rescaled_derivative_bound _ targetProfile_smooth _ _ hh j D hD.le (hDg j hj) x⟩
    exact hg'.finer hr hrh
  have hc (c : ℝ) : ScaleControl M r |c| (fun _ : d → ℝ => c) := ScaleControl.const M r c hr
  have ha2 : a ^ 2 ≤ 1 := by nlinarith
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have hat : a ^ 2 * t ^ 2 ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul ha2 ht2 (sq_nonneg _) (by norm_num)
      _ = 1 := one_mul 1
  have hη : ScaleControl M r Eη (packetEta S x₀ r h a t) := by
    have hb' := (hc 3).sub (hq.smul 2)
    have he := (hg.mul hb' hr).smul_le (a ^ 2 * t ^ 2 / 3) 1
      (by rw [abs_of_nonneg (by positivity)]; linarith)
    simpa only [packetEta, Eη, abs_of_pos (by norm_num : (0 : ℝ) < 3),
      abs_of_pos (by norm_num : (0 : ℝ) < 2), one_mul] using he
  have hp3 : ScaleControl M r E₃ (fun x => packetField S (fun k => U (sample k)) x₀ r h x ^ 3) := by
    convert (hp.mul hp hr).mul hp hr using 1
    funext x; ring
  have hcub : ScaleControl M r Eκ (normalizedCubic S (fun k => U (sample k)) x₀ r h a t) := by
    have he := ((hc 1).add hη).mul hp hr
    have h3 := hp3.smul_le (a ^ 2 / 3) 1 (by rw [abs_of_nonneg (by positivity)]; linarith)
    simpa only [normalizedCubic, Eκ, abs_one, one_mul] using he.sub h3
  have hcross : ScaleControl M r Ex (fun x => (2 * a ^ 2 * t ^ 2) *
      (coarseBump x₀ h x ^ 2 * packetField S (fun k => U (sample k)) x₀ r h x)) := by
    exact (hg.mul hp hr).smul_le _ 2 (by rw [abs_of_nonneg (by positivity)]; nlinarith)
  exact ⟨hcub.mono (le_add_of_nonneg_right hex.le), hcub.sub hcross⟩

/-- The infinite periodic fourth-power sum agrees with the active-block
version wherever the coarse envelope is nonzero. -/
theorem weighted_quarticField_eq (x₀ : d → ℝ) (r h : ℝ) (hr : 0 < r) (hh : 0 < h) (x : d → ℝ) :
    coarseBump x₀ h x ^ 2 * quarticField (activeBlocks r h) x₀ r x =
      coarseBump x₀ h x ^ 2 *
        ∑' k : d → ℤ, quadraticPartition (fun i => (x i - x₀ i) / r - k i) ^ 4 := by
  by_cases hg : coarseBump x₀ h x = 0
  · simp [hg]
  · congr 1
    rw [quarticField]
    have he (k : d → ℤ) : rescaled quarticProfile (packetCenter x₀ r k) r x =
        quadraticPartition (fun i => (x i - x₀ i) / r - k i) ^ 4 := by
      simp only [rescaled, quarticProfile, packet_local_coordinate x₀ r hr.ne']
    simp_rw [he]
    symm
    apply tsum_eq_sum
    intro k hk
    have hz := packet_zero_outside_active x₀ r h hr hh k hk x
    have hφ := (mul_eq_zero.mp hz).resolve_left hg
    simp only [hφ, zero_pow (by decide : 4 ≠ 0)]
end CausalLowerbound.PartB.ShellGeometry
