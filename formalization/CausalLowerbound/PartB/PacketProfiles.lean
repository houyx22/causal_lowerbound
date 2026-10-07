import CausalLowerbound.HolderScaling
import CausalLowerbound.PartB.QuadraticPartition
import CausalLowerbound.PartB.VirtualShift

/-! Actual smooth packet profiles, carrier coordinates, and uniform support
overlap. The coefficient law may be any fixed finite law; in particular it
may be the concrete small-grid law from MomentSupport. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ContDiff

namespace CausalLowerbound.PartB.ShellGeometry

variable {d Ω : Type*} [Fintype d] [DecidableEq d] [Fintype Ω]

/-- The physical carrier cube is [-2,2]^d in local scale-r coordinates.
The packet support [-1,1]^d sits in its compact middle subcube. -/
def carrierCoordinate (u : d → ℝ) : d → ℝ := fun i => u i / 4 + 1 / 2

theorem carrierCoordinate_smooth : ContDiff ℝ ∞ (carrierCoordinate (d := d)) := by
  apply contDiff_pi.mpr
  intro i
  exact ((contDiff_apply ℝ ℝ i).div_const 4).add contDiff_const

theorem carrierCoordinate_inner (u : d → ℝ)
    (hu : u ∈ Set.Icc (fun _ => -1) (fun _ => 1)) :
    carrierCoordinate u ∈ Set.Icc (fun _ => 1 / 4) (fun _ => 3 / 4) := by
  have hl (i : d) : (-1 : ℝ) ≤ u i := hu.1 i
  have hh (i : d) : u i ≤ (1 : ℝ) := hu.2 i
  constructor <;> intro i <;> change _ ≤ _ <;> dsimp [carrierCoordinate] <;> linarith [hl i, hh i]

theorem coefficientEvaluation_smooth {Q : ℕ} (U : CoefficientExponent d Q → ℝ) :
    ContDiff ℝ ∞ (coefficientEvaluation U) := by
  apply ContDiff.sum
  intro b _
  apply contDiff_const.mul
  apply contDiff_prod
  intro a _
  exact (contDiff_embedding a).pow _

def packetProfile {Q : ℕ} (U : CoefficientExponent d Q → ℝ) (u : d → ℝ) : ℝ :=
  quadraticPartition u * coefficientEvaluation U (carrierCoordinate u)

theorem packetProfile_smooth {Q : ℕ} (U : CoefficientExponent d Q → ℝ) :
    ContDiff ℝ ∞ (packetProfile U) :=
  quadraticPartition_smooth.mul ((coefficientEvaluation_smooth U).comp carrierCoordinate_smooth)

theorem packetProfile_compact {Q : ℕ} (U : CoefficientExponent d Q → ℝ) :
    HasCompactSupport (packetProfile U) := quadraticPartition_compact.mul_right

theorem packetProfile_support {Q : ℕ} (U : CoefficientExponent d Q → ℝ) :
    tsupport (packetProfile U) ⊆ Set.Icc (fun _ => -1) (fun _ => 1) :=
  tsupport_mul_subset_left.trans quadraticPartition_support

theorem finite_packetProfile_derivative_bound {Q : ℕ} (U : Ω → CoefficientExponent d Q → ℝ) (M : ℕ) :
    ∃ B > 0, ∀ sample j, j ≤ M → ∀ x, ‖iteratedFDeriv ℝ j (packetProfile (U sample)) x‖ ≤ B := by
  have h (sample : Ω) := compact_smooth_derivatives_bounded (packetProfile (U sample))
    (packetProfile_smooth _) (packetProfile_compact _) M
  choose b hb hbound using h
  have hs0 : 0 ≤ ∑ sample, b sample := Finset.sum_nonneg (fun sample _ => (hb sample).le)
  refine ⟨1 + ∑ sample, b sample, by linarith, ?_⟩
  intro sample j hj x
  have hs := Finset.single_le_sum (fun sample _ => (hb sample).le) (Finset.mem_univ sample)
  exact (hbound sample j hj x).trans (hs.trans (by linarith))

def packetCenter (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ) : d → ℝ :=
  fun i => x₀ i + r * k i

theorem packet_local_coordinate (x₀ : d → ℝ) (r : ℝ) (hr : r ≠ 0)
    (k : d → ℤ) (x : d → ℝ) :
    r⁻¹ • (x - packetCenter x₀ r k) = (fun i => (x i - x₀ i) / r - k i) := by
  funext i
  dsimp [packetCenter]
  field_simp
  ring

def closedLatticeNeighbors (x : d → ℝ) : Finset (d → ℤ) :=
  Fintype.piFinset (fun i => Finset.Icc (⌊x i⌋ - 1) (⌊x i⌋ + 1))

theorem closedLatticeNeighbors_card (x : d → ℝ) :
    (closedLatticeNeighbors x).card = 3 ^ Fintype.card d := by
  have hc (i : d) : (Finset.Icc (⌊x i⌋ - 1) (⌊x i⌋ + 1)).card = 3 := by
    rw [Int.card_Icc]
    have he : (⌊x i⌋ + 1 + 1 - (⌊x i⌋ - 1)) = (3 : ℤ) := by ring
    rw [he]
    rfl
  simp only [closedLatticeNeighbors, Fintype.card_piFinset, hc, Finset.prod_const,
    Finset.card_univ]

theorem rescaled_cube_support (f : (d → ℝ) → ℝ)
    (hfs : tsupport f ⊆ Set.Icc (fun _ => -1) (fun _ => 1))
    (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r) (k : d → ℤ) (x : d → ℝ)
    (hx : x ∈ tsupport (rescaled f (packetCenter x₀ r k) r)) :
    k ∈ closedLatticeNeighbors (fun i => (x i - x₀ i) / r) := by
  have hs : tsupport (rescaled f (packetCenter x₀ r k) r) ⊆
      (fun y => r⁻¹ • (y - packetCenter x₀ r k)) ⁻¹' Set.Icc (fun _ => -1) (fun _ => 1) := by
    apply closure_minimal
    · intro y hy
      exact hfs (subset_tsupport _ hy)
    · exact isClosed_Icc.preimage (continuous_const.smul (continuous_id.sub continuous_const))
  have hcoord := hs hx
  change r⁻¹ • (x - packetCenter x₀ r k) ∈ Set.Icc (fun _ : d => (-1 : ℝ)) (fun _ => 1) at hcoord
  rw [packet_local_coordinate x₀ r hr.ne'] at hcoord
  apply Fintype.mem_piFinset.mpr
  intro i
  let z := (x i - x₀ i) / r
  have hlo : (-1 : ℝ) ≤ z - k i := hcoord.1 i
  have hhi : z - k i ≤ (1 : ℝ) := hcoord.2 i
  have h₁ : (⌊z⌋ : ℝ) - 1 ≤ (k i : ℝ) := by linarith [Int.floor_le z]
  have h₂ : (k i : ℝ) < (⌊z⌋ : ℝ) + 2 := by linarith [Int.lt_floor_add_one z]
  have h₁' : ⌊z⌋ - 1 ≤ k i := by exact_mod_cast h₁
  have h₂' : k i < ⌊z⌋ + 2 := by exact_mod_cast h₂
  change k i ∈ Finset.Icc (⌊z⌋ - 1) (⌊z⌋ + 1)
  exact Finset.mem_Icc.mpr ⟨h₁', by omega⟩

theorem rescaled_packetProfile_support {Q : ℕ} (U : CoefficientExponent d Q → ℝ)
    (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r) (k : d → ℤ) (x : d → ℝ)
    (hx : x ∈ tsupport (rescaled (packetProfile U) (packetCenter x₀ r k) r)) :
    k ∈ closedLatticeNeighbors (fun i => (x i - x₀ i) / r) :=
  rescaled_cube_support _ (packetProfile_support U) x₀ r hr k x hx

theorem cube_profile_overlap (S : Finset (d → ℤ)) (f : (d → ℤ) → (d → ℝ) → ℝ)
    (hfs : ∀ k, tsupport (f k) ⊆ Set.Icc (fun _ => -1) (fun _ => 1))
    (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r) (x : d → ℝ) :
    ∃ T : Finset (d → ℤ), T ⊆ S ∧ T.card ≤ 3 ^ Fintype.card d ∧
      ∀ k ∈ S, x ∈ tsupport (rescaled (f k) (packetCenter x₀ r k) r) → k ∈ T := by
  classical
  let N := closedLatticeNeighbors (fun i => (x i - x₀ i) / r)
  refine ⟨S ∩ N, Finset.inter_subset_left, ?_, ?_⟩
  · exact (Finset.card_le_card Finset.inter_subset_right).trans_eq (closedLatticeNeighbors_card _)
  · intro k hk hx
    exact Finset.mem_inter.mpr ⟨hk, rescaled_cube_support _ (hfs k) x₀ r hr k x hx⟩

theorem packetProfile_overlap {Q : ℕ} (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r) (x : d → ℝ) :
    ∃ T : Finset (d → ℤ), T ⊆ S ∧ T.card ≤ 3 ^ Fintype.card d ∧
      ∀ k ∈ S, x ∈ tsupport (rescaled (packetProfile (U k)) (packetCenter x₀ r k) r) → k ∈ T := by
  classical
  let N := closedLatticeNeighbors (fun i => (x i - x₀ i) / r)
  refine ⟨S ∩ N, Finset.inter_subset_left, ?_, ?_⟩
  · exact (Finset.card_le_card Finset.inter_subset_right).trans_eq (closedLatticeNeighbors_card _)
  · intro k hk hx
    exact Finset.mem_inter.mpr ⟨hk, rescaled_packetProfile_support _ x₀ r hr k x hx⟩

/-- The normalized nuisance field P, before multiplying by a=c_a r^α. -/
def packetField {Q : ℕ} (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h : ℝ) (x : d → ℝ) : ℝ :=
  rescaled quadraticPartition x₀ h x *
    ∑ k ∈ S, rescaled (packetProfile (U k)) (packetCenter x₀ r k) r x

theorem packetField_smooth {Q : ℕ} (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h : ℝ) :
    ContDiff ℝ ∞ (packetField S U x₀ r h) := by
  apply (rescaled_smooth _ quadraticPartition_smooth x₀ h).mul
  apply ContDiff.sum
  intro k _
  exact rescaled_smooth _ (packetProfile_smooth _) _ r

/-- The constant is independent of the number of active packets and of all
coefficient draws from the fixed finite support. -/
theorem packetField_derivative_bound {Q : ℕ} (U : Ω → CoefficientExponent d Q → ℝ) (M : ℕ) :
    ∃ C > 0, ∀ (S : Finset (d → ℤ)) (sample : (d → ℤ) → Ω) (x₀ : d → ℝ) (r h : ℝ),
      0 < r → r ≤ h → ∀ j ≤ M, ∀ x,
      ‖iteratedFDeriv ℝ j (packetField S (fun k => U (sample k)) x₀ r h) x‖ ≤ C * r⁻¹ ^ j := by
  obtain ⟨A, hA, hAb⟩ := compact_smooth_derivatives_bounded (quadraticPartition (d := d))
    quadraticPartition_smooth quadraticPartition_compact M
  obtain ⟨B, hB, hBb⟩ := finite_packetProfile_derivative_bound U M
  let N := 3 ^ Fintype.card d
  refine ⟨(2 : ℝ) ^ M * A * ((N : ℝ) * B), by dsimp [N]; positivity, ?_⟩
  intro S sample x₀ r h hr hrh
  have hh : 0 < h := hr.trans_le hrh
  have hgb : ∀ j ≤ M, ∀ x, ‖iteratedFDeriv ℝ j (rescaled quadraticPartition x₀ h) x‖ ≤ A * r⁻¹ ^ j := by
    intro j hj x
    refine (rescaled_derivative_bound _ quadraticPartition_smooth x₀ h hh j A hA.le (hAb j hj) x).trans ?_
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (inv_nonneg.mpr hh.le) (inv_anti₀ hr hrh) j) hA.le
  have hsb := derivative_scale_bounded_overlap S
    (fun k => rescaled (packetProfile (U (sample k))) (packetCenter x₀ r k) r)
    (fun k _ => rescaled_smooth _ (packetProfile_smooth _) _ r) M N B r hB.le hr
    (fun k _ j hj x => rescaled_derivative_bound _ (packetProfile_smooth _) _ r hr j B hB.le
      (hBb (sample k) j hj) x)
    (packetProfile_overlap S (fun k => U (sample k)) x₀ r hr)
  exact derivative_scale_product _ _ (rescaled_smooth _ quadraticPartition_smooth x₀ h)
    (ContDiff.sum (fun k _ => rescaled_smooth _ (packetProfile_smooth _) _ r))
    M A ((N : ℝ) * B) r hA.le (by positivity) hr hgb hsb

theorem packetField_holder_bound {Q : ℕ} (U : Ω → CoefficientExponent d Q → ℝ)
    (m : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ C > 0, ∀ (S : Finset (d → ℤ)) (sample : (d → ℤ) → Ω) (x₀ : d → ℝ) (r h : ℝ),
      0 < r → r ≤ h → r ≤ 1 →
      HolderControl m θ (C * r ^ (-((m : ℝ) + θ))) (packetField S (fun k => U (sample k)) x₀ r h) := by
  obtain ⟨C, hC, hb⟩ := packetField_derivative_bound U (m + 1)
  refine ⟨2 * C, by positivity, ?_⟩
  intro S sample x₀ r h hr hrh hr1
  have hh := derivative_scale_holder _ (packetField_smooth S (fun k => U (sample k)) x₀ r h)
    m θ C r hθ hθ1 hC.le hr hr1 (hb S sample x₀ r h hr hrh)
  simpa only [Real.inv_rpow hr.le, ← Real.rpow_neg hr.le] using hh

def quarticProfile (x : d → ℝ) : ℝ := quadraticPartition x ^ 4

theorem quarticProfile_smooth : ContDiff ℝ ∞ (quarticProfile (d := d)) :=
  quadraticPartition_smooth.pow 4

theorem quarticProfile_support :
    tsupport (quarticProfile (d := d)) ⊆ Set.Icc (fun _ => -1) (fun _ => 1) := by
  apply Set.Subset.trans _ quadraticPartition_support
  apply closure_mono
  intro x hx
  change quadraticPartition x ≠ 0
  intro h
  exact hx (by simp [quarticProfile, h])

theorem quarticProfile_compact : HasCompactSupport (quarticProfile (d := d)) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure quarticProfile_support

def quarticField (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (x : d → ℝ) : ℝ :=
  ∑ k ∈ S, rescaled quarticProfile (packetCenter x₀ r k) r x

theorem quarticField_smooth (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) :
    ContDiff ℝ ∞ (quarticField S x₀ r) :=
  ContDiff.sum (fun k _ => rescaled_smooth _ quarticProfile_smooth _ r)

theorem quarticField_derivative_bound (M : ℕ) :
    ∃ C > 0, ∀ (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ), 0 < r →
      ∀ j ≤ M, ∀ x, ‖iteratedFDeriv ℝ j (quarticField S x₀ r) x‖ ≤ C * r⁻¹ ^ j := by
  obtain ⟨B, hB, hb⟩ := compact_smooth_derivatives_bounded (quarticProfile (d := d))
    quarticProfile_smooth quarticProfile_compact M
  refine ⟨((3 : ℝ) ^ Fintype.card d) * B, by positivity, ?_⟩
  intro S x₀ r hr
  have h := derivative_scale_bounded_overlap S
    (fun k => rescaled quarticProfile (packetCenter x₀ r k) r)
    (fun k _ => rescaled_smooth _ quarticProfile_smooth _ r)
    M (3 ^ Fintype.card d) B r hB.le hr
    (fun k _ j hj x => rescaled_derivative_bound _ quarticProfile_smooth _ r hr j B hB.le (hb j hj) x)
    (cube_profile_overlap S (fun _ => quarticProfile) (fun _ => quarticProfile_support) x₀ r hr)
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using h

end CausalLowerbound.PartB.ShellGeometry
