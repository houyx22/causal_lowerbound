import CausalLowerbound.SmoothWindow
import CausalLowerbound.PartB.ShellGeometry

/-! An explicit smooth, compact quadratic partition of unity. A sine/cosine
transition makes the sum of squares exactly one without taking a square root
at the boundary of the support. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ContDiff

namespace CausalLowerbound.PartB
open Wiener

def quadraticWindow (x : ℝ) : ℝ :=
  Real.cos (Real.pi / 2 * Real.smoothTransition x) *
    Real.sin (Real.pi / 2 * Real.smoothTransition (x + 1))

theorem quadraticWindow_smooth : ContDiff ℝ ∞ quadraticWindow :=
  (Real.contDiff_cos.comp (contDiff_const.mul Real.smoothTransition.contDiff)).mul
    (Real.contDiff_sin.comp (contDiff_const.mul
      (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const))))

theorem quadraticWindow_left {x : ℝ} (hx : x ≤ -1) : quadraticWindow x = 0 := by
  simp [quadraticWindow, Real.smoothTransition.zero_of_nonpos (show x + 1 ≤ 0 by linarith)]

theorem quadraticWindow_right {x : ℝ} (hx : 1 ≤ x) : quadraticWindow x = 0 := by
  simp [quadraticWindow, Real.smoothTransition.one_of_one_le hx]

theorem quadraticWindow_support {x : ℝ} (hx : quadraticWindow x ≠ 0) : -1 < x ∧ x < 1 :=
  ⟨lt_of_not_ge (fun h => hx (quadraticWindow_left h)),
    lt_of_not_ge (fun h => hx (quadraticWindow_right h))⟩

theorem quadraticWindow_abs_le (x : ℝ) : |quadraticWindow x| ≤ 1 := by
  rw [quadraticWindow, abs_mul]
  exact (mul_le_mul (Real.abs_cos_le_one _) (Real.abs_sin_le_one _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem quadraticWindow_nonneg (x : ℝ) : 0 ≤ quadraticWindow x := by
  have hb (y : ℝ) : 0 ≤ Real.pi / 2 * Real.smoothTransition y ∧
      Real.pi / 2 * Real.smoothTransition y ≤ Real.pi / 2 := by
    constructor
    · exact mul_nonneg (by positivity) (Real.smoothTransition.nonneg y)
    · exact mul_le_of_le_one_right (by positivity) (Real.smoothTransition.le_one y)
  exact mul_nonneg
    (Real.cos_nonneg_of_mem_Icc ⟨by linarith [(hb x).1, Real.pi_pos], (hb x).2⟩)
    (Real.sin_nonneg_of_nonneg_of_le_pi (hb (x + 1)).1 (by linarith [(hb (x + 1)).2, Real.pi_pos]))

@[simp] theorem quadraticWindow_zero : quadraticWindow 0 = 1 := by
  norm_num [quadraticWindow, Real.smoothTransition.zero_of_nonpos (le_refl (0 : ℝ)),
    Real.smoothTransition.one_of_one_le (le_refl (1 : ℝ))]

theorem quadraticWindow_pair (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    quadraticWindow x ^ 2 + quadraticWindow (x - 1) ^ 2 = 1 := by
  have ha := Real.smoothTransition.one_of_one_le (show 1 ≤ x + 1 by linarith [hx.1])
  have hb := Real.smoothTransition.zero_of_nonpos (show x - 1 ≤ 0 by linarith [hx.2])
  simp only [quadraticWindow, sub_add_cancel, ha, hb, mul_one, mul_zero,
    Real.sin_pi_div_two, Real.cos_zero, one_mul]
  linarith [Real.sin_sq_add_cos_sq (Real.pi / 2 * Real.smoothTransition x)]

theorem quadraticWindow_integer_zero (x : ℝ) (hx : x ∈ Set.Icc 0 1) (k : ℤ)
    (hk : k ∉ ({0, -1} : Finset ℤ)) : quadraticWindow (x + k) = 0 := by
  have hk' : k ≠ 0 ∧ k ≠ -1 := by simpa using hk
  by_cases h : 0 ≤ k
  · have hi : (1 : ℝ) ≤ k := by exact_mod_cast (show (1 : ℤ) ≤ k by omega)
    exact quadraticWindow_right (by linarith [hx.1])
  · have hi : (k : ℝ) ≤ -2 := by exact_mod_cast (show k ≤ -2 by omega)
    exact quadraticWindow_left (by linarith [hx.2])

variable {d : Type*} [Fintype d]

def quadraticPartition (x : d → ℝ) : ℝ := ∏ i, quadraticWindow (x i)

theorem quadraticPartition_smooth : ContDiff ℝ ∞ (quadraticPartition (d := d)) := by
  apply contDiff_prod
  intro i _
  exact quadraticWindow_smooth.comp (contDiff_apply ℝ ℝ i)

theorem quadraticPartition_support :
    tsupport (quadraticPartition (d := d)) ⊆ Set.Icc (fun _ => -1) (fun _ => 1) := by
  classical
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have h (i : d) : quadraticWindow (x i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ i)
  exact ⟨fun i => (quadraticWindow_support (h i)).1.le,
    fun i => (quadraticWindow_support (h i)).2.le⟩

theorem quadraticPartition_compact : HasCompactSupport (quadraticPartition (d := d)) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure quadraticPartition_support

theorem quadraticPartition_abs_le (x : d → ℝ) : |quadraticPartition x| ≤ 1 := by
  rw [quadraticPartition, Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => quadraticWindow_abs_le _)

theorem quadraticPartition_nonneg (x : d → ℝ) : 0 ≤ quadraticPartition x :=
  Finset.prod_nonneg (fun _ _ => quadraticWindow_nonneg _)

@[simp] theorem quadraticPartition_zero : quadraticPartition (0 : d → ℝ) = 1 := by
  simp [quadraticPartition]

def quadraticPartitionSquare (x : d → ℝ) : ℂ := (quadraticPartition x ^ 2 : ℝ)

theorem quadraticPartitionSquare_prod (x : d → ℝ) :
    quadraticPartitionSquare x = ∏ i, ((quadraticWindow (x i) ^ 2 : ℝ) : ℂ) := by
  rw [quadraticPartitionSquare, quadraticPartition, ← Finset.prod_pow, Complex.ofReal_prod]

theorem quadraticPartition_sum_cube (x : d → ℝ) (hx : x ∈ Set.Icc 0 1) :
    periodize quadraticPartitionSquare (fun _ => 1) x = 1 := by
  classical
  let box : d → Finset ℤ := fun _ => {0, -1}
  have hz (k : d → ℤ) (hk : k ∉ Fintype.piFinset box) :
      quadraticPartitionSquare (latticeTranslate (fun _ => 1) k x) = 0 := by
    have hex : ∃ i, k i ∉ box i := by simpa only [Fintype.mem_piFinset, not_forall] using hk
    obtain ⟨i, hi⟩ := hex
    rw [quadraticPartitionSquare_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    have hi0 := quadraticWindow_integer_zero (x i) ⟨hx.1 i, hx.2 i⟩ (k i) hi
    simpa only [latticeTranslate, Nat.cast_one, one_mul, hi0, zero_pow (by decide : 2 ≠ 0),
      Complex.ofReal_zero] using (rfl : (0 : ℂ) = 0)
  rw [periodize, tsum_eq_sum hz]
  simp only [quadraticPartitionSquare_prod, latticeTranslate, Nat.cast_one, one_mul]
  rw [← Finset.prod_univ_sum box (fun i k => ((quadraticWindow (x i + k) ^ 2 : ℝ) : ℂ))]
  apply Finset.prod_eq_one
  intro i _
  simp only [box, Finset.sum_insert (by norm_num : (0 : ℤ) ∉ {-1}), Finset.sum_singleton,
    Int.cast_zero, add_zero, Int.cast_neg, Int.cast_one, ← Complex.ofReal_add]
  norm_num only [Int.cast_negSucc, Nat.cast_zero, zero_add]
  simpa only [sub_eq_add_neg, Complex.ofReal_add, Complex.ofReal_one] using
    congrArg Complex.ofReal (quadraticWindow_pair (x i) ⟨hx.1 i, hx.2 i⟩)

theorem quadraticPartition_periodize (x : d → ℝ) :
    periodize quadraticPartitionSquare (fun _ => 1) x = 1 := by
  let k : d → ℤ := fun i => -⌊x i⌋
  have hx : latticeTranslate (fun _ => 1) k x ∈ Set.Icc 0 1 := by
    constructor
    · intro i
      simp only [latticeTranslate, k, Nat.cast_one, one_mul, Int.cast_neg, Pi.zero_apply]
      linarith [Int.floor_le (x i)]
    · intro i
      simp only [latticeTranslate, k, Nat.cast_one, one_mul, Int.cast_neg, Pi.one_apply]
      linarith [Int.lt_floor_add_one (x i)]
  rw [← periodize_lattice_invariant quadraticPartitionSquare (fun _ => 1) k x]
  exact quadraticPartition_sum_cube _ hx

/-- The exact identity in `lem:partition`, in every finite dimension. -/
theorem quadraticPartition_sum_sq (x : d → ℝ) :
    (∑' k : d → ℤ, quadraticPartition (fun i => x i - k i) ^ 2) = 1 := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum, Complex.ofReal_one]
  have he := (Equiv.neg (d → ℤ)).tsum_eq
    (fun k => quadraticPartitionSquare (latticeTranslate (fun _ => 1) k x))
  have he' : (∑' k : d → ℤ, ((quadraticPartition (fun i => x i - k i) ^ 2 : ℝ) : ℂ)) =
      periodize quadraticPartitionSquare (fun _ => 1) x := by
    have ht (k : d → ℤ) : latticeTranslate (fun _ => 1) (-k) x =
        (fun i => x i - k i) := by
      funext i
      simp [latticeTranslate, sub_eq_add_neg]
    simpa only [periodize, quadraticPartitionSquare, Equiv.neg_apply, ht] using he
  rw [he', quadraticPartition_periodize]

/-- Physical packet bumps at scale r; the target bump G may be at a coarser scale. -/
def packet (G : (d → ℝ) → ℝ) (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ) (x : d → ℝ) : ℝ :=
  G x * quadraticPartition (fun i => (x i - x₀ i) / r - k i)

theorem packet_sum_sq (G : (d → ℝ) → ℝ) (x₀ : d → ℝ) (r : ℝ) (x : d → ℝ) :
    (∑' k : d → ℤ, packet G x₀ r k x ^ 2) = G x ^ 2 := by
  simp only [packet, mul_pow, tsum_mul_left]
  rw [quadraticPartition_sum_sq, mul_one]

theorem packet_smooth (G : (d → ℝ) → ℝ) (hG : ContDiff ℝ ∞ G)
    (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ) : ContDiff ℝ ∞ (packet G x₀ r k) := by
  apply hG.mul (quadraticPartition_smooth.comp _)
  apply contDiff_pi.mpr
  intro i
  exact (((contDiff_apply ℝ ℝ i).sub contDiff_const).div_const r).sub contDiff_const

def latticeNeighbors (x : d → ℝ) : Finset (d → ℤ) :=
  by classical exact Fintype.piFinset (fun i => {⌊x i⌋, ⌊x i⌋ + 1})

theorem quadraticPartition_zero_outside_neighbors (x : d → ℝ) (k : d → ℤ)
    (hk : k ∉ latticeNeighbors x) : quadraticPartition (fun i => x i - k i) = 0 := by
  classical
  by_contra hn
  apply hk
  apply Fintype.mem_piFinset.mpr
  intro i
  have hi := quadraticWindow_support ((Finset.prod_ne_zero_iff.mp hn) i (Finset.mem_univ i))
  dsimp only at hi
  have hlo : ⌊x i⌋ ≤ k i := by
    have hh : (⌊x i⌋ : ℝ) < (k i : ℝ) + 1 := by linarith [hi.2, Int.floor_le (x i)]
    have hh' : ⌊x i⌋ < k i + 1 := by exact_mod_cast hh
    omega
  have hhi : k i ≤ ⌊x i⌋ + 1 := by
    have hh : (k i : ℝ) < (⌊x i⌋ : ℝ) + 2 := by linarith [hi.1, Int.lt_floor_add_one (x i)]
    have hh' : k i < ⌊x i⌋ + 2 := by exact_mod_cast hh
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

theorem latticeNeighbors_card (x : d → ℝ) : (latticeNeighbors x).card = 2 ^ Fintype.card d := by
  classical
  simp [latticeNeighbors, Fintype.card_piFinset, Finset.card_pair]

theorem packet_finite_sum_sq (G : (d → ℝ) → ℝ) (x₀ : d → ℝ) (r : ℝ) (x : d → ℝ) :
    (∑ k ∈ latticeNeighbors (fun i => (x i - x₀ i) / r), packet G x₀ r k x ^ 2) = G x ^ 2 := by
  rw [← packet_sum_sq G x₀ r x]
  symm
  apply tsum_eq_sum
  intro k hk
  simp [packet, quadraticPartition_zero_outside_neighbors _ _ hk]

theorem packet_common_support_distance (G : (d → ℝ) → ℝ) (x₀ : d → ℝ)
    (r : ℝ) (hr : 0 < r) (k : d → ℤ) (x y : d → ℝ)
    (hx : packet G x₀ r k x ≠ 0) (hy : packet G x₀ r k y ≠ 0) :
    ‖x - y‖ ≤ 2 * r := by
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * r)).mpr
  intro i
  have hx' := quadraticWindow_support ((Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hx).2) i (Finset.mem_univ i))
  have hy' := quadraticWindow_support ((Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hy).2) i (Finset.mem_univ i))
  have hd : |(x i - x₀ i) / r - (y i - x₀ i) / r| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith [hx'.1, hx'.2, hy'.1, hy'.2]
  have he : (x i - x₀ i) / r - (y i - x₀ i) / r = (x i - y i) / r := by ring
  rw [he, abs_div, abs_of_pos hr] at hd
  exact (div_le_iff₀ hr).mp hd

end CausalLowerbound.PartB
