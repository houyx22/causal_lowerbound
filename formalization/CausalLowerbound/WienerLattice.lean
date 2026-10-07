import CausalLowerbound.WienerFourier
import Mathlib.Analysis.PSeries
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Uniform sums on anisotropic integer grids

Dividing an integer by a positive integer scale separates a coarse cell and
its finite residue. The number of residues is exactly canceled by the inverse
cell volume. Product decay will be supplied by mixed Fourier derivatives.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.Wiener

def decayKernel (x : ℝ) : ℝ := 1 / (1 + x ^ 2)

theorem decayKernel_nonneg (x : ℝ) : 0 ≤ decayKernel x := by
  unfold decayKernel; positivity

theorem decayKernel_summable : Summable (fun q : ℤ => decayKernel q) := by
  have hs := (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < (2 : ℕ))).update 0 1
  apply Summable.of_nonneg_of_le (fun q : ℤ => decayKernel_nonneg (q : ℝ)) _ hs
  intro q
  by_cases hq : q = 0
  · subst q; simp [decayKernel]
  · rw [Function.update_of_ne hq]
    exact one_div_le_one_div_of_le (sq_pos_of_ne_zero (by exact_mod_cast hq)) (by linarith)

theorem decayKernel_cell_bound (q s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    decayKernel (q + s) ≤ 3 * decayKernel q := by
  unfold decayKernel
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hs2 : s ^ 2 ≤ 1 := by nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs1)]
  nlinarith [sq_nonneg (q + s + s), sq_nonneg (q + s)]

def latticeConstant : ℝ := 3 * ∑' q : ℤ, decayKernel q

theorem latticeConstant_nonneg : 0 ≤ latticeConstant :=
  mul_nonneg (by norm_num) (tsum_nonneg fun q => decayKernel_nonneg q)

theorem decayKernel_residue_bound (N : ℕ) [NeZero N] (q : ℤ) (r : Fin N) :
    decayKernel (((q * (N : ℤ) + (r : ℕ) : ℤ) : ℝ) / N) ≤ 3 * decayKernel q := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hr0 : 0 ≤ (r : ℝ) / N := div_nonneg (by positivity) hN.le
  have hr1 : (r : ℝ) / N ≤ 1 := (div_le_one hN).mpr (by exact_mod_cast r.isLt.le)
  convert decayKernel_cell_bound (q : ℝ) ((r : ℝ) / N) hr0 hr1 using 1 <;>
    simp [add_div, mul_div_cancel_right₀ _ hN.ne']

theorem decayKernel_grid_summable (N : ℕ) [NeZero N] :
    Summable (fun k : ℤ => decayKernel ((k : ℝ) / N)) := by
  let e := Int.divModEquiv N
  have hs : Summable (fun p : ℤ × Fin N => 3 * decayKernel p.1) := by
    apply (summable_prod_of_nonneg
      (fun p : ℤ × Fin N => mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (decayKernel_nonneg p.1))).mpr
    refine ⟨fun _ => Summable.of_finite, ?_⟩
    simpa [tsum_fintype, mul_assoc] using (decayKernel_summable.mul_left (N * 3 : ℝ))
  have hmajor := hs.comp_injective e.injective
  apply Summable.of_nonneg_of_le (fun _ => decayKernel_nonneg _) _ hmajor
  intro k
  have h := decayKernel_residue_bound N (e k).1 (e k).2
  change decayKernel ((e.symm (e k) : ℤ) / (N : ℝ)) ≤ _ at h
  simpa using h

/-- The volume-normalized one-dimensional lattice sum is uniform in scale. -/
theorem decayKernel_grid_bound (N : ℕ) [NeZero N] :
    (∑' k : ℤ, decayKernel ((k : ℝ) / N)) ≤ (N : ℝ) * latticeConstant := by
  let e := Int.divModEquiv N
  have hs : Summable (fun p : ℤ × Fin N => 3 * decayKernel p.1) := by
    apply (summable_prod_of_nonneg
      (fun p : ℤ × Fin N => mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (decayKernel_nonneg p.1))).mpr
    refine ⟨fun _ => Summable.of_finite, ?_⟩
    simpa [tsum_fintype, mul_assoc] using (decayKernel_summable.mul_left (N * 3 : ℝ))
  calc
    _ = ∑' p : ℤ × Fin N, decayKernel ((e.symm p : ℤ) / (N : ℝ)) :=
      (e.symm.tsum_eq (fun k : ℤ => decayKernel ((k : ℝ) / N))).symm
    _ ≤ ∑' p : ℤ × Fin N, 3 * decayKernel p.1 := by
      apply Summable.tsum_le_tsum (fun p : ℤ × Fin N => decayKernel_residue_bound N p.1 p.2)
        ((decayKernel_grid_summable N).comp_injective e.symm.injective) hs
    _ = (N : ℝ) * latticeConstant := by
      rw [hs.tsum_prod' (fun _ => Summable.of_finite)]
      simp [tsum_fintype, latticeConstant, tsum_mul_left, mul_assoc, mul_comm, mul_left_comm]

variable {α : Type*} [Fintype α]

theorem finite_product_sum_bound (f : α → ℤ → ℝ) (hf : ∀ i k, 0 ≤ f i k)
    (hs : ∀ i, Summable (f i)) (s : Finset (α → ℤ)) :
    (∑ k ∈ s, ∏ i, f i (k i)) ≤ ∏ i, ∑' k, f i k := by
  classical
  let box : α → Finset ℤ := fun i => s.image (fun k => k i)
  have hsub : s ⊆ Fintype.piFinset box := by
    intro k hk
    exact Fintype.mem_piFinset.mpr (fun i => Finset.mem_image.mpr ⟨k, hk, rfl⟩)
  calc
    _ ≤ ∑ k ∈ Fintype.piFinset box, ∏ i, f i (k i) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => Finset.prod_nonneg (fun i _ => hf i _))
    _ = ∏ i, ∑ k ∈ box i, f i k := (Finset.prod_univ_sum box f).symm
    _ ≤ _ := Finset.prod_le_prod
      (fun i _ => Finset.sum_nonneg (fun k _ => hf i k))
      (fun i _ => (hs i).sum_le_tsum (box i) (fun k _ => hf i k))

theorem product_kernel_summable (f : α → ℤ → ℝ) (hf : ∀ i k, 0 ≤ f i k)
    (hs : ∀ i, Summable (f i)) : Summable (fun k : α → ℤ => ∏ i, f i (k i)) :=
  summable_of_sum_le (fun k => Finset.prod_nonneg (fun i _ => hf i _))
    (finite_product_sum_bound f hf hs)

theorem product_kernel_tsum_bound (f : α → ℤ → ℝ) (hf : ∀ i k, 0 ≤ f i k)
    (hs : ∀ i, Summable (f i)) :
    (∑' k : α → ℤ, ∏ i, f i (k i)) ≤ ∏ i, ∑' k, f i k :=
  (product_kernel_summable f hf hs).tsum_le_of_sum_le (finite_product_sum_bound f hf hs)

def normalizedKernel (N : ℕ) (k : ℤ) : ℝ := (N : ℝ)⁻¹ * decayKernel ((k : ℝ) / N)

theorem normalizedKernel_nonneg (N : ℕ) (k : ℤ) : 0 ≤ normalizedKernel N k :=
  mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N)) (decayKernel_nonneg _)

theorem normalizedKernel_summable (N : ℕ) [NeZero N] : Summable (normalizedKernel N) :=
  (decayKernel_grid_summable N).mul_left (N : ℝ)⁻¹

theorem normalizedKernel_tsum_bound (N : ℕ) [NeZero N] :
    (∑' k, normalizedKernel N k) ≤ latticeConstant := by
  simp only [normalizedKernel, tsum_mul_left]
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  calc
    _ ≤ (N : ℝ)⁻¹ * ((N : ℝ) * latticeConstant) :=
      mul_le_mul_of_nonneg_left (decayKernel_grid_bound N) (inv_nonneg.mpr (Nat.cast_nonneg N))
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]

def anisotropicKernel (N : α → ℕ) (k : α → ℤ) : ℝ := ∏ i, normalizedKernel (N i) (k i)

theorem anisotropicKernel_nonneg (N : α → ℕ) (k : α → ℤ) : 0 ≤ anisotropicKernel N k :=
  Finset.prod_nonneg (fun i _ => normalizedKernel_nonneg _ _)

theorem anisotropicKernel_summable (N : α → ℕ) (hN : ∀ i, N i ≠ 0) :
    Summable (anisotropicKernel N) := by
  apply product_kernel_summable (fun i k => normalizedKernel (N i) k)
    (fun i k => normalizedKernel_nonneg (N i) k)
  intro i
  letI : NeZero (N i) := ⟨hN i⟩
  exact normalizedKernel_summable (N i)

/-- Independent integer scales in every coordinate incur no scale-dependent
loss after multiplying by the inverse cell volume. -/
theorem anisotropicKernel_tsum_bound (N : α → ℕ) (hN : ∀ i, N i ≠ 0) :
    (∑' k, anisotropicKernel N k) ≤ latticeConstant ^ Fintype.card α := by
  have hs (i : α) : Summable (normalizedKernel (N i)) := by
    letI : NeZero (N i) := ⟨hN i⟩
    exact normalizedKernel_summable _
  calc
    _ ≤ ∏ i, ∑' k, normalizedKernel (N i) k :=
      product_kernel_tsum_bound (fun i k => normalizedKernel (N i) k)
        (fun i k => normalizedKernel_nonneg (N i) k) hs
    _ ≤ ∏ _i : α, latticeConstant := by
      apply Finset.prod_le_prod (fun i _ => tsum_nonneg (normalizedKernel_nonneg _))
      intro i _
      letI : NeZero (N i) := ⟨hN i⟩
      exact normalizedKernel_tsum_bound _
    _ = _ := by simp

theorem anisotropic_fourier_summable (N : α → ℕ) (hN : ∀ i, N i ≠ 0)
    (C : ℝ) (b : (α → ℤ) → ℂ) (hb : ∀ k, ‖b k‖ ≤ C * anisotropicKernel N k) :
    Summable (fun k => ‖b k‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb
    ((anisotropicKernel_summable N hN).mul_left C)

theorem anisotropic_fourier_bound (N : α → ℕ) (hN : ∀ i, N i ≠ 0)
    (C : ℝ) (hC : 0 ≤ C) (b : (α → ℤ) → ℂ)
    (hb : ∀ k, ‖b k‖ ≤ C * anisotropicKernel N k) :
    (∑' k, ‖b k‖) ≤ C * latticeConstant ^ Fintype.card α := by
  calc
    _ ≤ ∑' k, C * anisotropicKernel N k := Summable.tsum_le_tsum hb
      (anisotropic_fourier_summable N hN C b hb) ((anisotropicKernel_summable N hN).mul_left C)
    _ = C * ∑' k, anisotropicKernel N k := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (anisotropicKernel_tsum_bound N hN) hC

def fourierOfDecay (N : α → ℕ) (hN : ∀ i, N i ≠ 0)
    (C : ℝ) (b : (α → ℤ) → ℂ) (hb : ∀ k, ‖b k‖ ≤ C * anisotropicKernel N k) : Fourier α :=
  ⟨b, memℓp_gen (by simpa using anisotropic_fourier_summable N hN C b hb)⟩

theorem fourierOfDecay_bound (N : α → ℕ) (hN : ∀ i, N i ≠ 0)
    (C : ℝ) (hC : 0 ≤ C) (b : (α → ℤ) → ℂ)
    (hb : ∀ k, ‖b k‖ ≤ C * anisotropicKernel N k) :
    ‖fourierOfDecay N hN C b hb‖ ≤ C * latticeConstant ^ Fintype.card α := by
  rw [norm_eq_tsum]
  exact anisotropic_fourier_bound N hN C hC b hb

end CausalLowerbound.Wiener
