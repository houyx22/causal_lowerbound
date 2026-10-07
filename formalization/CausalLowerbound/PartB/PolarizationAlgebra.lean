import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A finite, real polarization stencil

The inclusion-exclusion version of polarization avoids choosing a Vandermonde
inverse. It applies in every finite degree, not just the cubic pilot degree.
All sums below are actual finite sums and all coefficients are explicit.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartB

namespace Polarization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def maskSign (b : ι → Bool) : ℝ := ∏ i, if b i then 1 else -1

def select (b : ι → Bool) (i : ι) : ℝ := if b i then 1 else 0

def flip (k : ι) (b : ι → Bool) : ι → Bool := Function.update b k (!(b k))

omit [Fintype ι] in
theorem flip_involutive (k : ι) : Function.Involutive (flip k) := by
  intro b
  funext i
  by_cases hi : i = k
  · subst i; simp [flip]
  · simp [flip, hi]

theorem maskSign_flip (k : ι) (b : ι → Bool) : maskSign (flip k b) = -maskSign b := by
  unfold maskSign
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  have h : (∏ i ∈ Finset.univ.erase k, if flip k b i then (1 : ℝ) else -1) =
      ∏ i ∈ Finset.univ.erase k, if b i then (1 : ℝ) else -1 := by
    apply Finset.prod_congr rfl
    intro i hi
    simp [flip, (Finset.mem_erase.mp hi).1]
  rw [h]
  cases hb : b k <;> simp [flip, hb]

theorem selector_sum (f : ι → ι) :
    (∑ b : ι → Bool, maskSign b * ∏ j, select b (f j)) =
      if Function.Bijective f then 1 else 0 := by
  classical
  by_cases hf : Function.Bijective f
  · rw [if_pos hf]
    have hp (b : ι → Bool) : (∏ j, select b (f j)) = ∏ i, select b i :=
      hf.prod_comp _
    simp_rw [hp, maskSign, select, ← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun (_ : ι) (v : Bool) =>
      (if v then (1 : ℝ) else -1) * (if v then 1 else 0))]
    simp [select, Fintype.sum_bool]
  · rw [if_neg hf]
    have hn : ¬ Function.Surjective f := fun hs => hf (Finite.surjective_iff_bijective.mp hs)
    obtain ⟨k, hk⟩ : ∃ k, ∀ j, f j ≠ k := by
      simpa only [Function.Surjective, not_forall, not_exists] using hn
    let e : (ι → Bool) ≃ (ι → Bool) :=
      ⟨flip k, flip k, flip_involutive k, flip_involutive k⟩
    have hp (b : ι → Bool) : (∏ j, select (flip k b) (f j)) = ∏ j, select b (f j) := by
      apply Finset.prod_congr rfl
      intro j _
      simp [select, flip, hk j]
    have he := e.sum_comp (fun b => maskSign b * ∏ j, select b (f j))
    change (∑ b, maskSign (flip k b) * ∏ j, select (flip k b) (f j)) = _ at he
    simp_rw [maskSign_flip, hp, neg_mul, Finset.sum_neg_distrib] at he
    linarith

/-- Ryser's inclusion-exclusion formula, with Boolean masks. Shared tensor
slots are handled by an actual sum over all permutations. -/
theorem ryser (M : ι → ι → ℝ) :
    (∑ b : ι → Bool, maskSign b * ∏ j, ∑ i, select b i * M i j) =
      ∑ σ : Equiv.Perm ι, ∏ j, M (σ j) j := by
  classical
  simp_rw [Fintype.prod_sum, Finset.mul_sum, Finset.prod_mul_distrib]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, selector_sum, ite_mul, one_mul, zero_mul,
    ← Finset.sum_filter]
  exact Finset.sum_bij
    (fun f h => Equiv.ofBijective f (Finset.mem_filter.mp h).2)
    (fun _ _ => Finset.mem_univ _)
    (fun _ _ _ _ h => by injection h)
    (fun σ _ => ⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, σ.bijective⟩,
      Equiv.coe_fn_injective rfl⟩)
    (fun _ _ => rfl)

/-- The symmetrized product, normalized by the exact number of permutations. -/
def symProduct {X : Type*} (w : ι → X → ℝ) (x : ι → X) : ℝ :=
  (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ * ∑ σ : Equiv.Perm ι, ∏ j, w (σ j) (x j)

theorem symProduct_eq_stencil {X : Type*} (w : ι → X → ℝ) (x : ι → X) :
    symProduct w x = (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ *
      ∑ b : ι → Bool, maskSign b * ∏ j, ∑ i, select b i * w i (x j) := by
  rw [ryser]
  rfl

omit [DecidableEq ι] in
theorem permute_product {X : Type*} (w : ι → X → ℝ) (x : ι → X)
    (σ : Equiv.Perm ι) :
    (∏ j, w (σ j) (x j)) = ∏ i, w i (x (σ.symm i)) := by
  simpa only [Equiv.symm_apply_apply] using
    (Equiv.prod_comp σ (fun i => w i (x (σ.symm i))))

/-- Multilinearity of the symmetrized product, in a form that exposes every
coefficient of the eventual positive-atom stencil. -/
theorem symProduct_mixture {X κ : Type*} [Fintype κ]
    (a : ι → κ → ℝ) (w : ι → κ → X → ℝ) (x : ι → X) :
    symProduct (fun i y => ∑ k, a i k * w i k y) x =
      ∑ b : ι → κ, (∏ i, a i (b i)) * symProduct (fun i => w i (b i)) x := by
  have hperm (v : ι → X → ℝ) : symProduct v x =
      (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm ι, ∏ i, v i (x (σ.symm i)) := by
    unfold symProduct
    simp_rw [permute_product v x]
  simp_rw [hperm]
  simp_rw [Fintype.prod_sum, Finset.prod_mul_distrib]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.mul_sum]
  ring

def maskMass (b : ι → Bool) : ℝ := ∑ i, select b i

omit [Fintype ι] [DecidableEq ι] in
theorem select_nonneg (b : ι → Bool) (i : ι) : 0 ≤ select b i := by
  cases h : b i <;> simp [select, h]

omit [DecidableEq ι] in
theorem maskMass_nonneg (b : ι → Bool) : 0 ≤ maskMass b :=
  Finset.sum_nonneg fun i _ => select_nonneg b i

omit [DecidableEq ι] in
theorem select_eq_zero_of_mass_zero {b : ι → Bool} (h : maskMass b = 0) (i : ι) :
    select b i = 0 := by
  have hi := Finset.single_le_sum (f := select b)
    (fun j _ => select_nonneg b j) (Finset.mem_univ i)
  change select b i ≤ maskMass b at hi
  exact le_antisymm (h ▸ hi) (select_nonneg b i)

def averageAtom {X : Type*} (f : ι → X → ℝ) (b : ι → Bool) (x : X) : ℝ :=
  if maskMass b = 0 then 1 else (maskMass b)⁻¹ * ∑ i, select b i * f i x

theorem mask_product_eq_average [Nonempty ι] {X : Type*}
    (f : ι → X → ℝ) (b : ι → Bool) (x : ι → X) :
    (∏ j, ∑ i, select b i * f i (x j)) =
      (maskMass b) ^ Fintype.card ι * ∏ j, averageAtom f b (x j) := by
  classical
  by_cases h : maskMass b = 0
  · simp [h, select_eq_zero_of_mass_zero h, averageAtom, Fintype.card_ne_zero]
  · have he (j : ι) : (∑ i, select b i * f i (x j)) =
        maskMass b * averageAtom f b (x j) := by
      simp [averageAtom, h, ← mul_assoc]
    simp_rw [he]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

def positiveWeight (b : ι → Bool) : ℝ :=
  (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ * maskSign b * (maskMass b) ^ Fintype.card ι

theorem symProduct_positive_stencil [Nonempty ι] {X : Type*}
    (f : ι → X → ℝ) (x : ι → X) :
    symProduct f x = ∑ b : ι → Bool, positiveWeight b * ∏ j, averageAtom f b (x j) := by
  rw [symProduct_eq_stencil, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [mask_product_eq_average]
  unfold positiveWeight
  ring

theorem averageAtom_bounds {X : Type*} (f : ι → X → ℝ) (b : ι → Bool)
    (η : ℝ) (hη : 0 ≤ η) (hf : ∀ i x, 1 - η ≤ f i x ∧ f i x ≤ 1 + η) (x : X) :
    1 - η ≤ averageAtom f b x ∧ averageAtom f b x ≤ 1 + η := by
  by_cases h : maskMass b = 0
  · simp only [averageAtom, if_pos h]; constructor <;> linarith
  · have hp : 0 < maskMass b := lt_of_le_of_ne (maskMass_nonneg b) (Ne.symm h)
    have hl : maskMass b * (1 - η) ≤ ∑ i, select b i * f i x := by
      rw [maskMass, Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hf i x).1 (select_nonneg b i)
    have hu : (∑ i, select b i * f i x) ≤ maskMass b * (1 + η) := by
      rw [maskMass, Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hf i x).2 (select_nonneg b i)
    simp only [averageAtom, if_neg h]
    constructor
    · calc
        1 - η = (maskMass b)⁻¹ * (maskMass b * (1 - η)) := by simp [← mul_assoc, h]
        _ ≤ _ := mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr hp.le)
    · calc
        _ ≤ (maskMass b)⁻¹ * (maskMass b * (1 + η)) :=
          mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr hp.le)
        _ = 1 + η := by simp [← mul_assoc, h]

/-- The two coefficients expressing `c + g` through `1` and `1 + θ*g`. -/
def affineCoefficient (c θ : ℝ) (b : Bool) : ℝ :=
  if b then θ⁻¹ else c - θ⁻¹

def affineDensity {X : Type*} (g : ι → X → ℝ) (θ : ℝ)
    (b : ι → Bool) (i : ι) (x : X) : ℝ :=
  if b i then 1 + θ * g i x else 1

def stencilAtom {X : Type*} (g : ι → X → ℝ) (θ : ℝ)
    (m : (ι → Bool) × (ι → Bool)) : X → ℝ :=
  averageAtom (affineDensity g θ m.1) m.2

/-- These are signed coefficients. Positivity refers to the density atoms. -/
def stencilWeight (c : ι → ℝ) (θ : ℝ) (m : (ι → Bool) × (ι → Bool)) : ℝ :=
  (∏ i, affineCoefficient (c i) θ (m.1 i)) * positiveWeight m.2

/-- Fully explicit positive-density polarization in every nonzero degree. -/
theorem positive_polarization [Nonempty ι] {X : Type*}
    (c : ι → ℝ) (g : ι → X → ℝ) (θ : ℝ) (hθ : θ ≠ 0) (x : ι → X) :
    symProduct (fun i y => c i + g i y) x =
      ∑ m : (ι → Bool) × (ι → Bool), stencilWeight c θ m *
        ∏ j, stencilAtom g θ m (x j) := by
  have h (i : ι) (y : X) : c i + g i y =
      ∑ b : Bool, affineCoefficient (c i) θ b * (if b then 1 + θ * g i y else 1) := by
    simp only [Fintype.sum_bool, affineCoefficient, Bool.true_eq, if_true, Bool.false_eq_true,
      if_false, mul_one]
    rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hθ, one_mul]
    ring
  conv_lhs => arg 1; ext i y; rw [h i y]
  rw [symProduct_mixture]
  simp_rw [symProduct_positive_stencil, Finset.mul_sum]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro p _
  simp only [stencilWeight, stencilAtom, affineDensity, mul_assoc]
  rfl

theorem stencilAtom_bounds {X : Type*} (g : ι → X → ℝ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hg : ∀ i x, |g i x| ≤ 1) (m : (ι → Bool) × (ι → Bool)) (x : X) :
    1 - θ ≤ stencilAtom g θ m x ∧ stencilAtom g θ m x ≤ 1 + θ := by
  apply averageAtom_bounds _ _ θ hθ
  intro i y
  have hb := abs_le.mp (hg i y)
  dsimp only [affineDensity]
  split_ifs
  · constructor
    · nlinarith [mul_nonneg hθ (by linarith : 0 ≤ g i y + 1)]
    · nlinarith [mul_nonneg hθ (by linarith : 0 ≤ 1 - g i y)]
  · constructor <;> linarith

def stencilBound (θ : ℝ) : ℝ :=
  (1 + 2 * |θ⁻¹|) ^ Fintype.card ι * ∑ b : ι → Bool, |positiveWeight b|

theorem stencilWeight_bound (c : ι → ℝ) (hc : ∀ i, |c i| ≤ 1) (θ : ℝ) :
    (∑ m : (ι → Bool) × (ι → Bool), |stencilWeight c θ m|) ≤
      stencilBound (ι := ι) θ := by
  classical
  have hα (i : ι) : (∑ b : Bool, |affineCoefficient (c i) θ b|) ≤ 1 + 2 * |θ⁻¹| := by
    simp only [Fintype.sum_bool, affineCoefficient, Bool.true_eq, if_true,
      Bool.false_eq_true, if_false]
    have h := abs_sub (c i) θ⁻¹
    linarith [hc i]
  have hp : (∑ b : ι → Bool, |∏ i, affineCoefficient (c i) θ (b i)|) ≤
      (1 + 2 * |θ⁻¹|) ^ Fintype.card ι := by
    simp_rw [Finset.abs_prod]
    rw [← Fintype.prod_sum (fun i b => |affineCoefficient (c i) θ b|)]
    calc
      _ ≤ ∏ _i : ι, (1 + 2 * |θ⁻¹|) :=
        Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun b _ => abs_nonneg _)
          (fun i _ => hα i)
      _ = _ := by simp
  simp only [stencilWeight, abs_mul, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right hp (Finset.sum_nonneg fun _ _ => abs_nonneg _)

end Polarization
end CausalLowerbound.PartB
