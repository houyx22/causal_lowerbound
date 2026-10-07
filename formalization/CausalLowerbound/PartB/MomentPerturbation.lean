import CausalLowerbound.FiniteBounds

/-!
# Positive finite-support moment perturbations

This proves the weight-perturbation step of `lem:moment-simplex`. A right inverse
of the augmented moment evaluation is supplied explicitly. Constructing the
unisolvent points in an arbitrarily small open ball is NOT proved in this file.
In particular this file does not replace that geometric/polynomial obligation
by a new axiom.
-/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.PartB

open scoped BigOperators

variable {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]

/-- Columns change one moment by one unit and preserve total mass.
Such columns can be obtained from an invertible augmented evaluation matrix. -/
structure MomentRightInverse (feature : I → Ω → ℝ) where
  coeff : Ω → I → ℝ
  mass : ∀ i, ∑ ω, coeff ω i = 0
  moment : ∀ i j, ∑ ω, coeff ω i * feature j ω = if i = j then 1 else 0

namespace MomentRightInverse

variable {feature : I → Ω → ℝ} (A : MomentRightInverse feature)

def adjustment (v : I → ℝ) (ω : Ω) : ℝ := ∑ i, v i * A.coeff ω i

theorem adjustment_mass (v : I → ℝ) : ∑ ω, A.adjustment v ω = 0 := by
  unfold adjustment
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, A.mass, mul_zero, Finset.sum_const_zero]

theorem adjustment_moment (v : I → ℝ) (j : I) :
    ∑ ω, A.adjustment v ω * feature j ω = v j := by
  simp only [adjustment, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, ← Finset.mul_sum, A.moment]
  simp

theorem adjustment_abs_le (v : I → ℝ) (δ : ℝ) (hv : ∀ i, |v i| ≤ δ) (ω : Ω) :
    |A.adjustment v ω| ≤ δ * ∑ i, |A.coeff ω i| := by
  calc
    _ ≤ ∑ i, |v i * A.coeff ω i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, δ * |A.coeff ω i| := Finset.sum_le_sum (fun i _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hv i) (abs_nonneg _))
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Preserve the same finite sample space while changing its probabilities. -/
def perturb (μ : FiniteLaw Ω) (v : I → ℝ)
    (hv : ∀ ω, |A.adjustment v ω| ≤ μ.weight ω / 2) : FiniteLaw Ω where
  weight ω := μ.weight ω + A.adjustment v ω
  nonneg ω := by
    have h := (abs_le.mp (hv ω)).1
    have hμ := μ.nonneg ω
    linarith
  total := by
    rw [Finset.sum_add_distrib, μ.total, A.adjustment_mass, add_zero]

theorem perturb_moment (μ : FiniteLaw Ω) (v : I → ℝ)
    (hv : ∀ ω, |A.adjustment v ω| ≤ μ.weight ω / 2) (j : I) :
    (A.perturb μ v hv).expect (feature j) = μ.expect (feature j) + v j := by
  simp only [FiniteLaw.expect, perturb, add_mul, Finset.sum_add_distrib,
    A.adjustment_moment]

theorem perturb_weight_lower (μ : FiniteLaw Ω) (v : I → ℝ)
    (hv : ∀ ω, |A.adjustment v ω| ≤ μ.weight ω / 2) (ω : Ω) :
    μ.weight ω / 2 ≤ (A.perturb μ v hv).weight ω := by
  change μ.weight ω / 2 ≤ μ.weight ω + A.adjustment v ω
  have h := (abs_le.mp (hv ω)).1
  linarith

/-- A quantitative interior radius, in coordinate maximum norm. -/
theorem exists_perturbation_of_bounds (μ : FiniteLaw Ω) (ε K : ℝ)
    (hε : 0 < ε) (hμ : ∀ ω, ε ≤ μ.weight ω)
    (hK : 0 < K) (hA : ∀ ω, ∑ i, |A.coeff ω i| ≤ K)
    (v : I → ℝ) (hv : ∀ i, |v i| ≤ ε / (2 * K)) :
    ∃ ν : FiniteLaw Ω, (∀ ω, 0 < ν.weight ω) ∧
      ∀ j, ν.expect (feature j) = μ.expect (feature j) + v j := by
  let δ := ε / (2 * K)
  have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hK)
  have hδK : δ * K = ε / 2 := by
    have he := div_mul_cancel₀ ε (ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 2) hK))
    dsimp [δ]
    nlinarith
  have hb : ∀ ω, |A.adjustment v ω| ≤ μ.weight ω / 2 := by
    intro ω
    calc
      _ ≤ δ * ∑ i, |A.coeff ω i| := A.adjustment_abs_le v δ hv ω
      _ ≤ δ * K := mul_le_mul_of_nonneg_left (hA ω) hδ.le
      _ = ε / 2 := hδK
      _ ≤ μ.weight ω / 2 := by linarith [hμ ω]
  refine ⟨A.perturb μ v hb, ?_, A.perturb_moment μ v hb⟩
  intro ω
  have hl := A.perturb_weight_lower μ v hb ω
  linarith [hμ ω]

end MomentRightInverse

private theorem finite_positive_margin {α : Type*} (s : Finset α) (w : α → ℝ)
    (hw : ∀ a ∈ s, 0 < w a) : ∃ ε : ℝ, 0 < ε ∧ ∀ a ∈ s, ε ≤ w a := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨ε, hε, hbound⟩ := ih (fun b hb => hw b (Finset.mem_insert_of_mem hb))
    refine ⟨min (w a) ε, lt_min (hw a (Finset.mem_insert_self _ _)) hε, ?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hbound b hb)

/-- Strictly positive baseline masses and a moment right inverse give a positive
radius in which every moment perturbation is realized on exactly the same atoms. -/
theorem exists_positive_moment_radius (feature : I → Ω → ℝ)
    (A : MomentRightInverse feature) (μ : FiniteLaw Ω)
    (hμ : ∀ ω, 0 < μ.weight ω) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v : I → ℝ, (∀ i, |v i| ≤ δ) →
      ∃ ν : FiniteLaw Ω, (∀ ω, 0 < ν.weight ω) ∧
        ∀ j, ν.expect (feature j) = μ.expect (feature j) + v j := by
  classical
  obtain ⟨ε, hε, hbound⟩ := finite_positive_margin Finset.univ μ.weight (fun ω _ => hμ ω)
  let K : ℝ := 1 + ∑ ω, ∑ i, |A.coeff ω i|
  have hsum : 0 ≤ ∑ ω, ∑ i, |A.coeff ω i| :=
    Finset.sum_nonneg (fun ω _ => Finset.sum_nonneg (fun i _ => abs_nonneg _))
  have hK : 0 < K := by dsimp [K]; linarith
  have hA : ∀ ω, ∑ i, |A.coeff ω i| ≤ K := by
    intro ω
    have he : (∑ i, |A.coeff ω i|) ≤ ∑ z, ∑ i, |A.coeff z i| :=
      Finset.single_le_sum (f := fun z => ∑ i, |A.coeff z i|)
        (fun z _ => Finset.sum_nonneg (fun i _ => abs_nonneg _))
        (Finset.mem_univ ω)
    dsimp [K]
    linarith
  refine ⟨ε / (2 * K), div_pos hε (mul_pos (by norm_num) hK), ?_⟩
  intro v hv
  exact A.exists_perturbation_of_bounds μ ε K hε (fun ω => hbound ω (Finset.mem_univ ω))
    hK hA v hv

end CausalLowerbound.PartB
