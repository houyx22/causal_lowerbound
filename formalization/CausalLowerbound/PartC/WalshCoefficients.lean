import CausalLowerbound.WienerSeries
import CausalLowerbound.PartB.BinaryExperiment
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.Fintype.Powerset

/-! Walsh coefficient arrays with their absolute coefficient norm. Evaluation
and coefficient projections are contractions, uniformly in the number of signs.
Arrays are retained as coefficients; equality is not defined by evaluation. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal

namespace CausalLowerbound.PartC.Walsh

variable {J : Type*}

abbrev Coefficients (J : Type*) := Wiener.Series (Finset J) ℝ

def character (S : Finset J) (ζ : J → Bool) : ℝ := ∏ j ∈ S, PartB.sign (ζ j)

@[simp] theorem character_empty (ζ : J → Bool) : character ∅ ζ = 1 := by
  simp [character]

@[simp] theorem abs_character (S : Finset J) (ζ : J → Bool) : |character S ζ| = 1 := by
  simp [character, Finset.abs_prod, PartB.abs_sign]

theorem character_congr (S : Finset J) (ζ ζ' : J → Bool)
    (h : ∀ j ∈ S, ζ j = ζ' j) : character S ζ = character S ζ' := by
  exact Finset.prod_congr rfl (fun j hj => congrArg PartB.sign (h j hj))

def evaluate (ζ : J → Bool) : Coefficients J →L[ℝ] ℝ :=
  Wiener.synthesis (fun S => character S ζ) 1 (fun S => by
    rw [Real.norm_eq_abs, abs_character])

theorem evaluate_apply (ζ : J → Bool) (a : Coefficients J) :
    evaluate ζ a = ∑' S, a S * character S ζ := rfl

theorem evaluate_bound (ζ : J → Bool) (a : Coefficients J) : |evaluate ζ a| ≤ ‖a‖ := by
  simpa only [one_mul] using Wiener.norm_synthesis (fun S => character S ζ) 1
    (fun S => by rw [Real.norm_eq_abs, abs_character]) a

variable [DecidableEq J]

@[simp] theorem evaluate_single (ζ : J → Bool) (S : Finset J) (c : ℝ) :
    evaluate ζ (lp.single 1 S c) = c * character S ζ :=
  Wiener.synthesis_single _ _ _ S c

/-- A bounded diagonal coefficient operator. -/
def multiplier (b : Finset J → ℝ) (hb : ∀ S, |b S| ≤ 1) :
    Coefficients J →L[ℝ] Coefficients J :=
  Wiener.synthesis (fun S => lp.single 1 S (b S)) 1 (fun S => by
    rw [lp.norm_single (by norm_num), Real.norm_eq_abs]
    exact hb S)

theorem multiplier_bound (b : Finset J → ℝ) (hb : ∀ S, |b S| ≤ 1)
    (a : Coefficients J) : ‖multiplier b hb a‖ ≤ ‖a‖ := by
  simpa only [one_mul] using Wiener.norm_synthesis (fun S =>
    (lp.single 1 S (b S) : Coefficients J)) 1
    (fun S => by rw [lp.norm_single (by norm_num), Real.norm_eq_abs]; exact hb S) a

theorem multiplier_apply (b : Finset J → ℝ) (hb : ∀ S, |b S| ≤ 1)
    (a : Coefficients J) (T : Finset J) : multiplier b hb a T = a T * b T := by
  change Wiener.entry T (Wiener.synthesis _ 1 _ a) = _
  rw [Wiener.synthesis_apply, (Wiener.entry T).map_tsum
    (Wiener.summable_synthesis _ 1 (fun S => by
      rw [lp.norm_single (by norm_num), Real.norm_eq_abs]; exact hb S) a)]
  simp only [map_smul, Wiener.entry_apply, lp.single_apply, Pi.single_apply, smul_eq_mul]
  rw [tsum_eq_single T]
  · simp
  · intro S hS
    simp [Ne.symm hS]

theorem multiplier_single (b : Finset J → ℝ) (hb : ∀ S, |b S| ≤ 1)
    (S : Finset J) (c : ℝ) : multiplier b hb (lp.single 1 S c) = lp.single 1 S (c * b S) := by
  rw [multiplier, Wiener.synthesis_single, ← lp.single_smul]
  rfl

def project (p : Finset J → Prop) [DecidablePred p] :
    Coefficients J →L[ℝ] Coefficients J :=
  multiplier (fun S => if p S then 1 else 0) (fun S => by
    dsimp only
    split_ifs <;> norm_num)

@[simp] theorem project_apply (p : Finset J → Prop) [DecidablePred p]
    (a : Coefficients J) (S : Finset J) : project p a S = if p S then a S else 0 := by
  rw [project, multiplier_apply]
  split_ifs <;> simp

theorem project_bound (p : Finset J → Prop) [DecidablePred p]
    (a : Coefficients J) : ‖project p a‖ ≤ ‖a‖ := multiplier_bound _ _ a

theorem project_single (p : Finset J → Prop) [DecidablePred p]
    (S : Finset J) (c : ℝ) : project p (lp.single 1 S c) =
      if p S then lp.single 1 S c else 0 := by
  rw [project, multiplier_single]
  split_ifs <;> simp

theorem project_add_compl (p : Finset J → Prop) [DecidablePred p]
    (a : Coefficients J) : project p a + project (fun S => ¬ p S) a = a := by
  ext S
  simp only [lp.coeFn_add, Pi.add_apply, project_apply]
  by_cases h : p S <;> simp [h]

theorem project_idempotent (p : Finset J → Prop) [DecidablePred p]
    (a : Coefficients J) : project p (project p a) = project p a := by
  ext S
  simp only [project_apply]
  split_ifs <;> rfl

variable {I : Type*} [Fintype I]

/-- The vector-valued coefficient norm still controls every moment coordinate
without a factor depending on the number of rough signs. -/
def evaluateCoordinate (ζ : J → Bool) (i : I) : (I → Coefficients J) →ₗ[ℝ] ℝ where
  toFun a := evaluate ζ (a i)
  map_add' a b := map_add (evaluate ζ) (a i) (b i)
  map_smul' c a := map_smul (evaluate ζ) c (a i)

omit [DecidableEq J] in
theorem evaluateCoordinate_bound (ζ : J → Bool) (i : I) (a : I → Coefficients J) :
    |evaluateCoordinate ζ i a| ≤ ‖a‖ :=
  (evaluate_bound ζ (a i)).trans (norm_le_pi_norm a i)

end CausalLowerbound.PartC.Walsh
