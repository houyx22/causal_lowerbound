import CausalLowerbound.PartB.PhysicalComponentFactorization

/-! Actual finite conditional experiments for fixed physical sites, with
uniform cell lower bounds inherited from the legal nuisance parameters. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace CausalLowerbound
variable {d : Type*} [Fintype d]

theorem NuisanceFields.conditionalLaw_lower (F : NuisanceFields d) {α β γ : Regularity}
    {Lπ L₀ Lτ κ : ℝ} (h : F.Legal α β γ Lπ L₀ Lτ κ) (hκ : 0 ≤ κ)
    (x : d → ℝ) (w : Bool × Bool) : κ ^ 2 ≤ (F.conditionalLaw h hκ x).weight w := by
  obtain ⟨hp0, hp1, hy0, hy1, ht0, ht1⟩ := h.2.2.2 x
  rcases w with ⟨R, T⟩
  rw [F.conditionalLaw_cell h hκ]
  cases R <;> cases T <;> simp only [Bool.false_eq_true, if_false, if_true, add_zero]
  · simpa only [pow_two] using mul_le_mul (by linarith : κ ≤ 1 - F.propensity x)
      (by linarith : κ ≤ 1 - F.baseline x) hκ (by linarith)
  · simpa only [pow_two] using mul_le_mul (by linarith : κ ≤ 1 - F.propensity x) hy0 hκ (by linarith)
  · simpa only [pow_two] using mul_le_mul hp0 (by linarith : κ ≤ 1 - (F.baseline x + F.effect x)) hκ (by linarith)
  · simpa only [pow_two] using mul_le_mul hp0 ht0 hκ (by linarith)

namespace PartB.ShellGeometry
open Wiener
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable [DecidableEq d] {Ω : Type*} [Fintype Ω] [Inhabited Ω]

theorem legal_model_propensity_abs {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h a b t δ : ℝ)
    {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}
    (hlegal : (modelFields side S U x₀ r h a b t δ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) (x : d → ℝ) : |a * packetField S U x₀ r h x| ≤ 1 := by
  have hp0 := (hlegal.2.2.2 x).1
  have hp1 := (hlegal.2.2.2 x).2.1
  change κ ≤ (1 + a * packetField S U x₀ r h x) / 2 at hp0
  change (1 + a * packetField S U x₀ r h x) / 2 ≤ 1 - κ at hp1
  rw [abs_le]
  constructor <;> linarith

theorem modelCellMass_abs_le_one {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h a b t δ : ℝ)
    (x : d → ℝ) (w : Bool × Bool) (z : S → Ω) {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}
    (hlegal : (modelFields side S (fun k => atoms (extendBlockSample S z k)) x₀ r h a b t δ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) : |modelCellMass side S atoms x₀ r h a b t δ x w z| ≤ 1 := by
  rw [modelCellMass_eq_conditional side S atoms x₀ r h a b t δ x w z hlegal hκ]
  rw [abs_of_nonneg (FiniteLaw.nonneg _ _)]
  exact FiniteLaw.weight_le_one _ _

def finitePhysicalConditional {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h a b t δ : ℝ)
    (μ : S → FiniteLaw Ω) {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}
    (hlegal : ∀ z : S → Ω,
      (modelFields side S (fun k => atoms (extendBlockSample S z k)) x₀ r h a b t δ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) {m : ℕ} (x : Fin m → d → ℝ) : FiniteLaw (Fin m → Bool × Bool) :=
  (FiniteLaw.independent μ).mixture (fun z => FiniteLaw.independent (fun i =>
    (modelFields side S (fun k => atoms (extendBlockSample S z k)) x₀ r h a b t δ).conditionalLaw
      (hlegal z) hκ (x i)))

theorem finitePhysicalConditional_weight {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h a b t δ : ℝ)
    (μ : S → FiniteLaw Ω) {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}
    (hlegal : ∀ z : S → Ω,
      (modelFields side S (fun k => atoms (extendBlockSample S z k)) x₀ r h a b t δ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) {m : ℕ} (x : Fin m → d → ℝ) (w : Fin m → Bool × Bool) :
    (finitePhysicalConditional side S atoms x₀ r h a b t δ μ hlegal hκ x).weight w =
      (FiniteLaw.independent μ).expect (fun z => ∏ i, modelCellMass side S atoms x₀ r h a b t δ (x i) (w i) z) := by
  change (FiniteLaw.independent μ).expect _ = _
  apply FiniteLaw.expect_congr
  intro z
  dsimp only [FiniteLaw.independent]
  apply Finset.prod_congr rfl
  intro i _
  exact (modelCellMass_eq_conditional side S atoms x₀ r h a b t δ (x i) (w i) z (hlegal z) hκ).symm

theorem finitePhysicalConditional_lower {Q : ℕ} (side : Bool) (S : Finset (d → ℤ))
    (atoms : Ω → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h a b t δ : ℝ)
    (μ : S → FiniteLaw Ω) {α β γ : Regularity} {Lπ L₀ Lτ κ : ℝ}
    (hlegal : ∀ z : S → Ω,
      (modelFields side S (fun k => atoms (extendBlockSample S z k)) x₀ r h a b t δ).Legal α β γ Lπ L₀ Lτ κ)
    (hκ : 0 ≤ κ) {m : ℕ} (x : Fin m → d → ℝ) (w : Fin m → Bool × Bool) :
    (κ ^ 2) ^ m ≤ (finitePhysicalConditional side S atoms x₀ r h a b t δ μ hlegal hκ x).weight w := by
  change (κ ^ 2) ^ m ≤ (FiniteLaw.independent μ).expect _
  rw [← (FiniteLaw.independent μ).expect_const ((κ ^ 2) ^ m)]
  apply FiniteLaw.expect_mono
  intro z
  change (κ ^ 2) ^ m ≤ ∏ i : Fin m, _
  have he : (κ ^ 2) ^ m = ∏ _i : Fin m, κ ^ 2 := by simp
  rw [he]
  apply Finset.prod_le_prod (fun _ _ => sq_nonneg κ)
  intro i _
  exact NuisanceFields.conditionalLaw_lower _ (hlegal z) hκ (x i) (w i)

end PartB.ShellGeometry
end CausalLowerbound
