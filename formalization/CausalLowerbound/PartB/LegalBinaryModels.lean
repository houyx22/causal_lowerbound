import CausalLowerbound.PartB.NuisanceLegality
import CausalLowerbound.PartB.BinaryExperiment

/-! Connect the proved physical parameter constraints to the actual
Bernoulli experiment already used by the local moment bridges. -/
noncomputable section
set_option autoImplicit false
namespace CausalLowerbound
variable {d : Type*} [Fintype d]

theorem NuisanceFields.Legal.binaryLegal {F : NuisanceFields d} {α β γ : Regularity}
    {Lπ L₀ Lτ κ : ℝ} (h : F.Legal α β γ Lπ L₀ Lτ κ) (hκ : 0 ≤ κ) (x : d → ℝ) :
    PartB.BinaryLegal (2 * F.propensity x - 1) (2 * F.baseline x - 1) (F.effect x) := by
  obtain ⟨hp0, hp1, hm0, hm1, ht0, ht1⟩ := h.2.2.2 x
  constructor
  · apply abs_le.mpr; constructor <;> linarith
  · intro r
    cases r <;> simp only [PartB.sign] <;> apply abs_le.mpr <;> constructor <;> linarith

def NuisanceFields.conditionalLaw (F : NuisanceFields d) {α β γ : Regularity}
    {Lπ L₀ Lτ κ : ℝ} (h : F.Legal α β γ Lπ L₀ Lτ κ) (hκ : 0 ≤ κ) (x : d → ℝ) : FiniteLaw (Bool × Bool) :=
  PartB.binaryLaw _ _ _ (h.binaryLegal hκ x)

theorem NuisanceFields.conditionalLaw_cell (F : NuisanceFields d) {α β γ : Regularity}
    {Lπ L₀ Lτ κ : ℝ} (h : F.Legal α β γ Lπ L₀ Lτ κ) (hκ : 0 ≤ κ) (x : d → ℝ) (r t : Bool) :
    (F.conditionalLaw h hκ x).weight (r, t) =
      (if r then F.propensity x else 1 - F.propensity x) *
        (if t then F.baseline x + (if r then F.effect x else 0)
          else 1 - (F.baseline x + (if r then F.effect x else 0))) := by
  cases r <;> cases t <;>
    simp only [conditionalLaw, PartB.binaryLaw, PartB.codedLikelihood, PartB.sign,
      Bool.false_eq_true, if_false, if_true] <;> ring

end CausalLowerbound
