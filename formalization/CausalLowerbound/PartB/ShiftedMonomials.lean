import CausalLowerbound.PartB.SignMonomials

/-! Exact finite expansion of a shifted coordinate monomial, with one option
per occurrence: retain its baseline factor or choose a shift site. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartB

variable {K V : Type*} [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]

abbrev ShiftPositions (s : K → Option V) := {k : K // (s k).isSome}
abbrev BasePositions (s : K → Option V) := {k : K // ¬ (s k).isSome}

def choiceSite (s : K → Option V) (k : ShiftPositions s) : V := (s k.val).get k.property
def choiceDegree (s : K → Option V) : ℕ := Fintype.card (ShiftPositions s)
def choiceBase (U : K → ℝ) (s : K → Option V) : ℝ := ∏ k : BasePositions s, U k.val
def choiceValue (U : K → ℝ) (H : K → V → ℝ) (s : K → Option V) : ℝ :=
  ∏ k, (s k).elim (U k) (H k)

theorem shifted_product_expansion (U : K → ℝ) (H : K → V → ℝ) :
    (∏ k, (U k + ∑ i, H k i)) = ∑ s : K → Option V, choiceValue U H s := by
  unfold choiceValue
  rw [← Fintype.prod_sum (fun (k : K) (s : Option V) => s.elim (U k) (H k))]
  simp only [Fintype.sum_option, Option.elim_none, Option.elim_some]

theorem choiceValue_split (U : K → ℝ) (H : K → V → ℝ) (s : K → Option V) :
    choiceValue U H s = choiceBase U s * ∏ k : ShiftPositions s, H k.val (choiceSite s k) := by
  classical
  have hs (k : ShiftPositions s) : (s k.val).elim (U k.val) (H k.val) = H k.val (choiceSite s k) := by
    have hk : (s k.val).isSome = true := k.property
    cases h : s k.val with
    | none => simp only [h, Option.isSome_none, Bool.false_eq_true] at hk
    | some i => simp [choiceSite, h]
  have hb (k : BasePositions s) : (s k.val).elim (U k.val) (H k.val) = U k.val := by
    have hk : ¬ (s k.val).isSome = true := k.property
    cases h : s k.val with
    | none => rfl
    | some i => simp only [h, Option.isSome_some, not_true_eq_false] at hk
  unfold choiceValue
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun k => (s k).isSome)]
  simp only [hs, hb]
  exact mul_comm _ _

theorem choiceValue_scaled (U : K → ℝ) (c : K → V → ℝ) (t : ℝ) (ω : V → Bool) (s : K → Option V) :
    choiceValue U (fun k i => t * c k i * sign (ω i)) s =
      choiceBase U s * t ^ choiceDegree s * (∏ k : ShiftPositions s, c k.val (choiceSite s k)) *
        (∏ k : ShiftPositions s, sign (ω (choiceSite s k))) := by
  rw [choiceValue_split]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, choiceDegree]
  ring

theorem choiceDegree_le (s : K → Option V) : choiceDegree s ≤ Fintype.card K :=
  Fintype.card_le_of_injective Subtype.val Subtype.val_injective

theorem choiceDegree_zero_iff (s : K → Option V) : choiceDegree s = 0 ↔ s = fun _ => none := by
  constructor
  · intro h
    funext k
    cases he : s k with
    | none => rfl
    | some i =>
      have hp : 0 < choiceDegree s := Fintype.card_pos_iff.mpr ⟨⟨k, by rw [he]; rfl⟩⟩
      omega
  · intro h
    subst s
    simp [choiceDegree, ShiftPositions]

theorem independent_sign_mean (i : V) : independentSigns.expect (fun ω => sign (ω i)) = 0 := by
  have he (ω : V → Bool) : signMonomial (Pi.single i 1) ω = sign (ω i) := by
    simp [signMonomial, Pi.single_apply]
  have hn : ¬ EvenExponents (Pi.single i 1) := by
    intro h
    have hi := h i
    simpa using hi
  rw [← independentSigns.expect_congr he, expect_signMonomial, if_neg hn]

theorem sign_product_one_mean {S : Type*} [Fintype S] (sites : S → V) (hS : Fintype.card S = 1) :
    independentSigns.expect (fun ω => ∏ k : S, sign (ω (sites k))) = 0 := by
  classical
  obtain ⟨k, hk⟩ := Fintype.card_eq_one_iff.mp hS
  have hu : (Finset.univ : Finset S) = {k} := by
    ext j
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact hk j
  simp only [hu, Finset.prod_singleton]
  exact independent_sign_mean (sites k)

end CausalLowerbound.PartB
