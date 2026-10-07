import CausalLowerbound.PartB.PolarizationAlgebra
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Configuration-shell counting and inverse-order bookkeeping

A shell level is a natural number, with zero reserved for the coarse shell.
These are the combinatorial steps used after the taper has bounded each
vertex's total incident level. No geometric taper estimate is assumed proved.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartB.ConfigurationShells

variable {V E R : Type*} [Fintype V] [DecidableEq V] [Fintype E] [Fintype R]

def incident (a b : E → V) (i : V) (e : E) : Prop := a e = i ∨ b e = i

instance (a b : E → V) (i : V) (e : E) : Decidable (incident a b i e) :=
  inferInstanceAs (Decidable (a e = i ∨ b e = i))

def vertexOrder (a b : E → V) (m : E → ℕ) (i : V) : ℕ :=
  ∑ e, if incident a b i e then m e else 0

theorem edge_le_vertexOrder (a b : E → V) (m : E → ℕ) (e : E) :
    m e ≤ vertexOrder a b m (a e) := by
  have h := Finset.single_le_sum
    (f := fun k => if incident a b (a e) k then m k else 0)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
  simpa [incident, vertexOrder] using h

def Admissible (a b : E → V) (L : ℕ) (m : E → ℕ) : Prop :=
  ∀ i, vertexOrder a b m i ≤ L

def shellCode (a b : E → V) (L : ℕ) (m : {m : E → ℕ // Admissible a b L m}) :
    E → Fin (L + 1) := fun e =>
  ⟨m.val e, Nat.lt_succ_of_le ((edge_le_vertexOrder a b m.val e).trans (m.property (a e)))⟩

theorem shellCode_injective (a b : E → V) (L : ℕ) : Function.Injective (shellCode a b L) := by
  intro m n h
  apply Subtype.ext; funext e
  exact congrArg Fin.val (congrFun h e)

instance admissibleFinite (a b : E → V) (L : ℕ) : Finite {m : E → ℕ // Admissible a b L m} :=
  Finite.of_injective (shellCode a b L) (shellCode_injective a b L)

/-- Admissible shell assignments have polynomial, not exponential-in-scale,
cardinality: one factor of L+1 for every graph edge. -/
theorem admissible_card_bound (a b : E → V) (L : ℕ) :
    Nat.card {m : E → ℕ // Admissible a b L m} ≤ (L + 1) ^ Fintype.card E := by
  classical
  letI : Fintype {m : E → ℕ // Admissible a b L m} := Fintype.ofFinite _
  simpa [Nat.card_eq_fintype_card, Fintype.card_fun] using
    Fintype.card_le_of_injective (shellCode a b L) (shellCode_injective a b L)

def inverseMultiplicity (a b : E → V) (sites : R → V) (e : E) : ℕ :=
  ∑ r, if incident a b (sites r) e then 1 else 0

/-- The exact inverse-order ledger, including repeated site indices and edges
sharing vertices. -/
theorem inverse_order_ledger (a b : E → V) (sites : R → V) (m : E → ℕ) :
    (∑ e, inverseMultiplicity a b sites e * m e) = ∑ r, vertexOrder a b m (sites r) := by
  simp only [inverseMultiplicity, vertexOrder, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro r _
  apply Finset.sum_congr rfl; intro e _
  split_ifs <;> simp

theorem inverse_order_le (a b : E → V) (sites : R → V) (m : E → ℕ) (L : ℕ)
    (hm : Admissible a b L m) :
    (∑ e, inverseMultiplicity a b sites e * m e) ≤ Fintype.card R * L := by
  rw [inverse_order_ledger]
  simpa using Finset.sum_le_sum (s := Finset.univ) (fun r _ => hm (sites r))

/-- Vertexwise inverse-distance bounds multiply once per shift factor. -/
theorem dyadic_ledger_bound (a b : E → V) (sites : R → V) (m : E → ℕ)
    (A : ℝ) (hA : ∀ r, (2 : ℝ) ^ vertexOrder a b m (sites r) ≤ A) :
    (2 : ℝ) ^ (∑ e, inverseMultiplicity a b sites e * m e) ≤ A ^ Fintype.card R := by
  calc
    _ = ∏ r, (2 : ℝ) ^ vertexOrder a b m (sites r) := by
      rw [inverse_order_ledger, Finset.prod_pow_eq_pow_sum]
    _ ≤ ∏ _r : R, A :=
      Finset.prod_le_prod (fun _ _ => by positivity) (fun r _ => hA r)
    _ = _ := by simp

end CausalLowerbound.PartB.ConfigurationShells
