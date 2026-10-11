import CausalLowerbound.UniformLowerBound.ClusterBounds
import CausalLowerbound.PartB.ComponentHellinger
import CausalLowerbound.PartB.ComponentRestriction
import CausalLowerbound.PartB.ComponentReindex

/-! A nontrivial component owns an adjacent ordered pair. This turns
uniform component bounds into a measurable close-pair majorant. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.UniformLowerBound
open PartB PartB.ShellGeometry
attribute [local instance] incidenceComponentFintype physicalComponentFintype finOrderedDecEq finOrderedDecLt
variable {V K : Type*} [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K]

def orderedAdjCount (G : SimpleGraph V) : ℝ :=
  ∑ e : Fin 2 ↪ V, if G.Adj (e 0) (e 1) then 1 else 0

theorem orderedAdjCount_nonneg (G : SimpleGraph V) : 0 ≤ orderedAdjCount G :=
  Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

theorem reachable_has_adjacent (G : SimpleGraph V) (i j : V) (hne : i ≠ j)
    (hij : G.Reachable i j) : ∃ b, G.Adj i b := by
  obtain ⟨p⟩ := hij
  cases p with
  | nil => exact (hne rfl).elim
  | cons hadj _ => exact ⟨_, hadj⟩

theorem component_has_adjacent_pair (inc : V → K → Prop)
    (c : Option (incidenceGraph inc).ConnectedComponent)
    (hc : 1 < Fintype.card {i // siteComponent inc i = c}) :
    ∃ e : Fin 2 ↪ V, siteComponent inc (e 0) = c ∧ (incidenceGraph inc).Adj (e 0) (e 1) := by
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card hc
  have hv : i.val ≠ j.val := fun he => hij (Subtype.ext he)
  obtain ⟨b, hadj⟩ := reachable_has_adjacent (incidenceGraph inc) i.val j.val hv
    (SimpleGraph.ConnectedComponent.exact (Option.some.inj (i.property.trans j.property.symm)))
  let e : Fin 2 ↪ V := ⟨Fin.cases i.val (fun _ : Fin 1 => b), by
    intro u v he
    fin_cases u <;> fin_cases v
    · rfl
    · exact (hadj.ne he).elim
    · exact (hadj.ne he.symm).elim
    · rfl⟩
  exact ⟨e, i.property, hadj⟩

theorem component_cost_sum_le_orderedAdjCount (inc : V → K → Prop)
    (cost : Option (incidenceGraph inc).ConnectedComponent → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hsingle : ∀ c, Fintype.card {i // siteComponent inc i = c} ≤ 1 → cost c = 0)
    (hcost : ∀ c, cost c ≤ D) :
    (∑ c, cost c) ≤ D * orderedAdjCount (incidenceGraph inc) := by
  let pc := fun c : Option (incidenceGraph inc).ConnectedComponent =>
    ∑ e : Fin 2 ↪ V, if siteComponent inc (e 0) = c then
      (if (incidenceGraph inc).Adj (e 0) (e 1) then (1 : ℝ) else 0) else 0
  have hp0 (c : Option (incidenceGraph inc).ConnectedComponent) : 0 ≤ pc c :=
    Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  have hc (c : Option (incidenceGraph inc).ConnectedComponent) : cost c ≤ D * pc c := by
    by_cases hs : Fintype.card {i // siteComponent inc i = c} ≤ 1
    · rw [hsingle c hs]
      exact mul_nonneg hD (hp0 c)
    · obtain ⟨e, he, ha⟩ := component_has_adjacent_pair inc c (by omega)
      have hp1 : 1 ≤ pc c := by
        have heq : (if siteComponent inc (e 0) = c then
            (if (incidenceGraph inc).Adj (e 0) (e 1) then (1 : ℝ) else 0) else 0) = 1 := by
          rw [if_pos he, if_pos ha]
        rw [← heq]
        exact Finset.single_le_sum
          (f := fun e : Fin 2 ↪ V => if siteComponent inc (e 0) = c then
            (if (incidenceGraph inc).Adj (e 0) (e 1) then (1 : ℝ) else 0) else 0)
          (fun _ _ => by dsimp only; split_ifs <;> norm_num) (Finset.mem_univ e)
      exact (hcost c).trans (by simpa using mul_le_mul_of_nonneg_left hp1 hD)
  calc
    _ ≤ ∑ c, D * pc c := Finset.sum_le_sum (fun c _ => hc c)
    _ = D * ∑ c, pc c := (Finset.mul_sum _ _ _).symm
    _ = _ := by
      congr 1
      dsimp only [pc]
      rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, orderedAdjCount]

theorem component_power_cost_sum_le (inc : V → K → Prop)
    (cost : Option (incidenceGraph inc).ConnectedComponent → ℝ)
    (Q : ℕ) (B δ : ℝ) (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hQ : ∀ c, Fintype.card {i // siteComponent inc i = c} ≤ Q)
    (hsingle : ∀ c, Fintype.card {i // siteComponent inc i = c} ≤ 1 → cost c = 0)
    (hcost : ∀ c, cost c ≤ B ^ Fintype.card {i // siteComponent inc i = c} * δ) :
    (∑ c, cost c) ≤ (B ^ Q * δ) * orderedAdjCount (incidenceGraph inc) := by
  apply component_cost_sum_le_orderedAdjCount inc cost (B ^ Q * δ)
    (mul_nonneg (pow_nonneg (zero_le_one.trans hB) _) hδ) hsingle
  intro c
  exact (hcost c).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB (hQ c)) hδ)

omit [DecidableEq V] in
theorem componentOutputLaw_eq_of_card_le_one {Ω Y : Type*} [Fintype Ω] [Inhabited Ω] [Fintype Y]
    (μ ν : K → FiniteLaw Ω) (inc : V → K → Prop)
    (P R : V → (K → Ω) → FiniteLaw Y)
    (hP : ∀ i x y, (∀ k, inc i k → x k = y k) → P i x = P i y)
    (hR : ∀ i x y, (∀ k, inc i k → x k = y k) → R i x = R i y)
    (hone : ∀ i, (FiniteLaw.independent μ).mixture (P i) =
      (FiniteLaw.independent ν).mixture (R i))
    (c : Option (incidenceGraph inc).ConnectedComponent)
    (hc : Fintype.card {i // siteComponent inc i = c} ≤ 1) :
    componentOutputLaw μ inc P c = componentOutputLaw ν inc R c := by
  apply FiniteLaw.ext
  intro w
  rw [componentOutputLaw_weight_full μ inc P hP, componentOutputLaw_weight_full ν inc R hR]
  letI : Subsingleton {i // siteComponent inc i = c} := Fintype.card_le_one_iff_subsingleton.mp hc
  cases isEmpty_or_nonempty {i // siteComponent inc i = c} with
  | inl he => simp only [Finset.univ_eq_empty, Finset.prod_empty, FiniteLaw.expect_const]
  | inr hn =>
    let i := Classical.choice hn
    letI : Unique {i // siteComponent inc i = c} := ⟨⟨i⟩, fun j => Subsingleton.elim _ _⟩
    simpa only [Fintype.prod_unique] using congrArg (fun law : FiniteLaw Y => law.weight (w i)) (hone i.val)

theorem reindexed_mixture_hellinger_le_orderedAdjCount
    {Ω Y : Type*} [Fintype Ω] [Inhabited Ω] [Fintype Y]
    (μ ν : K → FiniteLaw Ω) (inc : V → K → Prop)
    (P R : V → (K → Ω) → FiniteLaw Y)
    (hP : ∀ i x y, (∀ k, inc i k → x k = y k) → P i x = P i y)
    (hR : ∀ i x y, (∀ k, inc i k → x k = y k) → R i x = R i y)
    (m : Option (incidenceGraph inc).ConnectedComponent → ℕ)
    (e : ∀ c, Fin (m c) ≃ {i // siteComponent inc i = c}) (D : ℝ) (hD : 0 ≤ D)
    (hsingle : ∀ c, m c ≤ 1 →
      FiniteLaw.restrictedExperiment μ P (fun j => (e c j).val) =
        FiniteLaw.restrictedExperiment ν R (fun j => (e c j).val))
    (hcost : ∀ c,
      (FiniteLaw.restrictedExperiment μ P (fun j => (e c j).val)).hellingerSq
        (FiniteLaw.restrictedExperiment ν R (fun j => (e c j).val)) ≤ D) :
    ((FiniteLaw.independent μ).mixture (fun z => FiniteLaw.independent (fun i => P i z))).hellingerSq
      ((FiniteLaw.independent ν).mixture (fun z => FiniteLaw.independent (fun i => R i z))) ≤
      D * orderedAdjCount (incidenceGraph inc) := by
  apply (reindexed_component_hellinger μ ν inc P R hP hR m e).trans
  apply component_cost_sum_le_orderedAdjCount inc _ D hD _ hcost
  intro c hc
  have hm : m c ≤ 1 := by
    have he := Fintype.card_congr (e c)
    simp only [Fintype.card_fin] at he
    omega
  rw [hsingle c hm]
  simp only [FiniteLaw.hellingerSq, sub_self, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero]

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem observationGraph_orderedAdjCount_le_collisionCount (x₀ : d → ℝ) (ℓ h : ℝ)
    (hℓ : 0 < ℓ) (hℓh : ℓ ≤ h) {n : ℕ} (x : Fin n → d → ℝ) :
    orderedAdjCount (observationGraph (activeBlocks ℓ h) x₀ ℓ x) ≤ collisionCount x₀ ℓ h x := by
  apply Finset.sum_le_sum
  intro e _
  by_cases ha : (observationGraph (activeBlocks ℓ h) x₀ ℓ x).Adj (e 0) (e 1)
  · rw [if_pos ha]
    have hA : (fun i => x (e i)) ∈ labelledCluster 1 x₀ (5 * h) (4 * ℓ) := by
      obtain ⟨_, k, hi, hj⟩ := ha
      refine ⟨(mem_coordinateBox _ _ _).mpr
        (active_carrier_distance x₀ ℓ h hℓ hℓh k.val k.property (x (e 0)) hi), ?_⟩
      intro i
      fin_cases i
      apply (mem_coordinateBox _ _ _).mpr
      intro a
      exact common_carrier_distance x₀ ℓ hℓ k.val (x (e 1)) (x (e 0)) hj hi a
    rw [Set.indicator_of_mem hA]
  · rw [if_neg ha]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

theorem observation_component_cost_sum_le_collisionCount
    (x₀ : d → ℝ) (ℓ h : ℝ) (hℓ : 0 < ℓ) (hℓh : ℓ ≤ h)
    {n : ℕ} (x : Fin n → d → ℝ)
    (cost : Option (observationGraph (activeBlocks ℓ h) x₀ ℓ x).ConnectedComponent → ℝ)
    (D : ℝ) (hD : 0 ≤ D)
    (hsingle : ∀ c, Fintype.card {i // siteComponent
      (fun j (k : activeBlocks (d := d) ℓ h) => x j ∈ carrierBox x₀ ℓ k.val) i = c} ≤ 1 → cost c = 0)
    (hcost : ∀ c, cost c ≤ D) :
    (∑ c, cost c) ≤ D * collisionCount x₀ ℓ h x := by
  exact (component_cost_sum_le_orderedAdjCount _ cost D hD hsingle hcost).trans
    (mul_le_mul_of_nonneg_left
      (observationGraph_orderedAdjCount_le_collisionCount x₀ ℓ h hℓ hℓh x) hD)

end CausalLowerbound.UniformLowerBound
