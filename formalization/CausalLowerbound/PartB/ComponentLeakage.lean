import CausalLowerbound.PartB.ComponentSize

/-! Summing component leakage counts each active physical block once. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators Classical
namespace CausalLowerbound.PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt incidenceComponentFintype physicalComponentFintype
variable {d : Type*} [Fintype d] [DecidableEq d]

def actualBlockLeakage (H : DiscreteLaw ℕ) (Q : ℕ) (θ ε : ℝ) (x₀ : d → ℝ) (r : ℝ)
    (k : d → ℤ) {n : ℕ} (x : Fin n → d → ℝ) (hq : (carrierSites x₀ r k x).card ≤ Q) : ℝ :=
  if (carrierSites x₀ r k x).Nonempty then
    1 - evaluatedBlockWeight H Q θ ε (carrierSites x₀ r k x)
      (siteCompletion Q _ hq) (physicalBlockCoordinates x₀ r x k) else 0

theorem actualBlockLeakage_nonneg (H : DiscreteLaw ℕ) (Q : ℕ) (θ ε : ℝ)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ)
    {n : ℕ} (x : Fin n → d → ℝ) (hq : (carrierSites x₀ r k x).card ≤ Q) :
    0 ≤ actualBlockLeakage H Q θ ε x₀ r k x hq := by
  unfold actualBlockLeakage
  split_ifs
  · exact sub_nonneg.mpr (evaluatedBlockWeight_bounds H Q θ ε hθ hθ1 _ _ _).2
  · exact le_rfl

theorem actualBlockLeakage_component (H : DiscreteLaw ℕ) (Q : ℕ) (θ ε : ℝ)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) {n m : ℕ} (x : Fin n → d → ℝ)
    (c : Option (observationGraph S x₀ r x).ConnectedComponent)
    (e : Fin m ≃ {i // siteComponent (fun j (k : S) => x j ∈ carrierBox x₀ r k.val) i = c})
    (k : S) (hl : (carrierSites x₀ r k.val (componentConfiguration S x₀ r x c e)).card ≤ Q)
    (hf : (carrierSites x₀ r k.val x).card ≤ Q) :
    actualBlockLeakage H Q θ ε x₀ r k.val (componentConfiguration S x₀ r x c e) hl =
      if blockComponent (fun j (b : S) => x j ∈ carrierBox x₀ r b.val) k = c then
        actualBlockLeakage H Q θ ε x₀ r k.val x hf else 0 := by
  by_cases hk : blockComponent (fun j (b : S) => x j ∈ carrierBox x₀ r b.val) k = c
  · let f := componentCarrierSitesEquiv S x₀ r x c e k hk
    have hn : (carrierSites x₀ r k.val (componentConfiguration S x₀ r x c e)).Nonempty ↔
        (carrierSites x₀ r k.val x).Nonempty := by
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨(f ⟨i, hi⟩).val, (f ⟨i, hi⟩).property⟩
      · rintro ⟨i, hi⟩
        exact ⟨(f.symm ⟨i, hi⟩).val, (f.symm ⟨i, hi⟩).property⟩
    simp only [if_pos hk, actualBlockLeakage, hn]
    rw [evaluatedBlockWeight_component H Q θ ε S x₀ r x c e k hk hl hf]
  · simp only [if_neg hk, actualBlockLeakage,
      componentCarrierSites_empty_of_ne S x₀ r x c e k hk, Finset.not_nonempty_empty, if_false]

theorem component_leakage_sum (H : DiscreteLaw ℕ) (Q : ℕ) (θ ε : ℝ)
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) {n : ℕ} (x : Fin n → d → ℝ)
    (m : Option (observationGraph S x₀ r x).ConnectedComponent → ℕ)
    (e : ∀ c, Fin (m c) ≃ {i // siteComponent (fun j (k : S) => x j ∈ carrierBox x₀ r k.val) i = c})
    (hl : ∀ c (k : S), (carrierSites x₀ r k.val (componentConfiguration S x₀ r x c (e c))).card ≤ Q)
    (hf : ∀ k : S, (carrierSites x₀ r k.val x).card ≤ Q) :
    (∑ c, ∑ k : S, actualBlockLeakage H Q θ ε x₀ r k.val (componentConfiguration S x₀ r x c (e c)) (hl c k)) =
      ∑ k : S, actualBlockLeakage H Q θ ε x₀ r k.val x (hf k) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = ∑ c, if blockComponent (fun j (b : S) => x j ∈ carrierBox x₀ r b.val) k = c then
        actualBlockLeakage H Q θ ε x₀ r k.val x (hf k) else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      exact actualBlockLeakage_component H Q θ ε S x₀ r x c (e c) k (hl c k) (hf k)
    _ = _ := by simp

end CausalLowerbound.PartB.ShellGeometry
