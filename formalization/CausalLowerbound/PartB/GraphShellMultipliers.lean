import CausalLowerbound.PartB.MixedShellRealization

/-! Reindex coarse/fine profiles back onto a fixed graph. This is needed
before summing over all choices of coarse and fine edges. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartB.ShellGeometry

open Wiener ConfigurationShells
variable {V E F C d R : Type*} [Fintype V] [DecidableEq V] [Fintype E]
  [Fintype F] [Fintype C] [Fintype d] [Fintype R]

abbrev GraphFactor (E d : Type*) := E × Bool × Option (d × Bool)

def graphDistance (a b : E → V) (u : V × d → ℝ) (e : E) : ℝ :=
  truncatedDistance (configurationSite u (a e)) (configurationSite u (b e))

def graphFactor (a b : E → V) (r : GraphFactor E d) (u : V × d → ℝ) : ℝ :=
  if r.2.1 then elementaryCoefficient (configurationSite u (b r.1)) (configurationSite u (a r.1)) r.2.2
  else elementaryCoefficient (configurationSite u (a r.1)) (configurationSite u (b r.1)) r.2.2

def graphShellMultiplier (m0 : ℕ) (a b : E → V) (r : R → GraphFactor E d)
    (t : ℝ) (s : E → Option ℕ) (u : V × d → ℝ) : ℝ :=
  graphTaper a b taperCutoff t (graphDistance a b u) *
    (∏ e, shellCutoff m0 (s e) (graphDistance a b u e)) * ∏ j, graphFactor a b (r j) u

def splitGraphFactor (q : F ⊕ C ≃ E) (r : GraphFactor E d) : EdgeFactor F C d :=
  (q.symm r.1, r.2)

theorem sumEndpoints_eq (q : F ⊕ C ≃ E) (a : E → V) :
    Sum.elim (fun e => a (q (Sum.inl e))) (fun e => a (q (Sum.inr e))) = fun e => a (q e) := by
  funext e
  cases e <;> rfl

theorem split_distance_eq (q : F ⊕ C ≃ E) (a b : E → V) (u : V × d → ℝ) (e : F ⊕ C) :
    actualEdgeDistance (fun e => a (q (Sum.inl e))) (fun e => b (q (Sum.inl e)))
      (fun e => a (q (Sum.inr e))) (fun e => b (q (Sum.inr e))) u e = graphDistance a b u (q e) := by
  unfold actualEdgeDistance
  rw [sumEndpoints_eq, sumEndpoints_eq]
  rfl

theorem split_factor_eq (q : F ⊕ C ≃ E) (a b : E → V) (r : GraphFactor E d) (u : V × d → ℝ) :
    actualFactor (fun e => a (q (Sum.inl e))) (fun e => b (q (Sum.inl e)))
      (fun e => a (q (Sum.inr e))) (fun e => b (q (Sum.inr e))) (splitGraphFactor q r) u =
      graphFactor a b r u := by
  unfold actualFactor
  rw [sumEndpoints_eq, sumEndpoints_eq]
  simp only [splitGraphFactor, Equiv.apply_symm_apply]
  rfl

theorem split_taper_eq (q : F ⊕ C ≃ E) (a b : E → V) (t : ℝ) (u : V × d → ℝ) :
    graphTaper (Sum.elim (fun e => a (q (Sum.inl e))) (fun e => a (q (Sum.inr e))))
      (Sum.elim (fun e => b (q (Sum.inl e))) (fun e => b (q (Sum.inr e)))) taperCutoff t
      (actualEdgeDistance (fun e => a (q (Sum.inl e))) (fun e => b (q (Sum.inl e)))
        (fun e => a (q (Sum.inr e))) (fun e => b (q (Sum.inr e))) u) =
      graphTaper a b taperCutoff t (graphDistance a b u) := by
  unfold graphTaper
  apply Finset.prod_congr rfl
  intro i _
  congr 2
  unfold vertexProduct
  simp only [sumEndpoints_eq, incident, split_distance_eq]
  exact q.prod_comp (fun e => if a e = i ∨ b e = i then graphDistance a b u e else 1)

theorem split_shell_eq (m0 : ℕ) (q : F ⊕ C ≃ E) (a b : E → V)
    (r : R → GraphFactor E d) (t : ℝ) (s : E → Option ℕ) (n : F → ℕ)
    (hf : ∀ e : F, s (q (Sum.inl e)) = some (n e))
    (hc : ∀ e : C, s (q (Sum.inr e)) = none) (u : V × d → ℝ) :
    actualShellMultiplier m0 (fun e => a (q (Sum.inl e))) (fun e => b (q (Sum.inl e)))
      (fun e => a (q (Sum.inr e))) (fun e => b (q (Sum.inr e)))
      (fun j => splitGraphFactor q (r j)) t (fun e => m0 + n e) u =
      graphShellMultiplier m0 a b r t s u := by
  have hw : actualShellWeight m0 (fun e => a (q (Sum.inl e))) (fun e => b (q (Sum.inl e)))
      (fun e => a (q (Sum.inr e))) (fun e => b (q (Sum.inr e))) (fun e => m0 + n e) u =
      ∏ e, shellCutoff m0 (s e) (graphDistance a b u e) := by
    rw [← q.prod_comp (fun e => shellCutoff m0 (s e) (graphDistance a b u e)), Fintype.prod_sum_type]
    simp only [hf, hc, shellCutoff, Option.elim_some, Option.elim_none, actualShellWeight, split_distance_eq]
  unfold actualShellMultiplier graphShellMultiplier
  rw [hw, split_taper_eq]
  simp only [split_factor_eq]

theorem split_order_eq (m0 : ℕ) (q : F ⊕ C ≃ E) (r : R → GraphFactor E d)
    (s : E → Option ℕ) (n : F → ℕ)
    (hf : ∀ e : F, s (q (Sum.inl e)) = some (n e))
    (hc : ∀ e : C, s (q (Sum.inr e)) = none) :
    totalFactorOrder (fun e => m0 + n e) (fun j => splitGraphFactor q (r j)) =
      ∑ j, shellLevel m0 (s (r j).1) := by
  apply Finset.sum_congr rfl
  intro j _
  have he : (r j).1 = q (q.symm (r j).1) := (q.apply_symm_apply _).symm
  conv_rhs => rw [he]
  change Sum.elim (fun e => m0 + n e) (fun _ => 0) (q.symm (r j).1) = _
  cases h : q.symm (r j).1 with
  | inl e => rw [hf]; rfl
  | inr e => rw [hc]; rfl

variable [DecidableEq E]

/-- One constant handles every assignment of coarse/fine labels on a fixed
graph and every dyadic level. Finiteness of the edge patterns is used here,
after the analytic estimate, and causes no dependence on the shell indices. -/
theorem graph_shell_uniform_wiener (a b : E → V) (r : R → GraphFactor E d) :
    ∃ M : ℕ, 5 ≤ M ∧ ∀ m0, M ≤ m0 → ∃ B ≥ 0, ∀ t > 0, ∀ s : E → Option ℕ,
      ∃ A : Fourier (V × d),
        (∀ u, toContinuous A (torusProjection u) = (graphShellMultiplier m0 a b r t s u : ℝ)) ∧
        ‖A‖ ≤ B * (2 : ℝ) ^ (∑ j, shellLevel m0 (s (r j).1)) := by
  classical
  let Fine (P : Finset E) := {e : E // e ∈ P}
  let Coarse (P : Finset E) := {e : E // e ∉ P}
  let q (P : Finset E) : Fine P ⊕ Coarse P ≃ E := Equiv.Set.sumCompl (P : Set E)
  have hall (P : Finset E) := actual_shell_uniform_wiener
    (fun e : Fine P => a (q P (Sum.inl e))) (fun e : Fine P => b (q P (Sum.inl e)))
    (fun e : Coarse P => a (q P (Sum.inr e))) (fun e : Coarse P => b (q P (Sum.inr e)))
    (fun j => splitGraphFactor (q P) (r j))
  choose starts hstarts hbounds using hall
  let M : ℕ := Finset.univ.sup starts
  have hM (P : Finset E) : starts P ≤ M := Finset.le_sup (f := starts) (Finset.mem_univ P)
  refine ⟨M, (hstarts ∅).trans (hM ∅), ?_⟩
  intro m0 hm0
  choose bounds hbounds0 hreal using fun P => hbounds P m0 ((hM P).trans hm0)
  let B : ℝ := ∑ P, bounds P
  have hB : 0 ≤ B := Finset.sum_nonneg (fun P _ => hbounds0 P)
  have hPB (P : Finset E) : bounds P ≤ B :=
    Finset.single_le_sum (fun P _ => hbounds0 P) (Finset.mem_univ P)
  refine ⟨B, hB, ?_⟩
  intro t ht s
  let P : Finset E := Finset.univ.filter (fun e => (s e).isSome)
  let n : Fine P → ℕ := fun e => (s e.val).getD 0
  have hf (e : Fine P) : s (q P (Sum.inl e)) = some (n e) := by
    change s e.val = some ((s e.val).getD 0)
    have he : (s e.val).isSome = true := (Finset.mem_filter.mp e.property).2
    cases h : s e.val with
    | none => simp only [h, Option.isSome_none, Bool.false_eq_true] at he
    | some j => rfl
  have hc (e : Coarse P) : s (q P (Sum.inr e)) = none := by
    change s e.val = none
    have he : ¬ (s e.val).isSome = true := fun h => e.property
      (Finset.mem_filter.mpr ⟨Finset.mem_univ e.val, h⟩)
    cases h : s e.val with
    | none => rfl
    | some j => simp only [h, Option.isSome_some, not_true_eq_false] at he
  obtain ⟨A, hA, hn⟩ := hreal P t ht (fun e => m0 + n e) (fun _ => Nat.le_add_right _ _)
  refine ⟨A, ?_, ?_⟩
  · intro u
    rw [hA, split_shell_eq m0 (q P) a b r t s n hf hc]
  · rw [split_order_eq m0 (q P) r s n hf hc] at hn
    exact hn.trans (mul_le_mul_of_nonneg_right (hPB P) (by positivity))

end CausalLowerbound.PartB.ShellGeometry
