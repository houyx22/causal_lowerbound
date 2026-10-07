import CausalLowerbound.PartC.ObservationCountCosts
import CausalLowerbound.PartC.CollisionObservationCost

/-! Every bad small component has either a close ordered pair in the
coarse region or an observation in the assignment transition. Assigning
witnesses by their root component bounds the number of bad components
without a factor of the total sample size. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt incidenceComponentFintype
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I] [DecidableEq I]

def propensityGoodConfiguration (w : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ) (x : I → d → ℝ) : Prop :=
  (∀ i j, i ≠ j → 2 * ℓ < ‖x i - x j‖) ∧
    ∀ i, coarseBump x₀ h (x i) ≠ 0 → x i ∉ assignmentTransitionUnion (activeBlocks r h) w x₀ r

def propensityBadComponentCount (w : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ) (x : I → d → ℝ) : ℝ :=
  ∑ c : Option (incidenceGraph (physicalSharedIncidence (activeBlocks r h) x₀ ℓ r h x)).ConnectedComponent,
    if propensityGoodConfiguration w x₀ ℓ r h
      (fun i : {i // siteComponent (physicalSharedIncidence (activeBlocks r h) x₀ ℓ r h x) i = c} => x i.val)
    then 0 else 1

theorem propensityBadComponentCount_nonneg (w : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ) (x : I → d → ℝ) :
    0 ≤ propensityBadComponentCount w x₀ ℓ r h x := by
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

theorem shared_component_pair_coarse (x₀ : d → ℝ) (ℓ r h : ℝ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (hℓr : ℓ ≤ r) (hrh : r ≤ h) (x : I → d → ℝ)
    (i j : I) (hij : i ≠ j)
    (he : siteComponent (physicalSharedIncidence (activeBlocks r h) x₀ ℓ r h x) i =
      siteComponent (physicalSharedIncidence (activeBlocks r h) x₀ ℓ r h x) j) :
    x i ∈ coordinateBox x₀ (5 * h) := by
  obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact (Option.some.inj he)
  cases p with
  | nil => exact (hij rfl).elim
  | cons hadj p =>
    obtain ⟨_, q, hi, _⟩ := hadj
    exact (mem_coordinateBox x₀ (5 * h) (x i)).mpr
      (physicalSharedIncidence_coarse_bound x₀ ℓ r h hℓ hr hℓr hrh x i q hi)

theorem propensityBadComponentCount_le
    (w : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) (hℓr : ℓ ≤ r) (hrh : r ≤ h)
    {n : ℕ} (x : Fin n → d → ℝ) :
    propensityBadComponentCount w x₀ ℓ r h x ≤ collisionObservationCost x₀ ℓ h x +
      observationSetCount (assignmentTransitionUnion (activeBlocks r h) w x₀ r) x := by
  let inc := physicalSharedIncidence (activeBlocks r h) x₀ ℓ r h x
  let A := labelledCluster 1 x₀ (5 * h) (2 * ℓ)
  let T := assignmentTransitionUnion (activeBlocks r h) w x₀ r
  let pc := fun c : Option (incidenceGraph inc).ConnectedComponent =>
    ∑ e : Fin 2 ↪ Fin n, if siteComponent inc (e 0) = c then
      A.indicator (fun _ => (1 : ℝ)) (fun i => x (e i)) else 0
  let tc := fun c : Option (incidenceGraph inc).ConnectedComponent =>
    ∑ i : Fin n, if siteComponent inc i = c then T.indicator (fun _ => (1 : ℝ)) (x i) else 0
  have hp0 (c : Option (incidenceGraph inc).ConnectedComponent) : 0 ≤ pc c :=
    Finset.sum_nonneg (fun _ _ => ite_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) le_rfl)
  have ht0 (c : Option (incidenceGraph inc).ConnectedComponent) : 0 ≤ tc c :=
    Finset.sum_nonneg (fun _ _ => ite_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) le_rfl)
  have hc (c : Option (incidenceGraph inc).ConnectedComponent) :
      (if propensityGoodConfiguration w x₀ ℓ r h (fun i : {i // siteComponent inc i = c} => x i.val)
        then (0 : ℝ) else 1) ≤ pc c + tc c := by
    by_cases hg : propensityGoodConfiguration w x₀ ℓ r h (fun i : {i // siteComponent inc i = c} => x i.val)
    · rw [if_pos hg]
      exact add_nonneg (hp0 c) (ht0 c)
    · rw [if_neg hg]
      rcases not_and_or.mp hg with hsep | htr
      · push_neg at hsep
        obtain ⟨i, j, hij, hdist⟩ := hsep
        have hv : i.val ≠ j.val := fun he => hij (Subtype.ext he)
        let e : Fin 2 ↪ Fin n := ⟨Fin.cases i.val (fun _ : Fin 1 => j.val), by
          intro a b he
          fin_cases a <;> fin_cases b
          · rfl
          · exact (hv he).elim
          · exact (hv he.symm).elim
          · rfl⟩
        have hcoarse := shared_component_pair_coarse x₀ ℓ r h hℓ hr hℓr hrh x i.val j.val hv
          (i.property.trans j.property.symm)
        have hA : (fun a => x (e a)) ∈ A := by
          refine ⟨hcoarse, ?_⟩
          intro a
          fin_cases a
          apply (mem_coordinateBox (x i.val) (2 * ℓ) (x j.val)).mpr
          intro b
          have hb : |x j.val b - x i.val b| ≤ ‖x j.val - x i.val‖ := by
            simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (x j.val - x i.val) b
          exact hb.trans (by rwa [norm_sub_rev])
        have hp1 : 1 ≤ pc c := by
          have heq : (if siteComponent inc (e 0) = c then
              A.indicator (fun _ => (1 : ℝ)) (fun i => x (e i)) else 0) = 1 := by
            have he0 : siteComponent inc (e 0) = c := i.property
            rw [if_pos he0, Set.indicator_of_mem hA]
          rw [← heq]
          dsimp only [pc]
          exact Finset.single_le_sum (f := fun e : Fin 2 ↪ Fin n => if siteComponent inc (e 0) = c then
            A.indicator (fun _ => (1 : ℝ)) (fun i => x (e i)) else 0)
            (fun _ _ => ite_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) le_rfl) (Finset.mem_univ e)
        exact hp1.trans (le_add_of_nonneg_right (ht0 c))
      · push_neg at htr
        obtain ⟨i, _, hi⟩ := htr
        have ht1 : 1 ≤ tc c := by
          have heq : (if siteComponent inc i.val = c then T.indicator (fun _ => (1 : ℝ)) (x i.val) else 0) = 1 := by
            rw [if_pos i.property, Set.indicator_of_mem hi]
          rw [← heq]
          dsimp only [tc]
          exact Finset.single_le_sum (f := fun i : Fin n => if siteComponent inc i = c then
            T.indicator (fun _ => (1 : ℝ)) (x i) else 0)
            (fun _ _ => ite_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) le_rfl) (Finset.mem_univ i.val)
        exact ht1.trans (le_add_of_nonneg_left (hp0 c))
  calc
    _ ≤ ∑ c : Option (incidenceGraph inc).ConnectedComponent, (pc c + tc c) :=
      Finset.sum_le_sum (fun c _ => hc c)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1
      · dsimp only [pc]
        rw [Finset.sum_comm]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, collisionObservationCost, A]
      · dsimp only [tc]
        rw [Finset.sum_comm]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, observationSetCount, T]

end CausalLowerbound.PartC
