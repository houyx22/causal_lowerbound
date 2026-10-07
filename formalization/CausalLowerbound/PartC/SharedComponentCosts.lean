import CausalLowerbound.PartC.SharedComponentBlocks
import CausalLowerbound.PartC.PropensityErrorReduction
import CausalLowerbound.PartC.GhostDefectReindex
import CausalLowerbound.PartB.GlobalGhostCost

/-! Component costs count an incident physical block only in the unique
component owning that block. The completed ghost defect agrees with the
global retained-site cost, so the measurable subset majorant applies. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt incidenceComponentFintype
variable {d V U G : Type*} [Fintype d] [DecidableEq d]
  [Fintype V] [DecidableEq V] [Fintype U] [Fintype G]

theorem completedGhostTaperDefect_eq_blockSubsetCost
    (H₀ : DiscreteLaw ℕ) (Q : ℕ) (τ : ℝ) (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ)
    {n : ℕ} (x : Fin n → d → ℝ) (T : Finset (Fin n)) (hT : T.card ≤ Q)
    (hbox : ∀ i : T, x i.val ∈ carrierBox x₀ r k) (a : U ≃ T) (e : U ⊕ G ≃ Fin Q) :
    completedGhostTaperDefect Q e τ
      (fun i => carrierCoordinate (localCoordinate x₀ r k (x (a i).val))) =
      blockSubsetCost H₀ Q 0 τ x₀ r k T hT x := by
  have hg : Fintype.card G = Q - T.card := by
    have he := Fintype.card_congr e
    have ha := Fintype.card_congr a
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe] at he ha
    omega
  let b : G ≃ Fin (Q - T.card) := Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using hg)
  have hx : (fun i : T => x i.val) ∈ carrierConfigurationBox x₀ r k := fun i _ => hbox i
  rw [blockSubsetCost, physicalGhostCost, Set.indicator_of_mem hx,
    completedGhostTaperDefect_eq_ghostActivation H₀]
  exact congrArg (fun t : ℝ => 1 - t) (ghostActivation_reindex H₀ Q 0 τ e (siteCompletion Q T hT) a b
    (fun i => Wiener.torusProjection (carrierCoordinate (localCoordinate x₀ r k (x i.val)))))

def sharedComponentCarrierSitesEquiv (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h : ℝ)
    {n : ℕ} (x : Fin n → d → ℝ)
    (c : Option (incidenceGraph (physicalSharedIncidence S x₀ ℓ r h x)).ConnectedComponent)
    (k : S) (hk : componentBlockOwner (physicalSharedIncidence S x₀ ℓ r h x) k = c) :
    {i : {i // siteComponent (physicalSharedIncidence S x₀ ℓ r h x) i = c} //
      x i.val ∈ carrierBox x₀ r k.val} ≃ carrierSites x₀ r k.val x where
  toFun i := ⟨i.val.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.property⟩⟩
  invFun i := ⟨⟨i.val, (blockComponent_of_inc (physicalSharedIncidence S x₀ ℓ r h x)
    i.val (Sum.inl k) (Finset.mem_filter.mp i.property).2).symm.trans hk⟩,
      (Finset.mem_filter.mp i.property).2⟩
  left_inv i := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv i := by apply Subtype.ext; rfl

theorem shared_component_block_sum_le
    (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ r h : ℝ) (x : V → d → ℝ)
    (f : (d → ℤ) → ℝ) (hf : ∀ k ∈ S, 0 ≤ f k) :
    (∑ c : Option (incidenceGraph (physicalSharedIncidence S x₀ ℓ r h x)).ConnectedComponent,
      ∑ k : configurationBlocks S x₀ r
        (fun i : {i // siteComponent (physicalSharedIncidence S x₀ ℓ r h x) i = c} => x i.val), f k.val) ≤
      ∑ k : S, f k.val := by
  let inc := physicalSharedIncidence S x₀ ℓ r h x
  have hc (c : Option (incidenceGraph inc).ConnectedComponent) :
      (∑ k : configurationBlocks S x₀ r
        (fun i : {i // siteComponent inc i = c} => x i.val), f k.val) ≤
        ∑ k : {k : S // componentBlockOwner inc k = c}, f k.val.val := by
    by_cases hn : c = none
    · subst c
      have he : configurationBlocks S x₀ r
          (fun i : {i // siteComponent inc i = none} => x i.val) = ∅ := by
        apply Finset.eq_empty_iff_forall_not_mem.mpr
        intro k hk
        obtain ⟨_, i, _⟩ := (mem_configurationBlocks S x₀ r _ k).mp hk
        exact Option.noConfusion i.property
      rw [he]
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      exact Finset.sum_nonneg (fun k _ => hf k.val.val k.val.property)
    · exact le_of_eq (Fintype.sum_equiv (physicalComponentBlocksEquiv S x₀ ℓ r h x c hn).symm
        _ _ (fun k => rfl))
  exact (Finset.sum_le_sum (fun c _ => hc c)).trans_eq
    (Fintype.sum_fiberwise (componentBlockOwner inc) (fun k : S => f k.val))

theorem shared_component_ghost_defect_le_smallBlockCost
    (H₀ : DiscreteLaw ℕ) (Q : ℕ) (τ : ℝ) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (ℓ r h : ℝ) (hr : 0 < r) {n : ℕ} (x : Fin n → d → ℝ)
    (c : Option (incidenceGraph (physicalSharedIncidence S x₀ ℓ r h x)).ConnectedComponent)
    (hq : Fintype.card {i // siteComponent (physicalSharedIncidence S x₀ ℓ r h x) i = c} ≤ Q)
    (k : configurationBlocks S x₀ r
      (fun i : {i // siteComponent (physicalSharedIncidence S x₀ ℓ r h x) i = c} => x i.val)) :
    completedGhostTaperDefect Q
      (retainedDesignCompletion Q x₀ r k.val
        (fun i : {i // siteComponent (physicalSharedIncidence S x₀ ℓ r h x) i = c} => x i.val) hq) τ
      (fun i => carrierCoordinate (localCoordinate x₀ r k.val (x i.val.val))) ≤
      smallBlockCost H₀ Q 0 τ x₀ r k.val x := by
  let inc := physicalSharedIncidence S x₀ ℓ r h x
  obtain ⟨hks, i, hi⟩ := (mem_configurationBlocks S x₀ r _ k.val).mp k.property
  have hc : c ≠ none := by
    intro he
    have hh := i.property.trans he
    exact Option.noConfusion hh
  let kS : S := ⟨k.val, hks⟩
  have hk : componentBlockOwner inc kS = c :=
    (componentBlockOwner_eq_iff inc c hc kS).mpr ⟨i.val, i.property, hi⟩
  let a := sharedComponentCarrierSitesEquiv S x₀ ℓ r h x c kS hk
  have hg : (carrierSites x₀ r k.val x).card ≤ Q := by
    have ha := Fintype.card_congr a
    rw [Fintype.card_coe] at ha
    exact ha.symm.le.trans ((retained_design_card_le x₀ r k.val
      (fun i : {i // siteComponent inc i = c} => x i.val)).trans hq)
  have he := completedGhostTaperDefect_eq_blockSubsetCost H₀ Q τ x₀ r k.val x
    (carrierSites x₀ r k.val x) hg (fun i => (Finset.mem_filter.mp i.property).2) a
    (retainedDesignCompletion Q x₀ r k.val
      (fun i : {i // siteComponent inc i = c} => x i.val) hq)
  have hne : (carrierSites x₀ r k.val x).Nonempty :=
    ⟨i.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have hb := actual_block_leakage_le_smallBlockCost H₀ Q 0 τ (by norm_num) (by norm_num) x₀ r hr k.val x hg
  rw [if_pos hne, ← blockSubsetCost_at_carrierSites H₀ Q 0 τ x₀ r k.val x hg] at hb
  exact he.le.trans hb

theorem shared_component_ghost_sum_le_globalGhostCost
    (H₀ : DiscreteLaw ℕ) (Q : ℕ) (τ : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ) (hr : 0 < r)
    {n : ℕ} (x : Fin n → d → ℝ)
    (hq : ∀ c : Option (incidenceGraph (physicalSharedIncidence (activeBlocks r h) x₀ ℓ r h x)).ConnectedComponent,
      Fintype.card {i // siteComponent (physicalSharedIncidence (activeBlocks r h) x₀ ℓ r h x) i = c} ≤ Q) :
    let S := activeBlocks (d := d) r h
    let inc := physicalSharedIncidence S x₀ ℓ r h x
    (∑ c : Option (incidenceGraph inc).ConnectedComponent,
      propensityGhostDefectSum Q (configurationBlocks S x₀ r
        (fun i : {i // siteComponent inc i = c} => x i.val)) x₀ r τ
        (fun i : {i // siteComponent inc i = c} => x i.val)
        (fun k => Fin (Q - Fintype.card {i : {i // siteComponent inc i = c} // x i.val ∈ carrierBox x₀ r k.val}))
        (fun k => retainedDesignCompletion Q x₀ r k.val
          (fun i : {i // siteComponent inc i = c} => x i.val) (hq c))) ≤
      globalGhostCost H₀ Q 0 τ x₀ r h x := by
  dsimp only
  apply (Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (fun k _ =>
    shared_component_ghost_defect_le_smallBlockCost H₀ Q τ (activeBlocks r h) x₀ ℓ r h hr x c (hq c) k))).trans
  exact shared_component_block_sum_le (activeBlocks r h) x₀ ℓ r h x
    (fun k => smallBlockCost H₀ Q 0 τ x₀ r k x)
    (fun k _ => smallBlockCost_nonneg H₀ Q 0 τ (by norm_num) (by norm_num) x₀ r hr k x)

end CausalLowerbound.PartC
