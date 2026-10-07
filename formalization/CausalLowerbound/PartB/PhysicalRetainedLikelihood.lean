import CausalLowerbound.PartB.PhysicalFreshLikelihood
import CausalLowerbound.PartB.RetainedSignMarginal

/-! Identify the completed-block activation likelihood with the physical
partial jitter likelihood whose sitewise stability has been proved. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
open scoped BigOperators Classical
namespace CausalLowerbound.PartB.ShellGeometry
open Wiener
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d]

def physicalBaselineValues (Q : ℕ) (ρ : ℝ) (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r h : ℝ)
    {m : ℕ} (x : Fin m → d → ℝ) (z : S → MomentGrid (CoefficientExponent d Q) (4 * Q)) (i : Fin m) : ℝ :=
  packetField S (fun k => paperCoefficientAtoms Q ρ (extendBlockSample S z k)) x₀ r h (x i)

theorem activatedBlockField_decompose {I G : Type*} [Fintype I] [DecidableEq I] [Fintype G]
    (Q : ℕ) (ρ t : ℝ) (S : Finset I) (e : S ⊕ G ≃ Fin Q) (u : I → d → ℝ) (ψ : I → ℝ)
    (active : Bool) (z : MomentGrid (CoefficientExponent d Q) (4 * Q)) (ζ : Fin Q → Bool) (i : I) :
    activatedBlockField Q ρ t S e u ψ (active, (z, ζ)) i =
      baselineBlockField Q ρ u ψ z i +
        (t * (if active then ψ i else 0)) * retainedSigns Q S e ζ i := by
  cases active <;> simp [activatedBlockField, baselineBlockField] <;> ring

theorem physicalActivatedField_decompose (Q : ℕ) (ρ : ℝ) (S : Finset (d → ℤ))
    (x₀ : d → ℝ) (r h t : ℝ) (hr : 0 < r) {m : ℕ} (x : Fin m → d → ℝ)
    (hq : ∀ k : S, (carrierSites x₀ r k.val x).card ≤ Q)
    (active : S → Bool) (z : S → MomentGrid (CoefficientExponent d Q) (4 * Q))
    (ζ : S → Fin Q → Bool) (i : Fin m) :
    (∑ k : S, activatedBlockField Q ρ t (carrierSites x₀ r k.val x) (siteCompletion Q _ (hq k))
      (physicalBlockCoordinates x₀ r x k.val) (physicalBlockPackets x₀ r h x k.val) (active k, (z k, ζ k)) i) =
      physicalBaselineValues Q ρ S x₀ r h x z i +
        ∑ k : S, (t * (if active k then physicalBlockPackets x₀ r h x k.val i else 0)) *
          retainedSigns Q (carrierSites x₀ r k.val x) (siteCompletion Q _ (hq k)) (ζ k) i := by
  simp_rw [activatedBlockField_decompose]
  rw [Finset.sum_add_distrib, ← physical_baseline_field Q ρ S x₀ r h hr x z i]
  rfl

theorem physicalPartialCell_fresh (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (r h a b t : ℝ)
    (hr : 0 < r) {m : ℕ} (x : Fin m → d → ℝ)
    (hq : ∀ k : activeBlocks (d := d) r h, (carrierSites x₀ r k.val x).card ≤ Q)
    (w : Fin m → Bool × Bool) (active : activeBlocks (d := d) r h → Bool) :
    (FiniteLaw.independent (fun _ : activeBlocks (d := d) r h =>
      (paperCoefficientLaw (d := d) Q).prod (independentSigns (ι := Fin Q)))).expect
      (physicalPartialCell Q ρ false (activeBlocks r h) x₀ r h a b t (a * b * t ^ 2) x hq w active) =
      (FiniteLaw.independent (fun _ : activeBlocks (d := d) r h => paperCoefficientLaw (d := d) Q)).expect
        (fun z => freshJitterCell x₀ r h a b t x
          (physicalBaselineValues Q ρ (activeBlocks r h) x₀ r h x z) active w) := by
  rw [FiniteLaw.expect_independent_prods
    (fun _ : activeBlocks (d := d) r h => paperCoefficientLaw (d := d) Q)
    (fun _ : activeBlocks (d := d) r h => independentSigns (ι := Fin Q))]
  apply FiniteLaw.expect_congr
  intro z
  let f : (Fin m → ℝ) → ℝ := fun v => jointFieldLikelihood false
    (fun i => sign (w i).1) (fun i => sign (w i).2) a b
    (fun i => packetEta (activeBlocks r h) x₀ r h a t (x i))
    (fun i => targetField x₀ h (a * b * t ^ 2) (x i))
    (fun i => physicalBaselineValues Q ρ (activeBlocks r h) x₀ r h x z i + v i) / 4 ^ m
  let ψ : activeBlocks (d := d) r h → Fin m → ℝ := fun k i =>
    t * (if active k then physicalBlockPackets x₀ r h x k.val i else 0)
  have hψ (k : activeBlocks (d := d) r h) (i : Fin m) (hi : i ∉ carrierSites x₀ r k.val x) : ψ k i = 0 := by
    dsimp only [ψ]
    rw [physicalBlockPackets_zero x₀ r h x k.val i hi]
    simp
  have he := retained_signs_additive Q (fun k : activeBlocks (d := d) r h => carrierSites x₀ r k.val x)
    (fun k => siteCompletion Q _ (hq k)) ψ hψ f
  calc
    _ = (FiniteLaw.independent (fun _ : activeBlocks (d := d) r h => independentSigns (ι := Fin Q))).expect
        (fun ζ => f (fun i => ∑ k, ψ k i * retainedSigns Q (carrierSites x₀ r k.val x)
          (siteCompletion Q _ (hq k)) (ζ k) i)) := by
      apply (FiniteLaw.independent (fun _ : activeBlocks (d := d) r h => independentSigns (ι := Fin Q))).expect_congr
      intro ζ
      unfold physicalPartialCell
      simp_rw [physicalActivatedField_decompose Q ρ (activeBlocks r h) x₀ r h t hr x hq active z ζ]
      rfl
    _ = (FiniteLaw.independent (fun _ : Fin m => independentSigns (ι := activeBlocks (d := d) r h))).expect
        (fun ζ => f (fun i => ∑ k, ψ k i * sign (ζ i k))) := he
    _ = freshJitterCell x₀ r h a b t x (physicalBaselineValues Q ρ (activeBlocks r h) x₀ r h x z) active w := by
      unfold freshJitterCell
      apply (FiniteLaw.independent (fun _ : Fin m => independentSigns (ι := activeBlocks (d := d) r h))).expect_congr
      intro ζ
      dsimp only [f, ψ, freshJitterCell, jointFieldLikelihood]
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      congr 1
      congr 1
      simp only [physicalJitterField, physicalBlockPackets, Finset.mul_sum, mul_assoc]

end CausalLowerbound.PartB.ShellGeometry
