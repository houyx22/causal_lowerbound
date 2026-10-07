import CausalLowerbound.PartB.PhysicalPartialStability
import CausalLowerbound.FiniteProductBounds

/-! The joint physical likelihood with independent signs at each site.
Baseline fields may be arbitrary and dependent across sites. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators Classical
namespace CausalLowerbound.PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d]

def freshJitterCell (x₀ : d → ℝ) (r h a b t : ℝ) {m : ℕ} (x : Fin m → d → ℝ)
    (z : Fin m → ℝ) (active : activeBlocks (d := d) r h → Bool) (w : Fin m → Bool × Bool) : ℝ :=
  (FiniteLaw.independent (fun _ : Fin m => independentSigns (ι := activeBlocks (d := d) r h))).expect
    (fun ζ => ∏ i, siteFieldLikelihood false (sign (w i).1) (sign (w i).2) a b
      (packetEta (activeBlocks r h) x₀ r h a t (x i)) (targetField x₀ h (a * b * t ^ 2) (x i))
      (z i + physicalJitterField x₀ r h t (x i) active (ζ i)) / 4)

def baselinePhysicalCell (x₀ : d → ℝ) (r h a b t : ℝ) {m : ℕ} (x : Fin m → d → ℝ)
    (z : Fin m → ℝ) (w : Fin m → Bool × Bool) : ℝ :=
  ∏ i, siteFieldLikelihood true (sign (w i).1) (sign (w i).2) a b
    (packetEta (activeBlocks r h) x₀ r h a t (x i)) (targetField x₀ h (a * b * t ^ 2) (x i)) (z i) / 4

def componentStabilityConstant (m : ℕ) : ℝ := (2 : ℝ) ^ m * (m : ℝ) * (3 / 2)

theorem freshJitterCell_eq_product (x₀ : d → ℝ) (r h a b t : ℝ) {m : ℕ} (x : Fin m → d → ℝ)
    (z : Fin m → ℝ) (active : activeBlocks (d := d) r h → Bool) (w : Fin m → Bool × Bool) :
    freshJitterCell x₀ r h a b t x z active w =
      ∏ i, independentSigns.expect (fun ζ => siteFieldLikelihood false (sign (w i).1) (sign (w i).2) a b
        (packetEta (activeBlocks r h) x₀ r h a t (x i)) (targetField x₀ h (a * b * t ^ 2) (x i))
          (z i + physicalJitterField x₀ r h t (x i) active ζ) / 4) :=
  FiniteLaw.expect_independent_prod
    (fun _ : Fin m => independentSigns (ι := activeBlocks (d := d) r h))
    (fun i ζ => siteFieldLikelihood false (sign (w i).1) (sign (w i).2) a b
      (packetEta (activeBlocks r h) x₀ r h a t (x i)) (targetField x₀ h (a * b * t ^ 2) (x i))
        (z i + physicalJitterField x₀ r h t (x i) active ζ) / 4)

theorem freshJitterCell_full (x₀ : d → ℝ) (r h a b t : ℝ)
    (hr : 0 < r) (hh : 0 < h) (ha : a ≠ 0) {m : ℕ} (x : Fin m → d → ℝ)
    (z : Fin m → ℝ) (w : Fin m → Bool × Bool) :
    freshJitterCell x₀ r h a b t x z (fun _ => true) w = baselinePhysicalCell x₀ r h a b t x z w := by
  rw [freshJitterCell_eq_product]
  unfold baselinePhysicalCell
  apply Finset.prod_congr rfl
  intro i _
  simp only [div_eq_mul_inv, FiniteLaw.expect_mul_const]
  rw [physical_full_likelihood_match x₀ r h a b t hr hh ha]

theorem freshJitterCell_stability (x₀ : d → ℝ) (r h a b t : ℝ)
    (hr : 0 < r) (hh : 0 < h) (ha : 0 < a) (hb : 0 ≤ b) (hat : a ^ 2 * t ^ 2 ≤ 1)
    (hδ : a * b * t ^ 2 ≤ 1 / 2) {m : ℕ} (x : Fin m → d → ℝ) (z : Fin m → ℝ)
    (hp : ∀ i, |a * z i| ≤ 1) (w : Fin m → Bool × Bool)
    (hcell : ∀ i, |siteFieldLikelihood true (sign (w i).1) (sign (w i).2) a b
      (packetEta (activeBlocks r h) x₀ r h a t (x i)) (targetField x₀ h (a * b * t ^ 2) (x i)) (z i) / 4| ≤ 1)
    (active : activeBlocks (d := d) r h → Bool) :
    |freshJitterCell x₀ r h a b t x z active w - baselinePhysicalCell x₀ r h a b t x z w| ≤
      componentStabilityConstant m * (a * b * t ^ 2) := by
  let P : Fin m → ℝ := fun i => siteFieldLikelihood true (sign (w i).1) (sign (w i).2) a b
    (packetEta (activeBlocks r h) x₀ r h a t (x i)) (targetField x₀ h (a * b * t ^ 2) (x i)) (z i) / 4
  let Q : Fin m → ℝ := fun i => independentSigns.expect (fun ζ =>
    siteFieldLikelihood false (sign (w i).1) (sign (w i).2) a b
      (packetEta (activeBlocks r h) x₀ r h a t (x i)) (targetField x₀ h (a * b * t ^ 2) (x i))
      (z i + physicalJitterField x₀ r h t (x i) active ζ) / 4)
  have herr (i : Fin m) : |Q i - P i| ≤ (3 / 2) * (a * b * t ^ 2) := by
    have he := physical_partial_likelihood_stability x₀ r h a b t hr hh ha hb hat (x i) (z i) (hp i) active (w i).1 (w i).2
    dsimp only [P, Q]
    simp only [div_eq_mul_inv, FiniteLaw.expect_mul_const, ← sub_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4⁻¹)]
    nlinarith
  have hQ (i : Fin m) : |Q i| ≤ 2 := by
    have he : Q i = (Q i - P i) + P i := by ring
    rw [he]
    exact (abs_add _ _).trans (by have hc := hcell i; change |P i| ≤ 1 at hc; linarith [herr i])
  rw [freshJitterCell_eq_product]
  unfold baselinePhysicalCell
  change |(∏ i, Q i) - ∏ i, P i| ≤ _
  calc
    _ ≤ (2 : ℝ) ^ m * ∑ i, |Q i - P i| := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        abs_prod_sub_prod_le_bounded Finset.univ Q P 2 (by norm_num)
          (fun i _ => hQ i) (fun i _ => (hcell i).trans (by norm_num))
    _ ≤ (2 : ℝ) ^ m * ∑ _i : Fin m, (3 / 2) * (a * b * t ^ 2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => herr i)) (by positivity)
    _ = _ := by simp [componentStabilityConstant]; ring

theorem freshJitterCell_ignore (x₀ : d → ℝ) (r h a b t : ℝ) {m : ℕ} (x : Fin m → d → ℝ)
    (z : Fin m → ℝ) (active : activeBlocks (d := d) r h → Bool) (w : Fin m → Bool × Bool)
    (k : activeBlocks (d := d) r h) (hk : ¬(carrierSites x₀ r k.val x).Nonempty) (v : Bool) :
    freshJitterCell x₀ r h a b t x z (Function.update active k v) w =
      freshJitterCell x₀ r h a b t x z active w := by
  have hψ (i : Fin m) : packet (coarseBump x₀ h) x₀ r k.val (x i) = 0 :=
    physicalBlockPackets_zero x₀ r h x k.val i (fun hi => hk ⟨i, hi⟩)
  have hf (i : Fin m) (ζ : activeBlocks (d := d) r h → Bool) :
      physicalJitterField x₀ r h t (x i) (Function.update active k v) ζ =
        physicalJitterField x₀ r h t (x i) active ζ := by
    unfold physicalJitterField
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = k
    · subst j
      simp [hψ i]
    · rw [Function.update_of_ne hj]
  unfold freshJitterCell
  simp_rw [hf]

end CausalLowerbound.PartB.ShellGeometry
