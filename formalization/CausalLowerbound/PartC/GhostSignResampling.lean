import CausalLowerbound.PartC.RepresentativeStability
import CausalLowerbound.PartC.RoughChartResampling
import CausalLowerbound.PartC.UnitCubeGhosts
import Mathlib.MeasureTheory.Integral.Pi

/-! One-symbol sensitivity after actual ghost integration. Retained
formal variables stay fixed. Ghost dependence contributes the small
factor norm (B - 1) times the fine-packet chart volume. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB.ShellGeometry Wiener Representative
variable {d V I G : Type*} [Fintype d] [DecidableEq d] [Fintype V] [DecidableEq V]
  [Fintype I] [Fintype G] {D : ℕ}

theorem integral_cube_coordinate (i : G) (f : (d → ℝ) → ℝ) :
    (∫ g : G → d → ℝ, f (g i) ∂Measure.pi (fun _ : G => cubeMeasure d)) =
      ∫ u, f u ∂cubeMeasure d := by
  let F := fun j : G => fun u : d → ℝ => if j = i then f u else 1
  have he := @integral_fintype_prod_eq_prod ℝ inferInstance G inferInstance (fun _ => d → ℝ)
    F (fun _ => ⟨cubeMeasure d⟩) (fun _ => inferInstanceAs (SigmaFinite (cubeMeasure d)))
  have hp (g : G → d → ℝ) : (∏ j, F j (g j)) = f (g i) := by simp [F]
  have hi (j : G) : (∫ u, F j u ∂cubeMeasure d) = if j = i then ∫ u, f u ∂cubeMeasure d else 1 := by
    by_cases hj : j = i <;> simp [F, hj]
  change (∫ g : G → d → ℝ, (∏ j, F j (g j)) ∂Measure.pi (fun _ : G => cubeMeasure d)) =
    ∏ j, ∫ u, F j u ∂cubeMeasure d at he
  simp only [hp, hi] at he
  simpa using he

def partialPhysicalCarrierValue (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N : ℝ)
    (B : Representative.Array d V (activeBlocks (d := d) ℓ h) D)
    (e : I ⊕ G ≃ V) (u : I → d → ℝ) (a : I → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (g : G → d → ℝ) : ℝ :=
  pointValue (torusProjection (completedConfiguration e u g))
    (completedSites e a (fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (g j))) ζ B

theorem completedSites_ghost_continuous {X : Type*} [TopologicalSpace X]
    (e : I ⊕ G ≃ V) (a : I → X) (v : V) :
    Continuous (fun g : G → X => completedSites e a g v) := by
  cases hv : e.symm v with
  | inl i => simpa only [completedSites, Function.comp_apply, hv, Sum.elim_inl] using
      (continuous_const : Continuous (fun _ : G → X => a i))
  | inr i => simpa only [completedSites, Function.comp_apply, hv, Sum.elim_inr] using
      (continuous_apply i : Continuous (fun g : G → X => g i))

theorem partialPhysicalCarrierValue_continuous (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N : ℝ) (hc : 0 < c) (B : Representative.Array d V (activeBlocks (d := d) ℓ h) D)
    (e : I ⊕ G ≃ V) (u : I → d → ℝ) (a : I → ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool) :
    Continuous (partialPhysicalCarrierValue x₀ ℓ r h k c w N B e u a ζ) := by
  have hcoord : Continuous (fun g : G → d → ℝ => completedConfiguration e u g) :=
    continuous_pi (fun p => (continuous_apply p.2).comp (completedSites_ghost_continuous e u p.1))
  have hz (v : V) : Continuous (fun g : G → d → ℝ =>
      completedSites e a (fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (g j)) v) :=
    (completedSites_ghost_continuous e a v).comp (continuous_pi (fun j =>
      (normalizedRoughChart_continuous x₀ ℓ r h k c w N hc ζ).comp (continuous_apply j)))
  exact continuous_pointValue _ (torusProjection_quotient.continuous.comp hcoord) _ hz ζ B

theorem partialPhysicalCarrierValue_one_sign_integral_bound
    (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (hℓ : 0 < ℓ) (hr : 0 < r)
    (c w N N₀ : ℝ) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀)
    (B : Representative.Array d V (activeBlocks (d := d) ℓ h) D)
    (e : I ⊕ G ≃ V) (u : I → d → ℝ) (a : I → ℝ) (ha : ∀ i, |a i| ≤ 1)
    (j : activeBlocks (d := d) ℓ h) (ζ ζ' : activeBlocks (d := d) ℓ h → Bool)
    (he : ∀ i, i ≠ j → ζ i = ζ' i) :
    |(∫ g : G → d → ℝ, partialPhysicalCarrierValue x₀ ℓ r h k c w N B e u a ζ g
      ∂Measure.pi (fun _ : G => cubeMeasure d)) -
      ∫ g : G → d → ℝ, partialPhysicalCarrierValue x₀ ℓ r h k c w N B e u a ζ' g
        ∂Measure.pi (fun _ : G => cubeMeasure d)| ≤
      2 * ‖symbolPart j B‖ + ‖B - unit‖ * ((D : ℝ) *
        ((Fintype.card G : ℝ) * ((2 / (c * N)) * (ℓ / (2 * r)) ^ Fintype.card d))) := by
  let μ := Measure.pi (fun _ : G => cubeMeasure d)
  let z := fun η (g : G → d → ℝ) =>
    completedSites e a (fun s => normalizedRoughChart x₀ ℓ r h k c w N η (g s))
  let f := partialPhysicalCarrierValue x₀ ℓ r h k c w N B e u a
  let diff := fun (s : G) (g : G → d → ℝ) =>
    |normalizedRoughChart x₀ ℓ r h k c w N ζ (g s) - normalizedRoughChart x₀ ℓ r h k c w N ζ' (g s)|
  have hz η (g : G → d → ℝ) (v : V) : |z η g v| ≤ 1 := by
    cases hv : e.symm v with
    | inl i => simpa only [z, completedSites, Function.comp_apply, hv, Sum.elim_inl] using ha i
    | inr i => simpa only [z, completedSites, Function.comp_apply, hv, Sum.elim_inr] using
        normalizedRoughChart_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough η (g i)
  have hf η : Integrable (f η) μ :=
    (integrable_const ‖B‖).mono'
      (partialPhysicalCarrierValue_continuous x₀ ℓ r h k c w N hc B e u a η).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun g => by
        simpa only [Real.norm_eq_abs] using pointValue_bound _ _ (hz η g) η B))
  have hd (s : G) : Integrable (diff s) μ := by
    have hc' : Continuous (diff s) :=
      (((normalizedRoughChart_continuous x₀ ℓ r h k c w N hc ζ).comp
        (continuous_apply s : Continuous (fun g : G → d → ℝ => g s))).sub
        ((normalizedRoughChart_continuous x₀ ℓ r h k c w N hc ζ').comp
          (continuous_apply s : Continuous (fun g : G → d → ℝ => g s)))).abs
    apply (integrable_const (2 : ℝ)).mono' hc'.aestronglyMeasurable
    filter_upwards [] with g
    simp only [diff, Real.norm_eq_abs, abs_abs]
    calc
      _ ≤ 1 + 1 := (abs_sub _ _).trans (add_le_add
        (normalizedRoughChart_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough ζ (g s))
        (normalizedRoughChart_bound x₀ ℓ r h k c w N N₀ hc hN₀ hN hm hrough ζ' (g s)))
      _ = _ := by norm_num
  have hs (g : G → d → ℝ) : (∑ v, |z ζ g v - z ζ' g v|) = ∑ s, diff s g := by
    rw [← Equiv.sum_comp e (fun v => |z ζ g v - z ζ' g v|)]
    simp only [Fintype.sum_sum_type, z, completedSites_retained, completedSites_ghost,
      sub_self, abs_zero, Finset.sum_const_zero, zero_add, diff]
  have hb (g : G → d → ℝ) : |f ζ g - f ζ' g| ≤
      2 * ‖symbolPart j B‖ + ‖B - unit‖ * ((D : ℝ) * ∑ s, diff s g) := by
    have hh := pointValue_resample_sub_bound {j} B (torusProjection (completedConfiguration e u g))
      (z ζ g) (z ζ' g) (hz ζ g) (hz ζ' g) ζ ζ'
      (fun i hi => he i (by simpa only [Finset.mem_singleton] using hi))
    simpa only [Finset.sum_singleton, hs, f, partialPhysicalCarrierValue] using hh
  have hsum : Integrable (fun g => ∑ s, diff s g) μ := integrable_finset_sum _ (fun s _ => hd s)
  have hbound := integral_mono ((hf ζ).sub (hf ζ')).abs
    ((integrable_const (2 * ‖symbolPart j B‖)).add ((hsum.const_mul (D : ℝ)).const_mul ‖B - unit‖)) hb
  simp only [Pi.sub_apply, Pi.add_apply] at hbound
  rw [integral_add (integrable_const (2 * ‖symbolPart j B‖))
    ((hsum.const_mul (D : ℝ)).const_mul ‖B - unit‖)] at hbound
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul,
    integral_const_mul] at hbound
  rw [integral_finset_sum Finset.univ (fun s _ => hd s)] at hbound
  have hsum_bound : (∑ s, ∫ g, diff s g ∂μ) ≤ (Fintype.card G : ℝ) *
      ((2 / (c * N)) * (ℓ / (2 * r)) ^ Fintype.card d) := by
    calc
      _ ≤ ∑ _s : G, ((2 / (c * N)) * (ℓ / (2 * r)) ^ Fintype.card d) := by
        apply Finset.sum_le_sum
        intro s _
        rw [show (∫ g, diff s g ∂μ) = ∫ v, |normalizedRoughChart x₀ ℓ r h k c w N ζ v -
          normalizedRoughChart x₀ ℓ r h k c w N ζ' v| ∂cubeMeasure d from
            integral_cube_coordinate (d := d) s (fun v => |normalizedRoughChart x₀ ℓ r h k c w N ζ v -
              normalizedRoughChart x₀ ℓ r h k c w N ζ' v|)]
        exact normalizedRoughChart_one_sign_integral x₀ ℓ r h k hℓ hr c w N hc
          ((div_pos hN₀ hc).trans_le hN) hm j ζ ζ' he
      _ = _ := by simp
  rw [← integral_sub (hf ζ) (hf ζ')]
  exact abs_integral_le_integral_abs.trans (hbound.trans
    (add_le_add_left (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hsum_bound (Nat.cast_nonneg D)) (norm_nonneg _)) _))

namespace Walsh

theorem resample_function_bound {J : Type*} [Fintype J] [DecidableEq J]
    (f : (J → Bool) → ℝ) (C : J → ℝ)
    (hf : ∀ j ζ ζ', (∀ i, i ≠ j → ζ i = ζ' i) → |f ζ - f ζ'| ≤ C j)
    (S : Finset J) (ζ fresh : J → Bool) :
    |f ζ - f (resample S ζ fresh)| ≤ ∑ j ∈ S, C j := by
  induction S using Finset.induction_on generalizing ζ with
  | empty =>
    have he0 : resample ∅ ζ fresh = ζ := by funext i; simp [resample]
    rw [he0]
    simp
  | @insert j S hj ih =>
    let η := resample {j} ζ fresh
    have he : resample S η fresh = resample (insert j S) ζ fresh := by
      funext i
      by_cases hi : i ∈ S <;> by_cases hij : i = j <;> simp [resample, η, hi, hij]
    have hη : ∀ i, i ≠ j → ζ i = η i := by
      intro i hij
      simp [η, resample, hij]
    rw [Finset.sum_insert hj]
    calc
      _ ≤ |f ζ - f η| + |f η - f (resample (insert j S) ζ fresh)| := abs_sub_le _ _ _
      _ ≤ C j + ∑ i ∈ S, C i := by
        apply add_le_add (hf j ζ η hη)
        rw [← he]
        exact ih η

theorem averaged_resample_function_bound {J : Type*} [Fintype J] [DecidableEq J]
    (f : (J → Bool) → ℝ) (C : J → ℝ)
    (hf : ∀ j ζ ζ', (∀ i, i ≠ j → ζ i = ζ' i) → |f ζ - f ζ'| ≤ C j)
    (S : Finset J) (ζ : J → Bool) :
    |f ζ - PartB.independentSigns.expect (fun fresh => f (resample S ζ fresh))| ≤ ∑ j ∈ S, C j := by
  have he := PartB.independentSigns.expect_sub (fun _ : J → Bool => f ζ)
    (fun fresh => f (resample S ζ fresh))
  rw [FiniteLaw.expect_const] at he
  rw [← he]
  exact FiniteLaw.abs_expect_le_bound _ _ _ (fun fresh => resample_function_bound f C hf S ζ fresh)

end Walsh

end CausalLowerbound.PartC
