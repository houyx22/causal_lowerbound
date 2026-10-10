import CausalLowerbound.UpperBound.StarCompletion
import CausalLowerbound.UpperBound.AcceptedVolume

/-! The mixed-scale completion bounds for the actual observed stencil.
There is one exceptional (fine-scale) partner role; all auxiliary boxes
have the same coarse volume. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open CausalLowerbound.PartB.ShellGeometry
open scoped BigOperators ENNReal Classical

namespace CausalLowerbound.UpperBound

theorem prod_one_exception {I R : Type*} [Fintype I] [DecidableEq I] [CommMonoid R]
    (a : I) (f : I → R) (b : R) (hb : ∀ i, i ≠ a → f i = b) :
    (∏ i, f i) = f a * b ^ (Fintype.card I - 1) := by
  rw [Fintype.prod_eq_mul_prod_compl a f]
  calc
    _ = f a * ∏ _i ∈ ({a} : Finset I)ᶜ, b := by
      congr 1
      exact Finset.prod_congr rfl (fun i hi => hb i (by simpa using hi))
    _ = _ := by simp [Finset.card_compl]

variable {d : Type*} [Fintype d]

def stencilRoleShift (p : ℕ) (x₀ : d → ℝ) (ℓ r : ℝ) : StencilRole d p → d → ℝ :=
  Option.elim' (ℓ • inwardReflection x₀ (fun _ => 1 / 2))
    (Option.elim' 0 (fun j => r • inwardReflection x₀ (gridNode p j)))

def stencilRoleRadius (p : ℕ) (T : StencilTemplate d p) (ℓ r : ℝ) : StencilRole d p → ℝ :=
  Option.elim' (ℓ / 2) (fun _ => r * T.radius)

def coarseCellVolume (p : ℕ) (T : StencilTemplate d p) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * r * T.radius) ^ Fintype.card d

def fineCellVolume (d : Type*) [Fintype d] (ℓ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ℓ ^ Fintype.card d

theorem stencilRoleRadius_partner (p : ℕ) (T : StencilTemplate d p) (ℓ r : ℝ) :
    ENNReal.ofReal (2 * stencilRoleRadius p T ℓ r none) ^ Fintype.card d =
      fineCellVolume d ℓ := by
  simp only [stencilRoleRadius, Option.elim'_none, fineCellVolume]
  rw [show (2 : ℝ) * (ℓ / 2) = ℓ by ring]

theorem stencilRoleRadius_other (p : ℕ) (T : StencilTemplate d p) (ℓ r : ℝ)
    (i : StencilRole d p) (hi : i ≠ none) :
    ENNReal.ofReal (2 * stencilRoleRadius p T ℓ r i) ^ Fintype.card d = coarseCellVolume p T r := by
  cases i with
  | none => exact (hi rfl).elim
  | some j => simp only [stencilRoleRadius, Option.elim'_some, coarseCellVolume, mul_assoc]

theorem acceptedStencil_eq_starCluster (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (hr : 0 < r) :
    acceptedStencil p T x₀ h ℓ r =
      starCluster (some none) (coordinateBox (x₀ + h • inwardReflection x₀ (fun _ => 1 / 8)) (h / 8))
        (stencilRoleShift p x₀ ℓ r) (stencilRoleRadius p T ℓ r) := by
  rw [acceptedStencil_eq_mixedCluster p T x₀ hh hℓ hr]
  ext X
  simp [starCluster, mixedCluster, stencilAnchorSplit, stencilRoleShift, stencilRoleRadius,
    stencilPhysicalShift, stencilPhysicalRadius, Option.forall]

theorem stencilCompletion_volume_both_shared (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (hr : 0 < r)
    (S : Finset (StencilRole d p)) (ha : some none ∈ S) (hb : none ∈ S)
    (x : {i // i ∈ S} → d → ℝ) :
    volume {y | joinRoles S (x, y) ∈ acceptedStencil p T x₀ h ℓ r} ≤
      coarseCellVolume p T r ^ Fintype.card {i // i ∉ S} := by
  rw [acceptedStencil_eq_starCluster p T x₀ hh hℓ hr]
  apply (starCompletion_volume_shared_anchor _ _ _ _ S ha x).trans_eq
  have he (i : {i // i ∉ S}) : (i : StencilRole d p) ≠ none :=
    fun h => i.property (h.symm ▸ hb)
  calc
    _ = ∏ _i : {i // i ∉ S}, coarseCellVolume p T r :=
      Finset.prod_congr rfl (fun i _ => stencilRoleRadius_other p T ℓ r i (he i))
    _ = _ := by simp

theorem stencilCompletion_volume_anchor_shared (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (hr : 0 < r)
    (S : Finset (StencilRole d p)) (ha : some none ∈ S) (hb : none ∉ S)
    (x : {i // i ∈ S} → d → ℝ) :
    volume {y | joinRoles S (x, y) ∈ acceptedStencil p T x₀ h ℓ r} ≤
      fineCellVolume d ℓ * coarseCellVolume p T r ^ (Fintype.card {i // i ∉ S} - 1) := by
  rw [acceptedStencil_eq_starCluster p T x₀ hh hℓ hr]
  apply (starCompletion_volume_shared_anchor _ _ _ _ S ha x).trans_eq
  rw [prod_one_exception (⟨none, hb⟩ : {i // i ∉ S}) _ (coarseCellVolume p T r)
    (fun i hi => stencilRoleRadius_other p T ℓ r i (fun he => hi (Subtype.ext he))),
    stencilRoleRadius_partner]

theorem stencilCompletion_volume_partner_shared (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (hr : 0 < r)
    (S : Finset (StencilRole d p)) (ha : some none ∉ S) (hb : none ∈ S)
    (x : {i // i ∈ S} → d → ℝ) :
    volume {y | joinRoles S (x, y) ∈ acceptedStencil p T x₀ h ℓ r} ≤
      fineCellVolume d ℓ * coarseCellVolume p T r ^ (Fintype.card {i // i ∉ S} - 1) := by
  rw [acceptedStencil_eq_starCluster p T x₀ hh hℓ hr]
  apply (starCompletion_volume_missing_anchor _ _ _ _ S ha x ⟨none, hb⟩).trans_eq
  rw [stencilRoleRadius_partner]
  congr 1
  have he (i : {i : {i // i ∉ S} // i ≠ ⟨some none, ha⟩}) :
      i.val.val ≠ none := fun h => i.val.property (h.symm ▸ hb)
  calc
    _ = ∏ _i : {i : {i // i ∉ S} // i ≠ ⟨some none, ha⟩}, coarseCellVolume p T r :=
      Finset.prod_congr rfl (fun i _ => stencilRoleRadius_other p T ℓ r i.val.val (he i))
    _ = _ := by simp

theorem stencilCompletion_volume_neither_shared (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (hr : 0 < r)
    (S : Finset (StencilRole d p)) (hS : S.Nonempty)
    (ha : some none ∉ S) (hb : none ∉ S) (x : {i // i ∈ S} → d → ℝ) :
    volume {y | joinRoles S (x, y) ∈ acceptedStencil p T x₀ h ℓ r} ≤
      fineCellVolume d ℓ * coarseCellVolume p T r ^ (Fintype.card {i // i ∉ S} - 1) := by
  obtain ⟨j, hj⟩ := hS
  let a : {i // i ∉ S} := ⟨some none, ha⟩
  let J := {i : {i // i ∉ S} // i ≠ a}
  let b : J := ⟨⟨none, hb⟩, by
    intro he
    have he' := congrArg Subtype.val he
    cases he'⟩
  have hjb : j ≠ none := fun he => hb (he ▸ hj)
  have hcard : Fintype.card J = Fintype.card {i // i ∉ S} - 1 := by
    simp [J, a]
  have hpos : 0 < Fintype.card J := Fintype.card_pos_iff.mpr ⟨b⟩
  have he (i : J) (hi : i ≠ b) : i.val.val ≠ none := by
    intro h
    exact hi (Subtype.ext (Subtype.ext h))
  rw [acceptedStencil_eq_starCluster p T x₀ hh hℓ hr]
  apply (starCompletion_volume_missing_anchor _ _ _ _ S ha x ⟨j, hj⟩).trans_eq
  change ENNReal.ofReal (2 * stencilRoleRadius p T ℓ r j) ^ Fintype.card d *
    (∏ i : J, ENNReal.ofReal (2 * stencilRoleRadius p T ℓ r i.val.val) ^ Fintype.card d) = _
  rw [stencilRoleRadius_other p T ℓ r j hjb,
    prod_one_exception b _ (coarseCellVolume p T r)
      (fun i hi => stencilRoleRadius_other p T ℓ r i.val.val (he i hi))]
  change coarseCellVolume p T r *
    (ENNReal.ofReal (2 * stencilRoleRadius p T ℓ r none) ^ Fintype.card d *
      coarseCellVolume p T r ^ (Fintype.card J - 1)) = _
  rw [stencilRoleRadius_partner]
  calc
    _ = fineCellVolume d ℓ *
        (coarseCellVolume p T r ^ (Fintype.card J - 1) * coarseCellVolume p T r) := by ac_rfl
    _ = fineCellVolume d ℓ * coarseCellVolume p T r ^ Fintype.card J := by
      rw [← pow_succ, Nat.sub_add_cancel hpos]
    _ = _ := by rw [hcard]

def stencilCompletionVolumeBound (p : ℕ) (T : StencilTemplate d p) (ℓ r : ℝ)
    (S : Finset (StencilRole d p)) : ℝ≥0∞ :=
  if some none ∈ S ∧ none ∈ S then
    coarseCellVolume p T r ^ Fintype.card {i // i ∉ S}
  else fineCellVolume d ℓ * coarseCellVolume p T r ^ (Fintype.card {i // i ∉ S} - 1)

theorem stencilCompletionVolumeBound_ne_top (p : ℕ) (T : StencilTemplate d p) (ℓ r : ℝ)
    (S : Finset (StencilRole d p)) : stencilCompletionVolumeBound p T ℓ r S ≠ ⊤ := by
  unfold stencilCompletionVolumeBound coarseCellVolume fineCellVolume
  split
  · exact ENNReal.pow_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  · exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.pow_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))

theorem stencilCompletion_volume_le (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) {h ℓ r : ℝ} (hh : 0 < h) (hℓ : 0 < ℓ) (hr : 0 < r)
    (S : Finset (StencilRole d p)) (hS : S.Nonempty) (x : {i // i ∈ S} → d → ℝ) :
    volume {y | joinRoles S (x, y) ∈ acceptedStencil p T x₀ h ℓ r} ≤
      stencilCompletionVolumeBound p T ℓ r S := by
  by_cases ha : some none ∈ S <;> by_cases hb : none ∈ S
  · simpa only [stencilCompletionVolumeBound, ha, hb, and_self, if_true] using
      stencilCompletion_volume_both_shared p T x₀ hh hℓ hr S ha hb x
  · simpa only [stencilCompletionVolumeBound, and_false, hb, if_false] using
      stencilCompletion_volume_anchor_shared p T x₀ hh hℓ hr S ha hb x
  · simpa only [stencilCompletionVolumeBound, false_and, ha, if_false] using
      stencilCompletion_volume_partner_shared p T x₀ hh hℓ hr S ha hb x
  · simpa only [stencilCompletionVolumeBound, false_and, ha, if_false] using
      stencilCompletion_volume_neither_shared p T x₀ hh hℓ hr S hS ha hb x

end CausalLowerbound.UpperBound
