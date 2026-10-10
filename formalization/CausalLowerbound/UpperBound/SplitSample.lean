import CausalLowerbound.UpperBound.SharedCompletion
import CausalLowerbound.UpperBound.OverlapCounting
import CausalLowerbound.FiniteProductMeasures

/-! Sampling one observation per independent role group.  The observations
have an arbitrary probability law, and kernels have only a second moment. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace CausalLowerbound.UpperBound

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {J : I → Type*} [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]
variable {Z : Type*} [MeasurableSpace Z]

def tupleObservation (a : ∀ i, J i) (x : (Σ i, J i) → Z) (i : I) : Z := x ⟨i, a i⟩

omit [DecidableEq I] [∀ i, DecidableEq (J i)] in
theorem tupleObservation_measurePreserving (μ : Measure Z) [IsProbabilityMeasure μ]
    (a : ∀ i, J i) :
    MeasurePreserving (tupleObservation a) (Measure.pi (fun _ : Σ i, J i => μ))
      (Measure.pi (fun _ : I => μ)) := by
  apply measurePreserving_coordinateSelection
  intro i j h
  exact congrArg Sigma.fst h

def joinRoles (S : Finset I) :
    (({i // i ∈ S} → Z) × ({i // i ∉ S} → Z)) ≃ᵐ (I → Z) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => Z) (fun i => i ∈ S)).symm

theorem joinRoles_measurePreserving (μ : Measure Z) [IsProbabilityMeasure μ]
    (S : Finset I) :
    MeasurePreserving (joinRoles (Z := Z) S)
      ((Measure.pi (fun _ : {i // i ∈ S} => μ)).prod
        (Measure.pi (fun _ : {i // i ∉ S} => μ)))
      (Measure.pi (fun _ : I => μ)) := by
  convert (measurePreserving_piEquivPiSubtypeProd
    (fun _ : I => μ) (fun i => i ∈ S)).symm using 1
  congr 2
  exact Subsingleton.elim _ _

/-- The actual partial kernel, obtained by integrating the unshared roles. -/
def roleProjection (μ : Measure Z) (K : (I → Z) → ℝ) (S : Finset I)
    (x : {i // i ∈ S} → Z) : ℝ :=
  ∫ y : {i // i ∉ S} → Z, K (joinRoles S (x, y))
    ∂Measure.pi (fun _ : {i // i ∉ S} => μ)

def pairRoleIndex (S : Finset I) := {i // i ∈ S} ⊕ ({i // i ∉ S} ⊕ {i // i ∉ S})

instance (S : Finset I) : Fintype (pairRoleIndex S) := inferInstanceAs
  (Fintype ({i // i ∈ S} ⊕ ({i // i ∉ S} ⊕ {i // i ∉ S})))

def pairSelection (a b : ∀ i, J i) : pairRoleIndex (overlap a b) → Σ i, J i
  | Sum.inl i => ⟨i, a i⟩
  | Sum.inr (Sum.inl i) => ⟨i, a i⟩
  | Sum.inr (Sum.inr i) => ⟨i, b i⟩

omit [DecidableEq I] [∀ i, Fintype (J i)] in
theorem pairSelection_injective (a b : ∀ i, J i) :
    Function.Injective (pairSelection a b) := by
  intro u v h
  have idx := congrArg Sigma.fst h
  rcases u with u | (u | u) <;> rcases v with v | (v | v) <;>
    dsimp only [pairSelection] at idx h
  · exact congrArg Sum.inl (Subtype.ext idx)
  · exact False.elim (v.property (idx ▸ u.property))
  · exact False.elim (v.property (idx ▸ u.property))
  · exact False.elim (u.property (idx.symm ▸ v.property))
  · exact congrArg (Sum.inr ∘ Sum.inl) (Subtype.ext idx)
  · have huv : u = v := Subtype.ext idx
    subst v
    have hab : a u = b u := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    exact False.elim (u.property ((mem_overlap a b u).mpr hab))
  · exact False.elim (u.property (idx.symm ▸ v.property))
  · have huv : u = v := Subtype.ext idx
    subst v
    have hab : b u = a u := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    exact False.elim (u.property ((mem_overlap a b u).mpr hab.symm))
  · exact congrArg (Sum.inr ∘ Sum.inr) (Subtype.ext idx)

def pairObservation (a b : ∀ i, J i) (x : (Σ i, J i) → Z) :
    ({i // i ∈ overlap a b} → Z) ×
      (({i // i ∉ overlap a b} → Z) × ({i // i ∉ overlap a b} → Z)) :=
  (fun i => x ⟨i, a i⟩, (fun i => x ⟨i, a i⟩, fun i => x ⟨i, b i⟩))

theorem pairObservation_measurePreserving (μ : Measure Z) [IsProbabilityMeasure μ]
    (a b : ∀ i, J i) :
    MeasurePreserving (pairObservation a b) (Measure.pi (fun _ : Σ i, J i => μ))
      ((Measure.pi (fun _ : {i // i ∈ overlap a b} => μ)).prod
        ((Measure.pi (fun _ : {i // i ∉ overlap a b} => μ)).prod
          (Measure.pi (fun _ : {i // i ∉ overlap a b} => μ)))) := by
  have hselect := measurePreserving_coordinateSelection μ (pairSelection a b)
    (pairSelection_injective a b)
  have hsplit := measurePreserving_sumPiEquivProdPi
    (fun _ : {i // i ∈ overlap a b} ⊕
      ({i // i ∉ overlap a b} ⊕ {i // i ∉ overlap a b}) => μ)
  have hsplit' := measurePreserving_sumPiEquivProdPi
    (fun _ : {i // i ∉ overlap a b} ⊕ {i // i ∉ overlap a b} => μ)
  exact ((MeasurePreserving.id (Measure.pi (fun _ : {i // i ∈ overlap a b} => μ))).prod
    hsplit').comp (hsplit.comp hselect)

omit [∀ i, Fintype (J i)] in
theorem join_pairObservation_fst (a b : ∀ i, J i) (x : (Σ i, J i) → Z) :
    joinRoles (overlap a b) ((pairObservation a b x).1, (pairObservation a b x).2.1) =
      tupleObservation a x := by
  funext i
  by_cases hi : i ∈ overlap a b <;>
    simp [joinRoles, MeasurableEquiv.piEquivPiSubtypeProd,
      Equiv.piEquivPiSubtypeProd, pairObservation, tupleObservation, hi]

omit [∀ i, Fintype (J i)] in
theorem join_pairObservation_snd (a b : ∀ i, J i) (x : (Σ i, J i) → Z) :
    joinRoles (overlap a b) ((pairObservation a b x).1, (pairObservation a b x).2.2) =
      tupleObservation b x := by
  funext i
  by_cases hi : i ∈ overlap a b
  · have hab := (mem_overlap a b i).mp hi
    simp [joinRoles, MeasurableEquiv.piEquivPiSubtypeProd,
      Equiv.piEquivPiSubtypeProd, pairObservation, tupleObservation, hi, hab]
  · simp [joinRoles, MeasurableEquiv.piEquivPiSubtypeProd,
      Equiv.piEquivPiSubtypeProd, pairObservation, tupleObservation, hi]
    intro hab
    rw [hab]

theorem covariance_tuple_observations (μ : Measure Z) [IsProbabilityMeasure μ]
    {K : (I → Z) → ℝ} (hK : MemLp K 2 (Measure.pi (fun _ : I => μ)))
    (a b : ∀ i, J i) :
    covariance (Measure.pi (fun _ : Σ i, J i => μ))
      (K ∘ tupleObservation a) (K ∘ tupleObservation b) =
      variance (Measure.pi (fun _ : {i // i ∈ overlap a b} => μ))
        (roleProjection μ K (overlap a b)) := by
  let μS := Measure.pi (fun _ : {i // i ∈ overlap a b} => μ)
  let νS := Measure.pi (fun _ : {i // i ∉ overlap a b} => μ)
  have hsplit := hK.comp_measurePreserving (joinRoles_measurePreserving μ (overlap a b))
  have hc := covariance_comp_measurePreserving (pairObservation_measurePreserving μ a b)
    (completion_fst_memLp μS νS hsplit) (completion_snd_memLp μS νS hsplit)
  have he := covariance_shared_completion μS νS hsplit
  rw [he] at hc
  convert hc using 1
  simp only [Function.comp_def, join_pairObservation_fst, join_pairObservation_snd]

/-- Exact finite-sample variance of the split tuple average.  The projections
and overlap weights are both explicitly constructed and proved above. -/
theorem variance_splitSample (μ : Measure Z) [IsProbabilityMeasure μ]
    [∀ i, Nonempty (J i)] {K : (I → Z) → ℝ}
    (hK : MemLp K 2 (Measure.pi (fun _ : I => μ))) :
    variance (Measure.pi (fun _ : Σ i, J i => μ))
      (tupleAverage (fun a => K ∘ tupleObservation a)) =
      ∑ S : Finset I, overlapWeight J S *
        variance (Measure.pi (fun _ : {i // i ∈ S} => μ)) (roleProjection μ K S) := by
  exact variance_tupleAverage_of_overlap _ _
    (fun a => hK.comp_measurePreserving (tupleObservation_measurePreserving μ a))
    _ (covariance_tuple_observations μ hK)

theorem roleProjection_memLp (μ : Measure Z) [IsProbabilityMeasure μ]
    {K : (I → Z) → ℝ} (hK : MemLp K 2 (Measure.pi (fun _ : I => μ)))
    (S : Finset I) :
    MemLp (roleProjection μ K S) 2 (Measure.pi (fun _ : {i // i ∈ S} => μ)) :=
  partialKernel_memLp _ _ (hK.comp_measurePreserving (joinRoles_measurePreserving μ S))

@[simp] theorem variance_roleProjection_empty (μ : Measure Z) [IsProbabilityMeasure μ]
    (K : (I → Z) → ℝ) :
    variance (Measure.pi (fun _ : {i // i ∈ (∅ : Finset I)} => μ))
      (roleProjection μ K ∅) = 0 := by
  let x₀ : {i // i ∈ (∅ : Finset I)} → Z := fun i =>
    False.elim ((Finset.not_mem_empty i.val) i.property)
  have he : roleProjection μ K ∅ = fun _ => roleProjection μ K ∅ x₀ := by
    funext x
    congr 1
    funext i
    exact False.elim ((Finset.not_mem_empty i.val) i.property)
  rw [he, variance_const]

theorem variance_splitSample_nonempty (μ : Measure Z) [IsProbabilityMeasure μ]
    [∀ i, Nonempty (J i)] {K : (I → Z) → ℝ}
    (hK : MemLp K 2 (Measure.pi (fun _ : I => μ))) :
    variance (Measure.pi (fun _ : Σ i, J i => μ))
      (tupleAverage (fun a => K ∘ tupleObservation a)) =
      ∑ S ∈ Finset.univ.erase (∅ : Finset I), overlapWeight J S *
        variance (Measure.pi (fun _ : {i // i ∈ S} => μ)) (roleProjection μ K S) := by
  rw [variance_splitSample μ hK]
  symm
  simpa only [variance_roleProjection_empty, mul_zero, add_zero] using
    (Finset.sum_erase_add (s := Finset.univ)
      (f := fun S : Finset I => overlapWeight J S *
        variance (Measure.pi (fun _ : {i // i ∈ S} => μ)) (roleProjection μ K S))
      (Finset.mem_univ (∅ : Finset I)))

theorem variance_splitSample_le_projection_moments (μ : Measure Z)
    [IsProbabilityMeasure μ] [∀ i, Nonempty (J i)] {K : (I → Z) → ℝ}
    (hK : MemLp K 2 (Measure.pi (fun _ : I => μ))) :
    variance (Measure.pi (fun _ : Σ i, J i => μ))
      (tupleAverage (fun a => K ∘ tupleObservation a)) ≤
      ∑ S ∈ Finset.univ.erase (∅ : Finset I), overlapWeight J S *
        ∫ x, roleProjection μ K S x ^ 2 ∂Measure.pi (fun _ : {i // i ∈ S} => μ) := by
  rw [variance_splitSample_nonempty μ hK]
  apply Finset.sum_le_sum
  intro S _
  exact mul_le_mul_of_nonneg_left (variance_le_secondMoment _ _) (overlapWeight_nonneg S)

end CausalLowerbound.UpperBound
