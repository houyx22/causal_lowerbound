import CausalLowerbound.WienerRealExpansion

/-! # The complete algebra of symmetric real Wiener functions -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.Wiener

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d]

/-- Reality and symmetry are conditions on the actual continuous function. -/
def symmetricRealSubalgebra : Subalgebra ℝ (Fourier (ι × d)) where
  carrier := {a | (∀ x, (toContinuous a x).im = 0) ∧
    ∀ σ : Equiv.Perm ι, ∀ x, toContinuous a (permuteSlots σ x) = toContinuous a x}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha, hsa⟩ ⟨hb, hsb⟩
    constructor
    · intro x; simp [ha, hb]
    · intro σ x; simp [hsa, hsb]
  mul_mem' := by
    rintro a b ⟨ha, hsa⟩ ⟨hb, hsb⟩
    constructor
    · intro x; simp [Complex.mul_im, ha, hb]
    · intro σ x; simp [hsa, hsb]
  algebraMap_mem' := by
    intro r
    rw [Algebra.algebraMap_eq_smul_one]
    constructor <;> intros <;> simp

abbrev SymmetricReal (d ι : Type*) [Fintype d] [Fintype ι] [DecidableEq ι] :=
  ↥(symmetricRealSubalgebra (d := d) (ι := ι))

instance symmetricReal_normedSpace : NormedSpace ℝ (SymmetricReal d ι) where
  norm_smul_le r a := norm_smul_le r (a : Fourier (ι × d))

instance symmetricReal_normedAlgebra : NormedAlgebra ℝ (SymmetricReal d ι) where
  norm_smul_le := norm_smul_le

theorem symmetricReal_isClosed :
    IsClosed (symmetricRealSubalgebra (d := d) (ι := ι) : Set (Fourier (ι × d))) := by
  change IsClosed {a : Fourier (ι × d) | (∀ x, (toContinuous a x).im = 0) ∧
    ∀ σ : Equiv.Perm ι, ∀ x, toContinuous a (permuteSlots σ x) = toContinuous a x}
  simp only [Set.setOf_and, Set.setOf_forall]
  apply IsClosed.inter
  · apply isClosed_iInter; intro x
    exact isClosed_eq (Complex.continuous_im.comp (evaluation x).continuous) continuous_const
  · apply isClosed_iInter; intro σ
    apply isClosed_iInter; intro x
    exact isClosed_eq (evaluation (permuteSlots σ x)).continuous (evaluation x).continuous

instance symmetricReal_complete : CompleteSpace (SymmetricReal d ι) :=
  symmetricReal_isClosed.completeSpace_coe

instance symmetricReal_normOne : NormOneClass (SymmetricReal d ι) where
  norm_one := norm_one (α := Fourier (ι × d))

def symmetricInclusion : SymmetricReal d ι →L[ℝ] Fourier (ι × d) :=
  (symmetricRealSubalgebra (d := d) (ι := ι)).toSubmodule.subtypeL

@[simp]
theorem symmetricInclusion_apply (a : SymmetricReal d ι) : symmetricInclusion a = a := rfl

def symmetricExpansion : SymmetricReal d ι →L[ℝ]
    Series (PartB.PositiveWiener.BasisIndex d ι) ℝ :=
  realExpansion.comp symmetricInclusion

theorem symmetricExpansion_bound (a : SymmetricReal d ι) :
    ‖symmetricExpansion a‖ ≤ (2 : ℝ) ^ Fintype.card ι * ‖a‖ := by
  exact realExpansion_bound (d := d) (ι := ι) (a : Fourier (ι × d))

theorem symmetricExpansion_reconstruction (a : SymmetricReal d ι) :
    PartB.PositiveWiener.realTensorSynthesis (symmetricExpansion a) =
      (a : Fourier (ι × d)) := by
  exact realExpansion_reconstruction (d := d) (ι := ι)
    (a : Fourier (ι × d)) a.property.1 a.property.2

end CausalLowerbound.Wiener
