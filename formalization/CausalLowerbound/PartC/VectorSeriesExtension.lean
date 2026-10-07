import CausalLowerbound.PartC.VectorSeries

/-! Injective reindexing of Banach-valued coefficient families, with zero
coefficients outside the image. The absolute coefficient norm is preserved. -/

noncomputable section
set_option autoImplicit false
open scoped ENNReal Classical

namespace CausalLowerbound.PartC.VectorSeries

variable {I K E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_extend (f : I → K) (hf : Function.Injective f) (a : I → E) (k : K) :
    ‖Function.extend f a 0 k‖ = Function.extend f (fun i => ‖a i‖) 0 k := by
  by_cases hk : k ∈ Set.range f
  · obtain ⟨i, rfl⟩ := hk
    simp only [hf.extend_apply]
  · rw [Function.extend_apply' (f := f) a (0 : K → E) k hk,
      Function.extend_apply' (f := f) (fun i => ‖a i‖) (0 : K → ℝ) k hk]
    exact norm_zero

def extendFamily (f : I → K) (hf : Function.Injective f) (a : Family I E) : Family K E :=
  ⟨Function.extend f a 0, memℓp_gen (by
    simpa only [norm_extend f hf, ENNReal.toReal_one, Real.rpow_one] using
      ((hasSum_extend_zero hf).mpr (hasSum_norm a)).summable)⟩

@[simp] theorem extendFamily_image (f : I → K) (hf : Function.Injective f)
    (a : Family I E) (i : I) : extendFamily f hf a (f i) = a i := hf.extend_apply a 0 i

theorem extendFamily_outside (f : I → K) (hf : Function.Injective f)
    (a : Family I E) (k : K) (hk : k ∉ Set.range f) : extendFamily f hf a k = 0 :=
  Function.extend_apply' (f := f) a (0 : K → E) k hk

theorem extendFamily_norm (f : I → K) (hf : Function.Injective f) (a : Family I E) :
    ‖extendFamily f hf a‖ = ‖a‖ := by
  apply (hasSum_norm (extendFamily f hf a)).unique
  simpa only [extendFamily, norm_extend f hf] using
    (hasSum_extend_zero hf).mpr (hasSum_norm a)

def extend (f : I → K) (hf : Function.Injective f) : Family I E →L[ℝ] Family K E :=
  LinearMap.mkContinuous
    { toFun := extendFamily f hf
      map_add' := by
        intro a b
        apply lp.ext
        funext k
        by_cases hk : k ∈ Set.range f
        · obtain ⟨i, rfl⟩ := hk
          simp only [lp.coeFn_add, Pi.add_apply, extendFamily_image]
        · simp only [lp.coeFn_add, Pi.add_apply, extendFamily_outside f hf _ k hk, add_zero]
      map_smul' := by
        intro c a
        apply lp.ext
        funext k
        by_cases hk : k ∈ Set.range f
        · obtain ⟨i, rfl⟩ := hk
          simp only [lp.coeFn_smul, Pi.smul_apply, extendFamily_image, RingHom.id_apply]
        · simp only [lp.coeFn_smul, Pi.smul_apply, extendFamily_outside f hf _ k hk,
            RingHom.id_apply, smul_zero] }
    1 (fun a => by
      change ‖extendFamily f hf a‖ ≤ 1 * ‖a‖
      rw [extendFamily_norm, one_mul])

@[simp] theorem extend_image (f : I → K) (hf : Function.Injective f)
    (a : Family I E) (i : I) : extend f hf a (f i) = a i := extendFamily_image f hf a i

theorem extend_outside (f : I → K) (hf : Function.Injective f)
    (a : Family I E) (k : K) (hk : k ∉ Set.range f) : extend f hf a k = 0 :=
  extendFamily_outside f hf a k hk

theorem extend_norm (f : I → K) (hf : Function.Injective f) (a : Family I E) :
    ‖extend f hf a‖ = ‖a‖ := extendFamily_norm f hf a

theorem extend_hasSum {F : Type*} [NormedAddCommGroup F]
    (f : I → K) (hf : Function.Injective f) (a : Family I E)
    (g : K → E → F) (hg : ∀ k, g k 0 = 0) (b : F)
    (hs : HasSum (fun i => g (f i) (a i)) b) :
    HasSum (fun k => g k (extend f hf a k)) b := by
  apply (hf.hasSum_iff (fun k hk => by rw [extend_outside f hf a k hk, hg k])).mp
  simpa only [Function.comp_def, extend_image] using hs

end CausalLowerbound.PartC.VectorSeries
