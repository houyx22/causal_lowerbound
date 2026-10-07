import CausalLowerbound.PartC.RepresentativeEvaluation

/-! Degree substitutions multiply the retained Fourier coefficients and
move rows without changing their explicit Walsh symbols. Their norm and
symbol bounds have no factor depending on the number of rough signs. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartC.Representative

variable {d ι J : Type*} [Fintype d] [Fintype ι] [Fintype J]
  [DecidableEq ι] [DecidableEq J] {D : ℕ}

def fourierMultiplier (w : Wiener.Fourier (ι × d)) :
    Wiener.Fourier (ι × d) →L[ℝ] Wiener.Fourier (ι × d) :=
  (Wiener.convolutionRight w).restrictScalars ℝ

@[simp] theorem fourierMultiplier_apply (w a : Wiener.Fourier (ι × d)) : fourierMultiplier w a = a * w := rfl

def degreeSubstitution (g : Degree ι D → Degree ι D)
    (w : Degree ι D → Wiener.Fourier (ι × d)) (C : ℝ) (hw : ∀ e, ‖w e‖ ≤ C) :
    Array d ι J D →L[ℝ] Array d ι J D :=
  FiniteL1.transform (fun r : Row ι J D => (g r.1, r.2)) (fun r => fourierMultiplier (w r.1)) C
    (fun r a => (norm_mul_le a (w r.1)).trans
      ((mul_le_mul_of_nonneg_left (hw r.1) (norm_nonneg a)).trans_eq (mul_comm _ _)))

theorem degreeSubstitution_bound (g : Degree ι D → Degree ι D)
    (w : Degree ι D → Wiener.Fourier (ι × d)) (C : ℝ) (hw : ∀ e, ‖w e‖ ≤ C) (a : Array d ι J D) :
    ‖degreeSubstitution g w C hw a‖ ≤ C * ‖a‖ :=
  FiniteL1.transform_bound _ _ C _ a

theorem degreeSubstitution_single (g : Degree ι D → Degree ι D)
    (w : Degree ι D → Wiener.Fourier (ι × d)) (C : ℝ) (hw : ∀ e, ‖w e‖ ≤ C)
    (r : Row ι J D) (a : Wiener.Fourier (ι × d)) :
    degreeSubstitution g w C hw (lp.single 1 r a) = lp.single 1 (g r.1, r.2) (a * w r.1) :=
  FiniteL1.transform_single _ _ C _ r a

theorem symbolProject_single (p : Finset J → Prop) [DecidablePred p]
    (r : Row ι J D) (a : Wiener.Fourier (ι × d)) :
    FiniteL1.project (fun s : Row ι J D => p s.2) (lp.single 1 r a) =
      lp.single 1 r (if p r.2 then a else 0) := by
  unfold FiniteL1.project FiniteL1.diagonal
  rw [FiniteL1.transform_single]
  dsimp only [id_eq]
  split_ifs <;> rfl

theorem degreeSubstitution_symbolProject (g : Degree ι D → Degree ι D)
    (w : Degree ι D → Wiener.Fourier (ι × d)) (C : ℝ) (hw : ∀ e, ‖w e‖ ≤ C)
    (p : Finset J → Prop) [DecidablePred p] (a : Array d ι J D) :
    FiniteL1.project (fun s : Row ι J D => p s.2) (degreeSubstitution g w C hw a) =
      degreeSubstitution g w C hw (FiniteL1.project (fun s : Row ι J D => p s.2) a) := by
  rw [← FiniteL1.sum_single a]
  simp only [map_sum, degreeSubstitution_single, symbolProject_single]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> simp only [zero_mul]

theorem degreeSubstitution_symbol_bound (g : Degree ι D → Degree ι D)
    (w : Degree ι D → Wiener.Fourier (ι × d)) (C : ℝ) (hw : ∀ e, ‖w e‖ ≤ C)
    (a : Array d ι J D) (j : J) :
    ‖symbolPart j (degreeSubstitution g w C hw a)‖ ≤ C * ‖symbolPart j a‖ := by
  have he := degreeSubstitution_symbolProject g w C hw (fun s => j ∈ s) a
  change symbolPart j (degreeSubstitution g w C hw a) = degreeSubstitution g w C hw (symbolPart j a) at he
  rw [he]
  exact degreeSubstitution_bound g w C hw _

theorem degreeSubstitution_remove (g : Degree ι D → Degree ι D)
    (w : Degree ι D → Wiener.Fourier (ι × d)) (C : ℝ) (hw : ∀ e, ‖w e‖ ≤ C)
    (a : Array d ι J D) (S : Finset J) :
    remove S (degreeSubstitution g w C hw a) = degreeSubstitution g w C hw (remove S a) :=
  degreeSubstitution_symbolProject g w C hw (fun s => Disjoint s S) a

theorem degreeSubstitution_value (g : Degree ι D → Degree ι D)
    (w : Degree ι D → Wiener.Fourier (ι × d)) (C : ℝ) (hw : ∀ e, ‖w e‖ ≤ C)
    (x : Wiener.Torus (ι × d)) (z : ι → ℝ) (ζ : J → Bool)
    (hre : ∀ e, (Wiener.toContinuous (w e) x).im = 0) (a : Array d ι J D) :
    pointValue x z ζ (degreeSubstitution g w C hw a) =
      ∑ r : Row ι J D, rowWeight (g r.1, r.2) z ζ *
        ((Wiener.toContinuous (a r) x).re * (Wiener.toContinuous (w r.1) x).re) := by
  change pointValue x z ζ (∑ r : Row ι J D, lp.single 1 (g r.1, r.2) (a r * w r.1)) = _
  rw [pointValue_sum]
  simp only [pointValue_single, Wiener.toContinuous_mul, ContinuousMap.mul_apply,
    Complex.mul_re, hre, mul_zero, sub_zero]

end CausalLowerbound.PartC.Representative
