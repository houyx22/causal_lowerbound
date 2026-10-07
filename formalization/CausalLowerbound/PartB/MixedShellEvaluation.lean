import CausalLowerbound.PartB.MixedShellWiener
import CausalLowerbound.PartB.ConfigurationPeriodization

/-! The compact graph profile is exactly the original shell multiplier,
with one small scale for each occurrence of a fine elementary factor. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartB.ShellGeometry

open Wiener ConfigurationShells
variable {V F C d R : Type*} [Fintype V] [DecidableEq V]
  [Fintype F] [Fintype C] [Fintype d] [Fintype R]

def actualEdgeDistance (af bf : F → V) (ac bc : C → V) (u : V × d → ℝ) (e : F ⊕ C) : ℝ :=
  truncatedDistance (configurationSite u (Sum.elim af ac e)) (configurationSite u (Sum.elim bf bc e))

def actualFactor (af bf : F → V) (ac bc : C → V) (r : EdgeFactor F C d) (u : V × d → ℝ) : ℝ :=
  if r.2.1 then elementaryCoefficient (configurationSite u (Sum.elim bf bc r.1))
    (configurationSite u (Sum.elim af ac r.1)) r.2.2
  else elementaryCoefficient (configurationSite u (Sum.elim af ac r.1))
    (configurationSite u (Sum.elim bf bc r.1)) r.2.2

def actualShellWeight (m0 : ℕ) (af bf : F → V) (ac bc : C → V) (m : F → ℕ) (u : V × d → ℝ) : ℝ :=
  (∏ e : F, fineCutoff (m e) (actualEdgeDistance af bf ac bc u (Sum.inl e))) *
    (∏ e : C, coarseCutoff m0 (actualEdgeDistance af bf ac bc u (Sum.inr e)))

def actualShellMultiplier (m0 : ℕ) (af bf : F → V) (ac bc : C → V) (r : R → EdgeFactor F C d)
    (t : ℝ) (m : F → ℕ) (u : V × d → ℝ) : ℝ :=
  graphTaper (Sum.elim af ac) (Sum.elim bf bc) taperCutoff t (actualEdgeDistance af bf ac bc u) *
    actualShellWeight m0 af bf ac bc m u * ∏ j, actualFactor af bf ac bc (r j) u

def edgeScale (τ : F → ℝ) : F ⊕ C → ℝ := Sum.elim τ (fun _ => 1)
def factorScale (τ : F → ℝ) (r : EdgeFactor F C d) : ℝ := edgeScale τ r.1
def totalFactorScale (τ : F → ℝ) (r : R → EdgeFactor F C d) : ℝ := ∏ j, factorScale τ (r j)

def shellTaperScale (af bf : F → V) (ac bc : C → V) (t : ℝ) (τ : F → ℝ) (i : V) : ℝ :=
  vertexProduct (Sum.elim af ac) (Sum.elim bf bc) (edgeScale τ) i / t

theorem mixedFactor_central (af bf : F → V) (ac bc : C → V) (r : EdgeFactor F C d)
    (m : F → ℕ) (u : V × d → ℝ) :
    mixedFactor af bf ac bc r ((fun e => fineScale (m e)), centralConfiguration af bf m u) =
      factorScale (fun e => fineScale (m e)) r * actualFactor af bf ac bc r u := by
  rcases r with ⟨e, rev, a⟩
  cases e with
  | inl e =>
    cases rev with
    | false => exact elementaryProfile_fineLift (m e) _ _ a
    | true => exact elementaryProfile_reverse_fineLift (m e) _ _ a
  | inr e =>
    cases rev <;> simp only [mixedFactor, actualFactor, factorScale, edgeScale, Sum.elim_inr,
      Bool.false_eq_true, if_false, if_true, one_mul, basePoint, centralConfiguration, Sum.elim_inl, configurationSite] <;> rfl

theorem mixedShellProfile_central (m0 : ℕ) (af bf : F → V) (ac bc : C → V)
    (r : R → EdgeFactor F C d) (m : F → ℕ) (hm : ∀ e, 5 ≤ m e) (u : V × d → ℝ) :
    mixedShellProfile m0 af bf ac bc r ((fun e => fineScale (m e)), centralConfiguration af bf m u) =
      (actualShellWeight m0 af bf ac bc m u * totalFactorScale (fun e => fineScale (m e)) r *
        (∏ j, actualFactor af bf ac bc (r j) u) : ℝ) := by
  have hf (e : F) :
      annularCutoff (edgePoint (centralConfiguration af bf m u) e) *
        dyadicProfile (chordProfile (fineScale (m e)) (edgePoint (centralConfiguration af bf m u) e)) =
      fineCutoff (m e) (actualEdgeDistance af bf ac bc u (Sum.inl e)) :=
    annular_fineCutoff_exact (m e) (hm e) _ _
  have hfp := Finset.prod_congr (s₁ := Finset.univ) rfl (fun e _ => hf e)
  have hr : (∏ j, mixedFactor af bf ac bc (r j)
      ((fun e => fineScale (m e)), centralConfiguration af bf m u)) =
      totalFactorScale (fun e => fineScale (m e)) r * ∏ j, actualFactor af bf ac bc (r j) u := by
    simp_rw [mixedFactor_central]
    exact Finset.prod_mul_distrib
  change Complex.ofReal (((∏ e : F, annularCutoff (edgePoint (centralConfiguration af bf m u) e) *
      dyadicProfile (chordProfile (fineScale (m e)) (edgePoint (centralConfiguration af bf m u) e))) *
      (∏ e : C, coarseCutoff m0 (truncatedDistance (configurationSite u (ac e)) (configurationSite u (bc e))))) *
      (∏ j, mixedFactor af bf ac bc (r j) ((fun e => fineScale (m e)), centralConfiguration af bf m u))) = _
  rw [hfp, hr]
  change Complex.ofReal (actualShellWeight m0 af bf ac bc m u *
      (totalFactorScale (fun e => fineScale (m e)) r * ∏ j, actualFactor af bf ac bc (r j) u)) = _
  congr 1
  ring

theorem vertexProduct_mul (a b : F → V) (s q : F → ℝ) (i : V) :
    vertexProduct a b (fun e => s e * q e) i = vertexProduct a b s i * vertexProduct a b q i := by
  unfold vertexProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  split_ifs <;> simp

theorem actualDistance_on_shell (m0 : ℕ) (af bf : F → V) (ac bc : C → V)
    (m : F → ℕ) (hm : ∀ e, 5 ≤ m e) (u : V × d → ℝ)
    (hw : actualShellWeight m0 af bf ac bc m u ≠ 0) :
    actualEdgeDistance af bf ac bc u = fun e =>
      edgeScale (fun e => fineScale (m e)) e *
        mixedEdgeDistance ac bc ((fun e => fineScale (m e)), centralConfiguration af bf m u) e := by
  funext e
  cases e with
  | inl e =>
    have hh := (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hw).1) e (Finset.mem_univ e)
    exact fine_distance_exact_on_shell (m e) (hm e) _ _ hh
  | inr e =>
    simp only [edgeScale, mixedEdgeDistance, actualEdgeDistance, Sum.elim_inr, one_mul,
      basePoint, configurationSite, centralConfiguration, Sum.elim_inl]
    rfl

theorem shellTaper_central (m0 : ℕ) (af bf : F → V) (ac bc : C → V)
    (t : ℝ) (m : F → ℕ) (hm : ∀ e, 5 ≤ m e) (u : V × d → ℝ)
    (hw : actualShellWeight m0 af bf ac bc m u ≠ 0) :
    productTaper taperCutoff (mixedVertexDistance af bf ac bc)
      (shellTaperScale af bf ac bc t (fun e => fineScale (m e))) (fun e => fineScale (m e))
      (centralConfiguration af bf m u) =
      graphTaper (Sum.elim af ac) (Sum.elim bf bc) taperCutoff t (actualEdgeDistance af bf ac bc u) := by
  rw [actualDistance_on_shell m0 af bf ac bc m hm u hw]
  unfold productTaper graphTaper shellTaperScale mixedVertexDistance
  simp only [vertexProduct_mul]
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  ring

theorem mixedShellTaper_central (m0 : ℕ) (af bf : F → V) (ac bc : C → V)
    (r : R → EdgeFactor F C d) (t : ℝ) (m : F → ℕ) (hm : ∀ e, 5 ≤ m e) (u : V × d → ℝ) :
    mixedShellTaper m0 af bf ac bc r (shellTaperScale af bf ac bc t (fun e => fineScale (m e)))
      (fun e => fineScale (m e)) (centralConfiguration af bf m u) =
      (totalFactorScale (fun e => fineScale (m e)) r * actualShellMultiplier m0 af bf ac bc r t m u : ℝ) := by
  rw [mixedShellTaper, mixedShellProfile_central m0 af bf ac bc r m hm]
  by_cases hw : actualShellWeight m0 af bf ac bc m u = 0
  · simp only [hw, zero_mul, Complex.ofReal_zero, mul_zero, actualShellMultiplier]
  · rw [shellTaper_central m0 af bf ac bc t m hm u hw, ← Complex.ofReal_mul]
    congr 1
    unfold actualShellMultiplier
    ring

end CausalLowerbound.PartB.ShellGeometry
