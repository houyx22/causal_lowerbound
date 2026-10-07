import CausalLowerbound.PartB.MixedShellDomain

/-! Concrete simultaneous coarse/fine multipliers. The factor list records
both orientations of each elementary Lagrange coefficient, including repeats. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ContDiff

namespace CausalLowerbound.PartB.ShellGeometry

variable {V F C d R : Type*} [Fintype V] [Fintype F] [Fintype C] [Fintype d] [Fintype R]

abbrev EdgeFactor (F C d : Type*) := (F ⊕ C) × Bool × Option (d × Bool)

def mixedFactor (af bf : F → V) (ac bc : C → V) (r : EdgeFactor F C d)
    (p : (F → ℝ) × ((V × d) ⊕ (F × d) → ℝ)) : ℝ :=
  match r.1 with
  | Sum.inl e => if r.2.1 then
      elementaryProfile (p.1 e) (basePoint p.2 (af e)) (-edgePoint p.2 e) r.2.2
    else elementaryProfile (p.1 e) (basePoint p.2 (bf e)) (edgePoint p.2 e) r.2.2
  | Sum.inr e => if r.2.1 then
      elementaryCoefficient (basePoint p.2 (bc e)) (basePoint p.2 (ac e)) r.2.2
    else elementaryCoefficient (basePoint p.2 (ac e)) (basePoint p.2 (bc e)) r.2.2

def mixedShellProfile (m0 : ℕ) (af bf : F → V) (ac bc : C → V) (r : R → EdgeFactor F C d)
    (p : (F → ℝ) × ((V × d) ⊕ (F × d) → ℝ)) : ℂ :=
  ((∏ e : F, annularCutoff (edgePoint p.2 e) * dyadicProfile (chordProfile (p.1 e) (edgePoint p.2 e))) *
    (∏ e : C, coarseCutoff m0 (truncatedDistance (basePoint p.2 (ac e)) (basePoint p.2 (bc e)))) *
    (∏ j : R, mixedFactor af bf ac bc (r j) p) : ℝ)

theorem mixedFactor_smoothAt (m0 : ℕ) (af bf : F → V) (ac bc : C → V)
    (r : EdgeFactor F C d) (p : (F → ℝ) × ((V × d) ⊕ (F × d) → ℝ))
    (hx : p.2 ∈ mixedShellDomain m0 ac bc)
    (hD : ∀ e : F, chordSquare (p.1 e) (edgePoint p.2 e) ≠ 0)
    (hDn : ∀ e : F, chordSquare (p.1 e) (-edgePoint p.2 e) ≠ 0) :
    ContDiffAt ℝ ∞ (mixedFactor af bf ac bc r) p := by
  rcases r with ⟨e, rev, a⟩
  cases e with
  | inl e =>
    cases rev with
    | false =>
      exact (contDiff_apply ℝ ℝ a).contDiffAt.comp p
        ((contDiffAt_elementaryProfile _ _ _ (hD e)).comp p
          (((contDiff_apply ℝ ℝ e).comp contDiff_fst).prodMk
            (((basePoint_smooth (bf e)).comp contDiff_snd).prodMk
              ((edgePoint_smooth e).comp contDiff_snd))).contDiffAt)
    | true =>
      exact (contDiff_apply ℝ ℝ a).contDiffAt.comp p
        ((contDiffAt_elementaryProfile _ _ _ (hDn e)).comp p
          (((contDiff_apply ℝ ℝ e).comp contDiff_fst).prodMk
            (((basePoint_smooth (af e)).comp contDiff_snd).prodMk
              ((edgePoint_smooth e).comp contDiff_snd).neg)).contDiffAt)
  | inr e =>
    have hp := chordDistance_pos_of_truncated (coarse_domain_positive m0 ac bc p.2 hx e)
    cases rev with
    | false =>
      exact (elementaryCoefficient_smoothAt _ _ a hp.ne').comp p
        (((basePoint_smooth (ac e)).prodMk (basePoint_smooth (bc e))).comp contDiff_snd).contDiffAt
    | true =>
      have hpn : chordDistance (basePoint p.2 (bc e)) (basePoint p.2 (ac e)) ≠ 0 := by
        rw [chordDistance_symm]; exact hp.ne'
      exact (elementaryCoefficient_smoothAt _ _ a hpn).comp p
        (((basePoint_smooth (bc e)).prodMk (basePoint_smooth (ac e))).comp contDiff_snd).contDiffAt

theorem mixedShellProfile_smoothAt (m0 : ℕ) (af bf : F → V) (ac bc : C → V)
    (r : R → EdgeFactor F C d) (p : (F → ℝ) × ((V × d) ⊕ (F × d) → ℝ))
    (hx : p.2 ∈ mixedShellDomain m0 ac bc)
    (hD : ∀ e : F, chordSquare (p.1 e) (edgePoint p.2 e) ≠ 0)
    (hDn : ∀ e : F, chordSquare (p.1 e) (-edgePoint p.2 e) ≠ 0) :
    ContDiffAt ℝ ∞ (mixedShellProfile m0 af bf ac bc r) p := by
  apply Complex.ofRealCLM.contDiff.contDiffAt.comp p
  apply ContDiffAt.mul
  · apply ContDiffAt.mul
    · apply contDiffAt_prod
      intro e _
      exact ((annularCutoff_smooth.comp ((edgePoint_smooth e).comp contDiff_snd)).contDiffAt).mul
        (dyadicProfile_smooth.contDiffAt.comp p (mixedEdgeDistance_smoothAt m0 ac bc p hx hD (Sum.inl e)))
    · apply contDiffAt_prod
      intro e _
      exact (coarseCutoff_smooth m0).contDiffAt.comp p
        (mixedEdgeDistance_smoothAt m0 ac bc p hx hD (Sum.inr e))
  · apply contDiffAt_prod
    intro j _
    exact mixedFactor_smoothAt m0 af bf ac bc (r j) p hx hD hDn

theorem mixedShellProfile_support (m0 : ℕ) (af bf : F → V) (ac bc : C → V)
    (r : R → EdgeFactor F C d) (τ : F → ℝ) :
    tsupport (Wiener.compactify (fun x => mixedShellProfile m0 af bf ac bc r (τ, x))) ⊆
      mixedShellDomain m0 ac bc := by
  classical
  have hn (x : (V × d) ⊕ (F × d) → ℝ) (h : mixedShellProfile m0 af bf ac bc r (τ, x) ≠ 0) :
      (∏ e : F, annularCutoff (edgePoint x e) * dyadicProfile (chordProfile (τ e) (edgePoint x e))) ≠ 0 ∧
      (∏ e : C, coarseCutoff m0 (truncatedDistance (basePoint x (ac e)) (basePoint x (bc e)))) ≠ 0 := by
    have hr : ((∏ e : F, annularCutoff (edgePoint x e) * dyadicProfile (chordProfile (τ e) (edgePoint x e))) *
        (∏ e : C, coarseCutoff m0 (truncatedDistance (basePoint x (ac e)) (basePoint x (bc e))))) *
        (∏ j : R, mixedFactor af bf ac bc (r j) (τ, x)) ≠ 0 := by
      intro hz
      exact h (by change Complex.ofReal _ = 0; rw [hz, Complex.ofReal_zero])
    exact mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hr).1
  apply mixedShellDomain_support
  · intro x hx e
    exact (mul_ne_zero_iff.mp ((Finset.prod_ne_zero_iff.mp (hn x hx).1) e (Finset.mem_univ e))).1
  · intro x hx e
    exact (Finset.prod_ne_zero_iff.mp (hn x hx).2) e (Finset.mem_univ e)

theorem mixedShellProfile_integer_period (m0 : ℕ) (af bf : F → V) (ac bc : C → V)
    (r : R → EdgeFactor F C d) (τ : F → ℝ) (k : V × d → ℤ) (u : V × d → ℝ) (z : F × d → ℝ) :
    mixedShellProfile m0 af bf ac bc r (τ, Sum.elim (Wiener.latticeTranslate (fun _ => 1) k u) z) =
      mixedShellProfile m0 af bf ac bc r (τ, Sum.elim u z) := by
  have hp (v : V) : basePoint (Sum.elim (Wiener.latticeTranslate (fun _ => 1) k u) z) v =
      fun i => u (v, i) + (k (v, i) : ℝ) := by
    funext i; simp only [basePoint, Sum.elim_inl, Wiener.latticeTranslate, Nat.cast_one, one_mul]
  have he (j : R) : mixedFactor af bf ac bc (r j)
      (τ, Sum.elim (Wiener.latticeTranslate (fun _ => 1) k u) z) =
      mixedFactor af bf ac bc (r j) (τ, Sum.elim u z) := by
    rcases r j with ⟨e, rev, a⟩
    cases e <;> cases rev <;>
      simp only [mixedFactor, Bool.false_eq_true, if_false, if_true, hp,
        elementaryCoefficient_integer_period, elementaryProfile_integer_period, basePoint, edgePoint, Sum.elim_inr, Sum.elim_inl] <;> rfl
  simp only [mixedShellProfile, hp, truncatedDistance_integer_period, he, basePoint, edgePoint,
    Sum.elim_inl, Sum.elim_inr]
  rfl

end CausalLowerbound.PartB.ShellGeometry
