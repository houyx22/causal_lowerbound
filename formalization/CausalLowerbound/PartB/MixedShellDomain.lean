import CausalLowerbound.PartB.FineShellDomain
import CausalLowerbound.PartB.ElementaryCoefficients
import CausalLowerbound.PartB.TaperWiener
import CausalLowerbound.MixedPeriodization

/-! A common compact domain for simultaneous fine and coarse graph edges.
The coarse diagonals are excluded by the actual coarse-shell cutoff. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ContDiff

namespace CausalLowerbound.PartB.ShellGeometry

open Wiener
variable {V F C d : Type*} [Fintype V] [Fintype F] [Fintype C] [Fintype d]

def basePoint (x : (V × d) ⊕ (F × d) → ℝ) (v : V) : d → ℝ := fun i => x (Sum.inl (v, i))
def edgePoint (x : (V × d) ⊕ (F × d) → ℝ) (e : F) : d → ℝ := fun i => x (Sum.inr (e, i))

theorem basePoint_smooth (v : V) : ContDiff ℝ ∞ (fun x : (V × d) ⊕ (F × d) → ℝ => basePoint x v) :=
  contDiff_pi.mpr (fun i => contDiff_apply ℝ ℝ (Sum.inl (v, i)))

theorem edgePoint_smooth (e : F) : ContDiff ℝ ∞ (fun x : (V × d) ⊕ (F × d) → ℝ => edgePoint x e) :=
  contDiff_pi.mpr (fun i => contDiff_apply ℝ ℝ (Sum.inr (e, i)))

def mixedShellDomain (m0 : ℕ) (a b : C → V) : Set ((V × d) ⊕ (F × d) → ℝ) :=
  Set.Icc (fun _ => -1) (fun _ => 1) ∩
    {x | (∀ e : F, edgePoint x e ∈ annularSet) ∧
      ∀ e : C, 1 / (2 : ℝ) ^ m0 ≤ truncatedDistance (basePoint x (a e)) (basePoint x (b e))}

theorem mixedShellDomain_compact (m0 : ℕ) (a b : C → V) :
    IsCompact (mixedShellDomain (F := F) (d := d) m0 a b) := by
  apply isCompact_Icc.inter_right
  apply IsClosed.inter
  · convert isClosed_iInter (fun e : F =>
      (annularSet_compact (d := d)).isClosed.preimage
        (edgePoint_smooth (V := V) e).continuous) using 1
    ext x
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
    rfl
  · simpa only [Set.iInter_setOf] using isClosed_iInter (fun e : C =>
      isClosed_le (f := fun _ : (V × d) ⊕ (F × d) → ℝ => 1 / (2 : ℝ) ^ m0) continuous_const
        (truncatedDistance_continuous.comp
          ((basePoint_smooth (a e)).continuous.prodMk (basePoint_smooth (b e)).continuous)))

theorem annularSet_neg (z : d → ℝ) (hz : z ∈ annularSet) : -z ∈ annularSet := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i
    have hi : z i ≤ 1 := hz.1.2 i
    simp only [Pi.neg_apply]
    linarith
  · intro i
    have hi : -1 ≤ z i := hz.1.1 i
    simp only [Pi.neg_apply]
    linarith
  · change 1 / (64 * Real.pi ^ 2) ≤ euclideanSquare (-z)
    simpa only [euclideanSquare, Pi.neg_apply, neg_sq] using
      (show 1 / (64 * Real.pi ^ 2) ≤ euclideanSquare z from hz.2)

theorem coarseCutoff_nonzero_lower (m0 : ℕ) (r : ℝ) (h : coarseCutoff m0 r ≠ 0) :
    1 / (2 : ℝ) ^ m0 < r :=
  lt_of_not_ge (fun hr => h (coarseCutoff_zero m0 hr))

theorem mixedShellDomain_support (m0 : ℕ) (a b : C → V)
    (H : ((V × d) ⊕ (F × d) → ℝ) → ℂ)
    (hf : ∀ x, H x ≠ 0 → ∀ e : F, annularCutoff (edgePoint x e) ≠ 0)
    (hc : ∀ x, H x ≠ 0 → ∀ e : C,
      coarseCutoff m0 (truncatedDistance (basePoint x (a e)) (basePoint x (b e))) ≠ 0) :
    tsupport (compactify H) ⊆ mixedShellDomain m0 a b := by
  apply closure_minimal _ (mixedShellDomain_compact m0 a b).isClosed
  intro x hx
  have hm := mul_ne_zero_iff.mp hx
  have hw := windowProduct_support (subset_tsupport _ hm.1)
  have he (e : F) := annularCutoff_support_point (edgePoint x e) (hf x hm.2 e)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro i
    cases i with
    | inl i => exact hw.1 i
    | inr i => exact (abs_lt.mp ((he i.1).1 i.2)).1.le
  · intro i
    cases i with
    | inl i => exact hw.2 i
    | inr i => exact (abs_lt.mp ((he i.1).1 i.2)).2.le
  · intro e
    exact annularCutoff_tsupport (subset_tsupport _ (hf x hm.2 e))
  · intro e
    exact (coarseCutoff_nonzero_lower m0 _ (hc x hm.2 e)).le

theorem coarse_domain_positive (m0 : ℕ) (a b : C → V)
    (x : (V × d) ⊕ (F × d) → ℝ) (hx : x ∈ mixedShellDomain m0 a b) (e : C) :
    0 < truncatedDistance (basePoint x (a e)) (basePoint x (b e)) :=
  lt_of_lt_of_le (by positivity) (hx.2.2 e)

def mixedEdgeDistance (a b : C → V) (p : (F → ℝ) × ((V × d) ⊕ (F × d) → ℝ)) : F ⊕ C → ℝ :=
  Sum.elim (fun e => chordProfile (p.1 e) (edgePoint p.2 e))
    (fun e => truncatedDistance (basePoint p.2 (a e)) (basePoint p.2 (b e)))

theorem mixedEdgeDistance_smoothAt (m0 : ℕ) (a b : C → V)
    (p : (F → ℝ) × ((V × d) ⊕ (F × d) → ℝ))
    (hx : p.2 ∈ mixedShellDomain m0 a b)
    (hD : ∀ e : F, chordSquare (p.1 e) (edgePoint p.2 e) ≠ 0) (e : F ⊕ C) :
    ContDiffAt ℝ ∞ (fun y => mixedEdgeDistance a b y e) p := by
  cases e with
  | inl e =>
    exact (contDiffAt_chordProfile _ _ (hD e)).comp p
      (((contDiff_apply ℝ ℝ e).comp contDiff_fst).prodMk
        ((edgePoint_smooth e).comp contDiff_snd)).contDiffAt
  | inr e =>
    exact (truncatedDistance_smoothAt _ _
      (chordDistance_pos_of_truncated (coarse_domain_positive m0 a b p.2 hx e)).ne').comp p
        (((basePoint_smooth (a e)).prodMk (basePoint_smooth (b e))).comp contDiff_snd).contDiffAt

theorem mixedEdgeDistance_pos (m0 : ℕ) (a b : C → V)
    (p : (F → ℝ) × ((V × d) ⊕ (F × d) → ℝ))
    (hx : p.2 ∈ mixedShellDomain m0 a b)
    (hq : ∀ e : F, 0 < chordProfile (p.1 e) (edgePoint p.2 e)) (e : F ⊕ C) :
    0 < mixedEdgeDistance a b p e := by
  cases e with
  | inl e => exact hq e
  | inr e => exact coarse_domain_positive m0 a b p.2 hx e

end CausalLowerbound.PartB.ShellGeometry
