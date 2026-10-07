import CausalLowerbound.PartB.MixedShellProfiles

/-! A uniform Wiener estimate for the complete compactified shell profile,
including all elementary factors and the coupled graph taper. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ContDiff

namespace CausalLowerbound.PartB.ShellGeometry

open Wiener ConfigurationShells

theorem finite_compact_positive_lower {I X : Type*} [Fintype I] [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (q : I → X → ℝ)
    (hq : ∀ i, ContinuousOn (q i) K) (hpos : ∀ i x, x ∈ K → 0 < q i x) :
    ∃ c > 0, ∀ i x, x ∈ K → c ≤ q i x := by
  classical
  have hb (s : Finset I) : ∃ c > 0, ∀ i ∈ s, ∀ x ∈ K, c ≤ q i x := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨c, hc, hb⟩ := ih
      obtain ⟨ci, hci, hbi⟩ := hK.exists_forall_le' (hq i) (hpos i)
      refine ⟨min c ci, lt_min hc hci, ?_⟩
      intro j hj x hx
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (min_le_right _ _).trans (hbi x hx)
      · exact (min_le_left _ _).trans (hb j hj x hx)
  obtain ⟨c, hc, hb⟩ := hb Finset.univ
  exact ⟨c, hc, fun i => hb i (Finset.mem_univ i)⟩

variable {V F C d R : Type*} [Fintype V] [DecidableEq V]
  [Fintype F] [Fintype C] [Fintype d] [Fintype R]

def mixedVertexDistance (af bf : F → V) (ac bc : C → V) (i : V)
    (p : (F → ℝ) × ((V × d) ⊕ (F × d) → ℝ)) : ℝ :=
  vertexProduct (Sum.elim af ac) (Sum.elim bf bc) (mixedEdgeDistance ac bc p) i

def mixedShellTaper (m0 : ℕ) (af bf : F → V) (ac bc : C → V) (r : R → EdgeFactor F C d)
    (lam : V → ℝ) (τ : F → ℝ) (x : (V × d) ⊕ (F × d) → ℝ) : ℂ :=
  (productTaper taperCutoff (mixedVertexDistance af bf ac bc) lam τ x : ℂ) *
    mixedShellProfile m0 af bf ac bc r (τ, x)

theorem mixedVertexDistance_smoothAt (m0 : ℕ) (af bf : F → V) (ac bc : C → V)
    (p : (F → ℝ) × ((V × d) ⊕ (F × d) → ℝ))
    (hx : p.2 ∈ mixedShellDomain m0 ac bc)
    (hD : ∀ e : F, chordSquare (p.1 e) (edgePoint p.2 e) ≠ 0) (i : V) :
    ContDiffAt ℝ ∞ (mixedVertexDistance af bf ac bc i) p := by
  apply contDiffAt_prod
  intro e _
  by_cases h : incident (Sum.elim af ac) (Sum.elim bf bc) i e
  · simpa only [if_pos h] using mixedEdgeDistance_smoothAt m0 ac bc p hx hD e
  · simpa only [if_neg h] using (contDiffAt_const : ContDiffAt ℝ ∞
      (fun _ : (F → ℝ) × ((V × d) ⊕ (F × d) → ℝ) => (1 : ℝ)) p)

theorem mixedVertexDistance_pos (m0 : ℕ) (af bf : F → V) (ac bc : C → V)
    (p : (F → ℝ) × ((V × d) ⊕ (F × d) → ℝ))
    (hx : p.2 ∈ mixedShellDomain m0 ac bc)
    (hq : ∀ e : F, 0 < chordProfile (p.1 e) (edgePoint p.2 e)) (i : V) :
    0 < mixedVertexDistance af bf ac bc i p := by
  apply Finset.prod_pos
  intro e _
  split_ifs
  · exact mixedEdgeDistance_pos m0 ac bc p hx hq e
  · exact zero_lt_one

theorem mixedShellTaper_compactify (m0 : ℕ) (af bf : F → V) (ac bc : C → V)
    (r : R → EdgeFactor F C d) (lam : V → ℝ) (τ : F → ℝ) :
    taperedProfile taperCutoff (mixedVertexDistance af bf ac bc)
      (fun p => compactify (fun x => mixedShellProfile m0 af bf ac bc r (p.1, x)) p.2) lam τ =
      compactify (mixedShellTaper m0 af bf ac bc r lam τ) := by
  funext x
  unfold taperedProfile mixedShellTaper compactify
  ring

/-- No Fourier bound or derivative bound is an input: the fixed compact
domain and the concrete formulas supply both. The constant is uniform in
every nonnegative taper parameter and every positive anisotropic period. -/
theorem mixed_shell_compact_wiener (af bf : F → V) (ac bc : C → V)
    (r : R → EdgeFactor F C d) :
    ∃ ε > 0, ∀ m0 : ℕ, ∃ B ≥ 0, ∀ lam : V → ℝ, (∀ i, 0 ≤ lam i) →
      ∀ τ ∈ Set.Icc 0 (fun _ : F => ε), ∀ N : (V × d) ⊕ (F × d) → ℕ, (∀ i, N i ≠ 0) →
      ∃ A : Fourier ((V × d) ⊕ (F × d)),
        (∀ x, toContinuous A x = periodizedTorus
          (compactify (mixedShellTaper m0 af bf ac bc r lam τ)) N x) ∧ ‖A‖ ≤ B := by
  obtain ⟨ε, hε, c0, hc0, C0, hC0, hε4, hann⟩ := fine_annular_domain (d := d)
  refine ⟨ε, hε, ?_⟩
  intro m0
  let Kp : Set (F → ℝ) := Set.Icc 0 (fun _ => ε)
  let Kx := mixedShellDomain (F := F) (d := d) m0 ac bc
  let H : (F → ℝ) × ((V × d) ⊕ (F × d) → ℝ) → ℂ := fun p =>
    compactify (fun x => mixedShellProfile m0 af bf ac bc r (p.1, x)) p.2
  let q : V → (F → ℝ) × ((V × d) ⊕ (F × d) → ℝ) → ℝ := mixedVertexDistance af bf ac bc
  have hD (τ : F → ℝ) (hτ : τ ∈ Kp) (x : (V × d) ⊕ (F × d) → ℝ) (hx : x ∈ Kx) (e : F) :
      chordSquare (τ e) (edgePoint x e) ≠ 0 :=
    (hann (τ e) ⟨hτ.1 e, hτ.2 e⟩ _ (hx.2.1 e)).2.2.1
  have hDn (τ : F → ℝ) (hτ : τ ∈ Kp) (x : (V × d) ⊕ (F × d) → ℝ) (hx : x ∈ Kx) (e : F) :
      chordSquare (τ e) (-edgePoint x e) ≠ 0 :=
    (hann (τ e) ⟨hτ.1 e, hτ.2 e⟩ _ (annularSet_neg _ (hx.2.1 e))).2.2.1
  have hH : ∀ τ ∈ Kp, ∀ x ∈ Kx, ContDiffAt ℝ ∞ H (τ, x) := by
    intro τ hτ x hx
    exact compactify_family_smooth _ τ x
      (mixedShellProfile_smoothAt m0 af bf ac bc r (τ, x) hx (hD τ hτ x hx) (hDn τ hτ x hx))
  have hq : ∀ i τ x, τ ∈ Kp → x ∈ Kx → ContDiffAt ℝ ∞ (q i) (τ, x) := by
    intro i τ x hτ hx
    exact mixedVertexDistance_smoothAt m0 af bf ac bc (τ, x) hx (hD τ hτ x hx) i
  have hp : ∀ i (p : (F → ℝ) × ((V × d) ⊕ (F × d) → ℝ)), p ∈ Kp ×ˢ Kx → 0 < q i p := by
    intro i p hp
    exact mixedVertexDistance_pos m0 af bf ac bc p hp.2 (fun e =>
      hc0.trans_le (hann (p.1 e) ⟨hp.1.1 e, hp.1.2 e⟩ _ (hp.2.2.1 e)).1) i
  obtain ⟨c, hc, hlow⟩ := finite_compact_positive_lower (Kp ×ˢ Kx)
    (isCompact_Icc.prod (mixedShellDomain_compact m0 ac bc)) q
    (fun i p hp => (hq i p.1 p.2 hp.1 hp.2).continuousAt.continuousWithinAt) hp
  obtain ⟨B, hB, hb⟩ := tapered_family_wiener taperCutoff taperCutoff_smooth (fun _ h => taperCutoff_one h)
    q H Kp Kx isCompact_Icc (mixedShellDomain_compact m0 ac bc)
    (fun τ _ => mixedShellProfile_support m0 af bf ac bc r τ) hH hq c hc
    (fun i τ x hτ hx => hlow i (τ, x) ⟨hτ, hx⟩)
  refine ⟨B, hB, ?_⟩
  intro lam hlam τ hτ N hN
  obtain ⟨A, hA, hn⟩ := hb lam hlam τ hτ N hN
  refine ⟨A, ?_, hn⟩
  intro x
  rw [hA]
  exact congrArg (fun f => periodizedTorus f N x) (mixedShellTaper_compactify m0 af bf ac bc r lam τ)

end CausalLowerbound.PartB.ShellGeometry
