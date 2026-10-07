import CausalLowerbound.PartB.MixedShellEvaluation

/-! Uniform Wiener realizations of the original graph shell multipliers.
No analytic estimates for those multipliers are left as hypotheses. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartB.ShellGeometry

open Wiener ConfigurationShells
variable {V F C d R : Type*} [Fintype V] [DecidableEq V]
  [Fintype F] [Fintype C] [Fintype d] [Fintype R]

theorem mixedEdgeDistance_integer_period (ac bc : C → V) (τ : F → ℝ)
    (k : V × d → ℤ) (u : V × d → ℝ) (z : F × d → ℝ) :
    mixedEdgeDistance ac bc (τ, Sum.elim (latticeTranslate (fun _ => 1) k u) z) =
      mixedEdgeDistance ac bc (τ, Sum.elim u z) := by
  funext e
  cases e with
  | inl e =>
    simp only [mixedEdgeDistance, Sum.elim_inl]
    congr 1
  | inr e =>
    have hp (v : V) : basePoint (Sum.elim (latticeTranslate (fun _ => 1) k u) z) v =
        fun i => u (v, i) + (k (v, i) : ℝ) := by
      funext i
      simp only [basePoint, Sum.elim_inl, latticeTranslate, Nat.cast_one, one_mul]
    simp only [mixedEdgeDistance, Sum.elim_inr, hp, truncatedDistance_integer_period]
    rfl

theorem mixedShellTaper_integer_period (m0 : ℕ) (af bf : F → V) (ac bc : C → V)
    (r : R → EdgeFactor F C d) (lam : V → ℝ) (τ : F → ℝ)
    (k : V × d → ℤ) (u : V × d → ℝ) (z : F × d → ℝ) :
    mixedShellTaper m0 af bf ac bc r lam τ (Sum.elim (latticeTranslate (fun _ => 1) k u) z) =
      mixedShellTaper m0 af bf ac bc r lam τ (Sum.elim u z) := by
  unfold mixedShellTaper productTaper mixedVertexDistance
  rw [mixedShellProfile_integer_period, mixedEdgeDistance_integer_period]

theorem mixedShellTaper_fine_support (m0 : ℕ) (af bf : F → V) (ac bc : C → V)
    (r : R → EdgeFactor F C d) (lam : V → ℝ) (τ : F → ℝ)
    (x : (V × d) ⊕ (F × d) → ℝ) (hx : mixedShellTaper m0 af bf ac bc r lam τ x ≠ 0) (e : F) :
    annularCutoff (edgePoint x e) ≠ 0 := by
  classical
  intro hz
  have hp : (∏ e : F, annularCutoff (edgePoint x e) * dyadicProfile (chordProfile (τ e) (edgePoint x e))) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ e) (by rw [hz, zero_mul])
  exact hx (by simp only [mixedShellTaper, mixedShellProfile, hp, zero_mul, Complex.ofReal_zero, mul_zero])

theorem mixedShellTaper_compact (m0 : ℕ) (af bf : F → V) (ac bc : C → V)
    (r : R → EdgeFactor F C d) (lam : V → ℝ) (τ : F → ℝ) :
    HasCompactSupport (compactify (mixedShellTaper m0 af bf ac bc r lam τ)) := by
  rw [← mixedShellTaper_compactify]
  exact (mixedShellDomain_compact m0 ac bc).of_isClosed_subset isClosed_closure
    (tsupport_mul_subset_right.trans (mixedShellProfile_support m0 af bf ac bc r τ))

def factorOrder (m : F → ℕ) (r : EdgeFactor F C d) : ℕ := Sum.elim m (fun _ => 0) r.1
def totalFactorOrder (m : F → ℕ) (r : R → EdgeFactor F C d) : ℕ := ∑ j, factorOrder m (r j)

theorem factorScale_dyadic (m : F → ℕ) (r : EdgeFactor F C d) :
    factorScale (fun e => fineScale (m e)) r = ((2 : ℝ) ^ factorOrder m r)⁻¹ := by
  rcases r with ⟨e, rev, a⟩
  cases e <;> simp only [factorScale, edgeScale, fineScale, factorOrder, Sum.elim_inl, Sum.elim_inr, pow_zero, inv_one]

theorem totalFactorScale_dyadic (m : F → ℕ) (r : R → EdgeFactor F C d) :
    totalFactorScale (fun e => fineScale (m e)) r = ((2 : ℝ) ^ totalFactorOrder m r)⁻¹ := by
  unfold totalFactorScale totalFactorOrder
  simp only [factorScale_dyadic, Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum]

theorem shellTaperScale_nonneg (af bf : F → V) (ac bc : C → V) (t : ℝ) (ht : 0 < t)
    (τ : F → ℝ) (hτ : ∀ e, 0 ≤ τ e) (i : V) : 0 ≤ shellTaperScale af bf ac bc t τ i := by
  apply div_nonneg _ ht.le
  apply vertexProduct_nonneg
  intro e
  cases e with
  | inl e => exact hτ e
  | inr e => exact zero_le_one

/-- The paper's shell estimate for any fixed list of oriented elementary
factors. The exponent counts every occurrence of a fine factor exactly once.
The graph may have shared vertices and cycles. -/
theorem actual_shell_uniform_wiener (af bf : F → V) (ac bc : C → V)
    (r : R → EdgeFactor F C d) :
    ∃ mStart : ℕ, 5 ≤ mStart ∧ ∀ m0, mStart ≤ m0 → ∃ B ≥ 0,
      ∀ t > 0, ∀ m : F → ℕ, (∀ e, m0 ≤ m e) →
      ∃ A : Fourier (V × d),
        (∀ u, toContinuous A (torusProjection u) = (actualShellMultiplier m0 af bf ac bc r t m u : ℝ)) ∧
        ‖A‖ ≤ B * (2 : ℝ) ^ totalFactorOrder m r := by
  obtain ⟨ε, hε, hbound⟩ := mixed_shell_compact_wiener af bf ac bc r
  obtain ⟨mStart, hstart, hs⟩ := exists_fine_start ε hε
  refine ⟨mStart, hstart, ?_⟩
  intro m0 hm0
  obtain ⟨B, hB, hb⟩ := hbound m0
  refine ⟨B, hB, ?_⟩
  intro t ht m hm
  let τ : F → ℝ := fun e => fineScale (m e)
  let lam := shellTaperScale af bf ac bc t τ
  let G := mixedShellTaper m0 af bf ac bc r lam τ
  have hτ : τ ∈ Set.Icc 0 (fun _ => ε) :=
    ⟨fun e => (hs (m e) (hm0.trans (hm e))).1, fun e => (hs (m e) (hm0.trans (hm e))).2⟩
  have hlam : ∀ i, 0 ≤ lam i := shellTaperScale_nonneg af bf ac bc t ht τ (fun e => (fineScale_pos _).le)
  have hN : ∀ i : F × d, dyadicPeriods m i ≠ 0 := fun _ => pow_ne_zero _ (by norm_num)
  obtain ⟨A, hA, hn⟩ := hb lam hlam τ hτ (mixedPeriods (dyadicPeriods m)) (mixedPeriods_ne_zero _ hN)
  let A0 := configurationPullback af bf A
  have he (u : V × d → ℝ) : toContinuous A0 (torusProjection u) =
      (totalFactorScale τ r * actualShellMultiplier m0 af bf ac bc r t m u : ℝ) := by
    rw [configurationPullback_value, hA]
    rw [periodizedTorus_compactify G (mixedShellTaper_compact m0 af bf ac bc r lam τ)
      (mixedShellTaper_integer_period m0 af bf ac bc r lam τ) _ hN]
    rw [mixed_graph_evaluation af bf m (fun e => hstart.trans (hm0.trans (hm e))) G
      (mixedShellTaper_integer_period m0 af bf ac bc r lam τ)
      (mixedShellTaper_fine_support m0 af bf ac bc r lam τ)]
    exact mixedShellTaper_central m0 af bf ac bc r t m (fun e => hstart.trans (hm0.trans (hm e))) u
  have hn0 : ‖A0‖ ≤ B := (configurationPullback_bound af bf A).trans hn
  refine ⟨((2 : ℝ) ^ totalFactorOrder m r : ℂ) • A0, ?_, ?_⟩
  · intro u
    simp only [map_smul, ContinuousMap.smul_apply, smul_eq_mul]
    rw [he]
    dsimp only [τ]
    rw [totalFactorScale_dyadic, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    congr 1
    rw [← mul_assoc, mul_inv_cancel₀ (by positivity : (2 : ℝ) ^ totalFactorOrder m r ≠ 0), one_mul]
  · rw [norm_smul, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < (2 : ℝ) ^ totalFactorOrder m r)]
    exact (mul_le_mul_of_nonneg_left hn0 (by positivity)).trans_eq (mul_comm _ _)

end CausalLowerbound.PartB.ShellGeometry
