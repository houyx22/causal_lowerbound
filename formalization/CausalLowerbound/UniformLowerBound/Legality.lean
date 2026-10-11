import CausalLowerbound.UniformLowerBound.Models

/-! Uniform Hölder and probability constraints, with amplitudes chosen from
the prescribed radii.  No design or regularity input is left unproved. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped ContDiff
namespace CausalLowerbound.UniformLowerBound
open PartB PartB.ShellGeometry
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem holder_half_add {s : Regularity} {C : ℝ} {f : (d → ℝ) → ℝ}
    (hf : HolderControl s.order s.fraction C f) (hs : ContDiff ℝ ∞ f) :
    HolderControl s.order s.fraction (1 / 2 + C) (fun x => 1 / 2 + f x) := by
  simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using
    (HolderControl.const s.order s.fraction (1 / 2)).add hf contDiff_const hs

theorem fields_legal_of_controls (regime side : Bool) (S : Finset (d → ℤ))
    (ζ : (d → ℤ) → Bool) (x₀ : d → ℝ) (ℓ h a b : ℝ)
    (α β γ : Regularity) (Lπ L₀ Lτ κ A B D : ℝ)
    (hLπ : 1 / 2 ≤ Lπ) (hL₀ : 1 / 2 ≤ L₀) (hLτ : 0 ≤ Lτ)
    (hκ : κ < 1 / 2)
    (hp : HolderControl α.order α.fraction A (fun x => a * signedField S ζ x₀ ℓ h x))
    (hy : HolderControl β.order β.fraction B (fun x => b * signedField S ζ x₀ ℓ h x))
    (hTβ : HolderControl β.order β.fraction D (targetField x₀ h (4 * a * b)))
    (hTγ : HolderControl γ.order γ.fraction Lτ (targetField x₀ h (4 * a * b)))
    (hArad : 1 / 2 + A ≤ Lπ) (hBrad : 1 / 2 + B + D / 2 ≤ L₀)
    (hA : A ≤ (1 / 2 - κ) / 4) (hB : B ≤ (1 / 2 - κ) / 4)
    (hT : ∀ x, |targetField x₀ h (4 * a * b) x| ≤ (1 / 2 - κ) / 4) :
    (fields regime side S ζ x₀ ℓ h a b).Legal α β γ Lπ L₀ Lτ κ := by
  have hUs := signedField_smooth S ζ x₀ ℓ h
  have hTs := targetField_smooth x₀ h (4 * a * b)
  have hps : ContDiff ℝ ∞ (fun x => a * signedField S ζ x₀ ℓ h x) := contDiff_const.mul hUs
  have hys : ContDiff ℝ ∞ (fun x => b * signedField S ζ x₀ ℓ h x) := contDiff_const.mul hUs
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hp.value_bound x₀)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hy.value_bound x₀)
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hTβ.value_bound x₀)
  have hp' := (holder_half_add hp hps).mono hArad
  have hπ0 : HolderControl α.order α.fraction Lπ (fun _ : d → ℝ => (1 / 2 : ℝ)) :=
    (HolderControl.const (E := d → ℝ) α.order α.fraction (1 / 2 : ℝ)).mono
      (by simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using hLπ)
  have hy' := holder_half_add hy hys
  have hμ0 : HolderControl β.order β.fraction (1 / 2) (fun _ : d → ℝ => (1 / 2 : ℝ)) := by
    simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using
      HolderControl.const (E := d → ℝ) β.order β.fraction (1 / 2)
  have hTneg : HolderControl β.order β.fraction (D / 2)
      (fun x => -(targetField x₀ h (4 * a * b) x / 2)) := by
    have hh := hTβ.const_smul hTs (-1 / 2)
    have hc : |(-1 / 2 : ℝ)| * D = D / 2 := by
      rw [abs_of_neg (by norm_num : (-1 / 2 : ℝ) < 0)]
      ring
    rw [hc] at hh
    convert hh using 1
    funext x
    simp only [smul_eq_mul]
    ring
  have hTns : ContDiff ℝ ∞ (fun x => -(targetField x₀ h (4 * a * b) x / 2)) :=
    (hTs.div_const 2).neg
  have hμUm : HolderControl β.order β.fraction L₀
      (fun x => 1 / 2 + b * signedField S ζ x₀ ℓ h x - targetField x₀ h (4 * a * b) x / 2) := by
    simpa only [sub_eq_add_neg] using
      (hy'.add hTneg (contDiff_const.add hys) hTns).mono hBrad
  have hμ0m : HolderControl β.order β.fraction L₀
      (fun x => 1 / 2 - targetField x₀ h (4 * a * b) x / 2) := by
    simpa only [sub_eq_add_neg] using
      (hμ0.add hTneg contDiff_const hTns).mono (by linarith)
  have hμU := hy'.mono (show 1 / 2 + B ≤ L₀ by linarith)
  have hτ0 : HolderControl γ.order γ.fraction Lτ (fun _ : d → ℝ => (0 : ℝ)) :=
    (HolderControl.const (E := d → ℝ) γ.order γ.fraction (0 : ℝ)).mono (by simpa using hLτ)
  have hprob : ∀ x, κ ≤ (fields regime side S ζ x₀ ℓ h a b).propensity x ∧
      (fields regime side S ζ x₀ ℓ h a b).propensity x ≤ 1 - κ ∧
      κ ≤ (fields regime side S ζ x₀ ℓ h a b).baseline x ∧
      (fields regime side S ζ x₀ ℓ h a b).baseline x ≤ 1 - κ ∧
      κ ≤ (fields regime side S ζ x₀ ℓ h a b).baseline x +
        (fields regime side S ζ x₀ ℓ h a b).effect x ∧
      (fields regime side S ζ x₀ ℓ h a b).baseline x +
        (fields regime side S ζ x₀ ℓ h a b).effect x ≤ 1 - κ := by
    intro x
    have hpv := abs_le.mp ((hp.value_bound x).trans hA)
    have hyv := abs_le.mp ((hy.value_bound x).trans hB)
    have htv := abs_le.mp (hT x)
    cases regime <;> cases side <;> dsimp [fields] <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
  refine ⟨?_, ?_, ?_, hprob⟩
  · cases regime <;> cases side
    all_goals first | simpa [fields] using hp' | simpa [fields] using hπ0
  · cases regime <;> cases side <;> simp only [fields, Bool.false_eq_true, Bool.and_false,
      Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, Bool.and_true,
      ↓reduceIte, add_zero, sub_zero] <;> assumption
  · cases side
    · simpa [fields] using hτ0
    · simpa [fields] using hTγ

theorem exists_legal_amplitudes (α β γ : Regularity) (hβγ : β.exponent ≤ γ.exponent)
    (Lπ L₀ Lτ κ : ℝ) (hLπ : 1 / 2 < Lπ) (hL₀ : 1 / 2 < L₀)
    (hLτ : 0 < Lτ) (hκ : κ < 1 / 2) :
    ∃ ε > 0, ε ≤ 1 ∧ ∀ (ca cb : ℝ), 0 ≤ ca → ca ≤ ε → 0 ≤ cb → cb ≤ ε →
      ∀ (regime side : Bool) (S : Finset (d → ℤ)) (ζ : (d → ℤ) → Bool)
        (x₀ : d → ℝ) (ℓ h : ℝ), 0 < ℓ → ℓ ≤ h → h ≤ 1 →
        h ^ γ.exponent = ℓ ^ (α.exponent + β.exponent) →
        (fields regime side S ζ x₀ ℓ h (ca * ℓ ^ α.exponent)
          (cb * ℓ ^ β.exponent)).Legal α β γ Lπ L₀ Lτ κ := by
  obtain ⟨A, hA, ha⟩ := signedField_amplitude_holder (d := d) α
  obtain ⟨B, hB, hb⟩ := signedField_amplitude_holder (d := d) β
  obtain ⟨E, hE, he⟩ := target_lower_regularity (d := d) β γ.exponent hβγ
  obtain ⟨D, hD, hd⟩ := target_lower_regularity (d := d) γ γ.exponent le_rfl
  let ε := min (1 / 32) (min ((1 / 2 - κ) / 16) (min ((Lπ - 1 / 2) / A)
    (min ((L₀ - 1 / 2) / (B + 2 * E)) (min (Lτ / (4 * D))
      (min (((1 / 2 - κ) / 4) / A) (((1 / 2 - κ) / 4) / B))))))
  have hπpos : 0 < Lπ - 1 / 2 := sub_pos.mpr hLπ
  have hμpos : 0 < L₀ - 1 / 2 := sub_pos.mpr hL₀
  have hmargin : 0 < 1 / 2 - κ := sub_pos.mpr hκ
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨hε32, hrest⟩ := le_min_iff.mp (show ε ≤ min (1 / 32) (min ((1 / 2 - κ) / 16) (min ((Lπ - 1 / 2) / A)
    (min ((L₀ - 1 / 2) / (B + 2 * E)) (min (Lτ / (4 * D))
      (min (((1 / 2 - κ) / 4) / A) (((1 / 2 - κ) / 4) / B)))))) from le_rfl)
  obtain ⟨hεmargin, hrest⟩ := le_min_iff.mp hrest
  obtain ⟨hεA, hrest⟩ := le_min_iff.mp hrest
  obtain ⟨hεBE, hrest⟩ := le_min_iff.mp hrest
  obtain ⟨hεD, hrest⟩ := le_min_iff.mp hrest
  obtain ⟨hεAs, hεBs⟩ := le_min_iff.mp hrest
  have hEA : ε * A ≤ Lπ - 1 / 2 := (le_div_iff₀ hA).mp hεA
  have hEB : ε * (B + 2 * E) ≤ L₀ - 1 / 2 :=
    (le_div_iff₀ (by positivity)).mp hεBE
  have hED : ε * (4 * D) ≤ Lτ := (le_div_iff₀ (by positivity)).mp hεD
  have hEAs : ε * A ≤ (1 / 2 - κ) / 4 := (le_div_iff₀ hA).mp hεAs
  have hEBs : ε * B ≤ (1 / 2 - κ) / 4 := (le_div_iff₀ hB).mp hεBs
  refine ⟨ε, hε, by linarith, ?_⟩
  intro ca cb hca hcaε hcb hcbε regime side S ζ x₀ ℓ h hℓ hℓh hh1 hbal
  have hh : 0 < h := hℓ.trans_le hℓh
  have hca1 : ca ≤ 1 := by linarith
  have hcb1 : cb ≤ 1 := by linarith
  have hcab : ca * cb ≤ cb := mul_le_of_le_one_left hcb hca1
  have hcabε : ca * cb ≤ ε := hcab.trans hcbε
  have h4 : 0 ≤ 4 * ca * cb := by positivity
  have heq : 4 * (ca * ℓ ^ α.exponent) * (cb * ℓ ^ β.exponent) =
      (4 * ca * cb) * h ^ γ.exponent := by
    rw [hbal, Real.rpow_add hℓ]
    ring
  have hp := ha S ζ x₀ ℓ h ca hℓ hℓh hh1 hca
  have hy := hb S ζ x₀ ℓ h cb hℓ hℓh hh1 hcb
  have hTβ := he x₀ h (4 * ca * cb) hh hh1 h4
  have hTγ := hd x₀ h (4 * ca * cb) hh hh1 h4
  rw [← heq] at hTβ hTγ
  have hTγ' := hTγ.mono (show D * (4 * ca * cb) ≤ Lτ by
    nlinarith [mul_le_mul_of_nonneg_left hcabε hD.le])
  have hArad : 1 / 2 + A * ca ≤ Lπ := by
    nlinarith [mul_le_mul_of_nonneg_left hcaε hA.le]
  have hBrad : 1 / 2 + B * cb + E * (4 * ca * cb) / 2 ≤ L₀ := by
    have hh₁ := mul_le_mul_of_nonneg_left hcab hE.le
    have hh₂ := mul_le_mul_of_nonneg_left hcbε (show 0 ≤ B + 2 * E by positivity)
    nlinarith
  have hAs : A * ca ≤ (1 / 2 - κ) / 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hcaε hA.le]
  have hBs : B * cb ≤ (1 / 2 - κ) / 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hcbε hB.le]
  have hTs : ∀ x, |targetField x₀ h
      (4 * (ca * ℓ ^ α.exponent) * (cb * ℓ ^ β.exponent)) x| ≤ (1 / 2 - κ) / 4 := by
    intro x
    apply (targetField_abs_le _ _ _ _).trans
    rw [heq, abs_of_nonneg (mul_nonneg h4 (Real.rpow_nonneg hh.le _))]
    have hpw := Real.rpow_le_one hh.le hh1 γ.exponent_nonneg
    calc
      _ ≤ 4 * ca * cb := mul_le_of_le_one_right h4 hpw
      _ ≤ 4 * ε := by nlinarith
      _ ≤ (1 / 2 - κ) / 4 := by linarith
  exact fields_legal_of_controls regime side S ζ x₀ ℓ h _ _ α β γ Lπ L₀ Lτ κ
    (A * ca) (B * cb) (E * (4 * ca * cb)) hLπ.le hL₀.le hLτ.le hκ
    hp hy hTβ hTγ' hArad hBrad hAs hBs hTs

end CausalLowerbound.UniformLowerBound
