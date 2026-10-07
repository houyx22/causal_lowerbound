import CausalLowerbound.PartC.CarrierLocalSigns
import CausalLowerbound.PartC.RepresentativeLocality
import CausalLowerbound.PartB.CarrierProbability

/-! Every physical carrier atom, its countable mixture, and its actual
density read only rough symbols intersecting that carrier box. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Representative
variable {d ι : Type*} [Fintype d] [DecidableEq d] [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem physicalCenteredFactor_symbol_zero (x₀ : d → ℝ) (ℓ r h : ℝ) (hr : r ≠ 0)
    (k : d → ℤ) (c w N : ℝ) (hc : 0 < c) (e : Fin (D + 1)) (q : d → ℤ) (b : Bool)
    (j : activeBlocks (d := d) ℓ h) (hj : j ∉ carrierLocalSigns x₀ ℓ r h k) :
    factorSymbol j (physicalCenteredFactor x₀ ℓ r h k c w N e q b) = 0 := by
  simp only [physicalCenteredFactor, centeredFactor, map_smul, map_sub,
    factorSymbol_basisFactor, factorSymbol_constantWalsh,
    normalizedTrigCenter_symbol_zero x₀ ℓ r h hr k c w N hc e.val q b j hj,
    map_zero, sub_zero, smul_zero]

theorem physicalDictionary_symbol_zero (x₀ : d → ℝ) (ℓ r h : ℝ) (hr : r ≠ 0)
    (k : d → ℤ) (c w N θ : ℝ) (hc : 0 < c) (m : PolynomialAtom d ι D)
    (j : activeBlocks (d := d) ℓ h) (hj : j ∉ carrierLocalSigns x₀ ℓ r h k) :
    factorSymbol j (physicalDictionary x₀ ℓ r h k c w N θ m) = 0 := by
  have hb := atomFactor_symbol_bound
    (fun i => physicalCenteredFactor x₀ ℓ r h k c w N (m.1 i).1 (m.1 i).2.1 (m.1 i).2.2)
    θ m.2 j 0 le_rfl (fun i => by
      rw [physicalCenteredFactor_symbol_zero x₀ ℓ r h hr k c w N hc _ _ _ j hj, norm_zero])
  apply norm_le_zero_iff.mp
  simpa only [mul_zero] using hb

theorem physicalDictionaryTensor_symbol_zero (x₀ : d → ℝ) (ℓ r h : ℝ) (hr : r ≠ 0)
    (k : d → ℤ) (c w N θ : ℝ) (hc : 0 < c) (m : PolynomialAtom d ι D)
    (j : activeBlocks (d := d) ℓ h) (hj : j ∉ carrierLocalSigns x₀ ℓ r h k) :
    symbolPart j (physicalDictionaryTensor x₀ ℓ r h k c w N θ m) = 0 := by
  have hb := tensor_symbol_bound j (fun _ : ι => physicalDictionary x₀ ℓ r h k c w N θ m)
    ‖physicalDictionary x₀ ℓ r h k c w N θ m‖ 0 (norm_nonneg _) le_rfl (fun _ => le_rfl)
    (fun _ => by rw [physicalDictionary_symbol_zero x₀ ℓ r h hr k c w N θ hc m j hj, norm_zero])
  apply norm_le_zero_iff.mp
  simpa only [mul_zero, zero_mul] using hb

attribute [local instance] polynomialAtomEncodable

theorem naturalPhysicalAtom_symbol_zero (x₀ : d → ℝ) (ℓ r h : ℝ) (hr : r ≠ 0)
    (k : d → ℤ) (c w N θ : ℝ) (hc : 0 < c) (n : ℕ)
    (j : activeBlocks (d := d) ℓ h) (hj : j ∉ carrierLocalSigns x₀ ℓ r h k) :
    symbolPart j (naturalPhysicalAtom (ι := ι) (D := D) x₀ ℓ r h k c w N θ n) = 0 := by
  unfold naturalPhysicalAtom naturalPolynomialAtom
  cases Encodable.decode (α := PolynomialAtom d ι D) n with
  | none => exact symbolPart_unit j
  | some m => exact physicalDictionaryTensor_symbol_zero x₀ ℓ r h hr k c w N θ hc m j hj

theorem pairedPhysicalAtom_symbol_zero (x₀ : d → ℝ) (ℓ r h : ℝ) (hr : r ≠ 0)
    (k : d → ℤ) (c w N θ : ℝ) (hc : 0 < c) (n : ℕ)
    (j : activeBlocks (d := d) ℓ h) (hj : j ∉ carrierLocalSigns x₀ ℓ r h k) :
    symbolPart j (pairedAtom reflection
      (naturalPhysicalAtom (ι := ι) (D := D) x₀ ℓ r h k c w N θ) n) = 0 := by
  unfold pairedAtom
  cases PairedSeries.labels.symm n with
  | inl m => exact naturalPhysicalAtom_symbol_zero x₀ ℓ r h hr k c w N θ hc m j hj
  | inr m =>
    rw [Sum.elim_inr, symbolPart_reflection,
      naturalPhysicalAtom_symbol_zero x₀ ℓ r h hr k c w N θ hc m j hj, map_zero]

theorem physicalCarrier_series_symbol_zero (x₀ : d → ℝ) (ℓ r h : ℝ) (hr : r ≠ 0)
    (k : d → ℤ) (c w N θ : ℝ) (hc : 0 < c) (weight : ℕ → ℝ)
    (B : Array d ι (activeBlocks (d := d) ℓ h) D)
    (hB : HasSum (fun n => weight n • CarrierCoefficients.labeledAtom unit
      (pairedAtom reflection (naturalPhysicalAtom (ι := ι) (D := D) x₀ ℓ r h k c w N θ)) n) B)
    (j : activeBlocks (d := d) ℓ h) (hj : j ∉ carrierLocalSigns x₀ ℓ r h k) :
    symbolPart j B = 0 := by
  have hz (n : ℕ) : symbolPart j (CarrierCoefficients.labeledAtom unit
      (pairedAtom reflection (naturalPhysicalAtom (ι := ι) (D := D) x₀ ℓ r h k c w N θ)) n) = 0 := by
    cases n with
    | zero => exact symbolPart_unit j
    | succ m => exact pairedPhysicalAtom_symbol_zero x₀ ℓ r h hr k c w N θ hc m j hj
  have hs : HasSum (fun _ : ℕ => (0 : Array d ι (activeBlocks (d := d) ℓ h) D)) (symbolPart j B) := by
    simpa only [map_smul, hz, smul_zero] using (symbolPart j).hasSum hB
  exact hs.unique hasSum_zero

theorem naturalPhysicalDensity_local_congr (x₀ : d → ℝ) (ℓ r h : ℝ) (hr : r ≠ 0)
    (k : d → ℤ) (c w N θ : ℝ) (hc : 0 < c) (n : ℕ)
    (ζ ζ' : activeBlocks (d := d) ℓ h → Bool)
    (hζ : ∀ j ∈ carrierLocalSigns x₀ ℓ r h k, ζ j = ζ' j)
    (u : d → ℝ) (hu : u ∈ Set.Icc (0 : d → ℝ) 1) :
    naturalPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ n ζ u =
      naturalPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ n ζ' u := by
  unfold naturalPhysicalDensity
  cases Encodable.decode (α := PolynomialAtom d ι D) n with
  | none => rfl
  | some m =>
    dsimp only
    rw [normalizedRoughChart_local_congr x₀ ℓ r h hr k c w N ζ ζ' hζ u hu,
      factorValue_local_congr (carrierLocalSigns x₀ ℓ r h k) _
        (fun j hj => physicalDictionary_symbol_zero x₀ ℓ r h hr k c w N θ hc m j hj) _ _ ζ ζ' hζ]

theorem pairedPhysicalDensity_local_congr (x₀ : d → ℝ) (ℓ r h : ℝ) (hr : r ≠ 0)
    (k : d → ℤ) (c w N θ : ℝ) (hc : 0 < c) (n : ℕ)
    (ζ ζ' : activeBlocks (d := d) ℓ h → Bool)
    (hζ : ∀ j ∈ carrierLocalSigns x₀ ℓ r h k, ζ j = ζ' j)
    (u : d → ℝ) (hu : u ∈ Set.Icc (0 : d → ℝ) 1) :
    pairedPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ n ζ u =
      pairedPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ n ζ' u := by
  unfold pairedPhysicalDensity
  cases PairedSeries.labels.symm n with
  | inl m => exact naturalPhysicalDensity_local_congr x₀ ℓ r h hr k c w N θ hc m ζ ζ' hζ u hu
  | inr m =>
    exact naturalPhysicalDensity_local_congr x₀ ℓ r h hr k c w N θ hc m _ _
      (fun j hj => by simp only [Walsh.flip, hζ j hj]) u hu

theorem carrierPhysicalDensity_local_congr (x₀ : d → ℝ) (ℓ r h : ℝ) (hr : r ≠ 0)
    (k : d → ℤ) (c w N θ : ℝ) (hc : 0 < c) (n : ℕ)
    (ζ ζ' : activeBlocks (d := d) ℓ h → Bool)
    (hζ : ∀ j ∈ carrierLocalSigns x₀ ℓ r h k, ζ j = ζ' j)
    (u : d → ℝ) (hu : u ∈ Set.Icc (0 : d → ℝ) 1) :
    carrierPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ n ζ u =
      carrierPhysicalDensity (ι := ι) (D := D) x₀ ℓ r h k c w N θ n ζ' u := by
  cases n with
  | zero => rfl
  | succ m => exact pairedPhysicalDensity_local_congr x₀ ℓ r h hr k c w N θ hc m ζ ζ' hζ u hu

end CausalLowerbound.PartC
