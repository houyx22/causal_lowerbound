import CausalLowerbound.PartB.ObservationGraph

/-! Uniform counts of the actual active and incident carrier blocks. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace CausalLowerbound.PartB.ShellGeometry
variable {d I : Type*} [Fintype d] [DecidableEq d] [Fintype I]

def incidentBlocks (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (x : d → ℝ) : Finset (d → ℤ) :=
  S.filter (fun k => x ∈ carrierBox x₀ r k)

theorem incidentBlocks_card_le (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ) (x : d → ℝ) :
    (incidentBlocks S x₀ r x).card ≤ 5 ^ Fintype.card d := by
  rw [← carrierNeighbors_card (fun i => (x i - x₀ i) / r)]
  apply Finset.card_le_card
  intro k hk
  exact carrierBox_overlap x₀ r k x (Finset.mem_filter.mp hk).2

def configurationBlocks (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (x : I → d → ℝ) : Finset (d → ℤ) :=
  Finset.univ.biUnion (fun i => incidentBlocks S x₀ r (x i))

theorem configurationBlocks_card_le (S : Finset (d → ℤ)) (x₀ : d → ℝ) (r : ℝ)
    (x : I → d → ℝ) :
    (configurationBlocks S x₀ r x).card ≤ Fintype.card I * 5 ^ Fintype.card d := by
  calc
    _ ≤ ∑ i : I, (incidentBlocks S x₀ r (x i)).card := Finset.card_biUnion_le
    _ ≤ ∑ _i : I, 5 ^ Fintype.card d := Finset.sum_le_sum (fun i _ => incidentBlocks_card_le S x₀ r (x i))
    _ = _ := by simp

theorem activeBlocks_card_bound (r h : ℝ) (hr : 0 < r) (hrh : r ≤ h) :
    ((activeBlocks (d := d) r h).card : ℝ) ≤ (7 * (h / r)) ^ Fintype.card d := by
  have hx : 1 ≤ h / r := (le_div_iff₀ hr).mpr (by simpa using hrh)
  have hc0 : (0 : ℤ) ≤ ⌈h / r + 1⌉ := by
    exact_mod_cast (show (0 : ℝ) ≤ (⌈h / r + 1⌉ : ℝ) by linarith [Int.le_ceil (h / r + 1)])
  have hc : (⌈h / r + 1⌉ : ℝ) < h / r + 2 := by
    simpa only [add_assoc, one_add_one_eq_two] using Int.ceil_lt_add_one (h / r + 1)
  have hlen : 0 ≤ ⌈h / r + 1⌉ + 1 - -⌈h / r + 1⌉ := by omega
  have hcard : ((Finset.Icc (-⌈h / r + 1⌉) ⌈h / r + 1⌉).card : ℝ) =
      2 * (⌈h / r + 1⌉ : ℝ) + 1 := by
    rw [Int.card_Icc]
    have he : (((⌈h / r + 1⌉ + 1 - -⌈h / r + 1⌉).toNat : ℕ) : ℝ) =
        ((⌈h / r + 1⌉ + 1 - -⌈h / r + 1⌉ : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hlen
    rw [he]
    push_cast
    ring
  have hbound : ((Finset.Icc (-⌈h / r + 1⌉) ⌈h / r + 1⌉).card : ℝ) ≤ 7 * (h / r) := by
    rw [hcard]
    linarith
  have he : (activeBlocks (d := d) r h).card =
      (Finset.Icc (-⌈h / r + 1⌉) ⌈h / r + 1⌉).card ^ Fintype.card d := by
    simp [activeBlocks, Fintype.card_piFinset]
  rw [he, Nat.cast_pow]
  exact pow_le_pow_left₀ (by positivity) hbound _

end CausalLowerbound.PartB.ShellGeometry
