import CausalLowerbound.PartB.GlobalPriors
import CausalLowerbound.DiscreteIndependence

/-! Independence and density tilting of the actual countable block prior.
After conditioning on sites, the block labels remain independent with
their respective density-posterior laws. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace CausalLowerbound.PartB.ShellGeometry
variable {K Ω : Type*} [Fintype K] [DecidableEq K] [Fintype Ω]

theorem blockPrior_expect_prod (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (f : K → ℕ × Ω → ℝ) (B : K → ℝ) (hb : ∀ k z, |f k z| ≤ B k) :
    (blockPrior H kernel).expect (fun z => ∏ k, f k (z.1 k, z.2 k)) =
      ∏ k, (H.joint kernel).expect (f k) := by
  have hprod (z : (K → ℕ) × (K → Ω)) : |∏ k, f k (z.1 k, z.2 k)| ≤ ∏ k, B k := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun k _ => hb k _)
  unfold blockPrior
  rw [DiscreteLaw.expect_joint _ _ _ _ hprod]
  have he (labels : K → ℕ) : (blockKernel kernel labels).expect (fun y => ∏ k, f k (labels k, y k)) =
      ∏ k, (kernel (labels k)).expect (fun sample => f k (labels k, sample)) :=
    FiniteLaw.expect_independent_prod (fun k => kernel (labels k)) (fun k sample => f k (labels k, sample))
  simp_rw [he]
  rw [DiscreteLaw.expect_independent_prod (fun _ : K => H)
    (fun k label => (kernel label).expect (fun sample => f k (label, sample))) B
    (fun k label => (kernel label).abs_expect_le_bound _ _ (fun sample => hb k (label, sample)))]
  apply Finset.prod_congr rfl
  intro k _
  exact (H.expect_joint kernel (f k) (B k) (hb k)).symm

def varyingBlockPrior (H : K → DiscreteLaw ℕ) (kernel : K → ℕ → FiniteLaw Ω) :
    DiscreteLaw ((K → ℕ) × (K → Ω)) :=
  (DiscreteLaw.independent H).joint (fun labels => FiniteLaw.independent (fun k => kernel k (labels k)))

theorem varyingBlockPrior_weight (H : K → DiscreteLaw ℕ) (kernel : K → ℕ → FiniteLaw Ω)
    (z : (K → ℕ) × (K → Ω)) :
    (varyingBlockPrior H kernel).weight z = ∏ k, ((H k).joint (kernel k)).weight (z.1 k, z.2 k) := by
  simp only [varyingBlockPrior, DiscreteLaw.joint, DiscreteLaw.independent_weight,
    FiniteLaw.independent, Finset.prod_mul_distrib]

theorem blockPrior_label_product_expect (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (g : K → ℕ → ℝ) (B : K → ℝ) (hb : ∀ k label, |g k label| ≤ B k) :
    (blockPrior H kernel).expect (fun z => ∏ k, g k (z.1 k)) = ∏ k, H.expect (g k) := by
  rw [blockPrior_expect_prod H kernel (fun k z => g k z.1) B (fun k z => hb k z.1)]
  apply Finset.prod_congr rfl
  intro k _
  exact H.joint_expect_label kernel (g k) (B k) (hb k)

/-- Bayes' rule factorizes for the actual countable labels, with every
normalizer computed from the prior rather than assumed. -/
theorem blockPrior_tilt_product (H : DiscreteLaw ℕ) (kernel : ℕ → FiniteLaw Ω)
    (g : K → ℕ → ℝ) (lo hi : K → ℝ) (hlo : ∀ k, 0 < lo k)
    (hg : ∀ k label, lo k ≤ g k label ∧ g k label ≤ hi k) :
    (blockPrior H kernel).tilt (fun z => ∏ k, g k (z.1 k)) (∏ k, lo k) (∏ k, hi k)
      (Finset.prod_pos (fun k _ => hlo k))
      (fun z => ⟨Finset.prod_le_prod (fun k _ => (hlo k).le) (fun k _ => (hg k (z.1 k)).1),
        Finset.prod_le_prod (fun k _ => (hlo k).le.trans (hg k (z.1 k)).1) (fun k _ => (hg k (z.1 k)).2)⟩) =
      varyingBlockPrior (fun k => H.tilt (g k) (lo k) (hi k) (hlo k) (hg k)) (fun _ => kernel) := by
  have hnorm := blockPrior_label_product_expect H kernel g hi (fun k label => by
    rw [abs_of_nonneg ((hlo k).le.trans (hg k label).1)]
    exact (hg k label).2)
  apply DiscreteLaw.ext
  intro z
  simp only [DiscreteLaw.tilt, blockPrior_weight, varyingBlockPrior_weight, DiscreteLaw.joint,
    hnorm, Finset.prod_mul_distrib, Finset.prod_div_distrib]
  ring

end CausalLowerbound.PartB.ShellGeometry
