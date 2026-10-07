import CausalLowerbound.FiniteReindex
import CausalLowerbound.PartB.FiniteRademacher

/-! Independent resampling of disjoint groups of a shared finite sign
field. A separate copy retains all signs outside the local groups, so
functions of those outside signs need not be constant. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.FiniteLaw

theorem expect_independent_coordinate {K Ω : Type*} [Fintype K] [DecidableEq K]
    [Fintype Ω] [Inhabited Ω] (μ : K → FiniteLaw Ω) (i : K) (f : Ω → ℝ) :
    (independent μ).expect (fun x => f (x i)) = (μ i).expect f := by
  rw [expect_independent_split μ i]
  simp [Equiv.funSplitAt, Equiv.piSplitAt]

theorem expect_independent_option {K Ω : Type*} [Fintype K] [DecidableEq K] [Fintype Ω]
    (μ : Option K → FiniteLaw Ω) (f : (Option K → Ω) → ℝ) :
    (independent μ).expect f = (μ none).expect (fun base =>
      (independent (fun i => μ (some i))).expect (fun fresh => f (fun i => i.elim base fresh))) := by
  simp only [expect, independent]
  rw [← (Equiv.piOptionEquivProd (β := fun _ : Option K => Ω)).symm.sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.prod_option, Equiv.piOptionEquivProd,
    Equiv.coe_fn_symm_mk, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro base _
  apply Finset.sum_congr rfl
  intro fresh _
  have he : (fun a : Option K => Option.rec base (fun val => fresh val) a) =
      (fun a : Option K => a.elim base fresh) := by
    funext a
    cases a <;> rfl
  rw [he, mul_assoc]

end CausalLowerbound.FiniteLaw

namespace CausalLowerbound.PartC
open PartB
variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

theorem independentSigns_expect_select (owner : J → V) (f : (J → Bool) → ℝ) :
    (FiniteLaw.independent (fun _ : V => independentSigns (ι := J))).expect
      (fun ω => f (fun j => ω (owner j) j)) = independentSigns.expect f := by
  simp only [independentSigns]
  rw [FiniteLaw.expect_independent_transpose (fun (_ : V) (_ : J) => rademacher)
    (fun ω => f (fun j => ω (owner j) j))]
  exact FiniteLaw.independent_replace_maps
    (fun _ : J => independentSigns (ι := V)) (fun _ : J => rademacher)
    (fun j x => x (owner j)) (fun _ b => b) f (fun j x =>
      FiniteLaw.expect_independent_coordinate (fun _ : V => rademacher) (owner j)
        (fun b => f (Function.update x j b)))

theorem owned_sign_resampling {A : Type*} (owner : J → Option V)
    (F : V → (J → Bool) → A) (g : (J → Bool) → (V → A) → ℝ)
    (hF : ∀ i ζ ζ', (∀ j, owner j = some i → ζ j = ζ' j) → F i ζ = F i ζ')
    (hg : ∀ ζ ζ' x, (∀ j, owner j = none → ζ j = ζ' j) → g ζ x = g ζ' x) :
    independentSigns.expect (fun ζ => g ζ (fun i => F i ζ)) =
      independentSigns.expect (fun base =>
        (FiniteLaw.independent (fun _ : V => independentSigns (ι := J))).expect
          (fun fresh => g base (fun i => F i (fresh i)))) := by
  rw [← independentSigns_expect_select owner (fun ζ => g ζ (fun i => F i ζ))]
  have he (ω : Option V → J → Bool) :
      g (fun j => ω (owner j) j) (fun i => F i (fun j => ω (owner j) j)) =
        g (ω none) (fun i => F i (ω (some i))) := by
    have hf : (fun i => F i (fun j => ω (owner j) j)) = (fun i => F i (ω (some i))) := by
      funext i
      apply hF i
      intro j hj
      rw [hj]
    rw [hf]
    apply hg
    intro j hj
    rw [hj]
  simp_rw [he]
  rw [FiniteLaw.expect_independent_option]
  rfl

def localSignOwner (T : V → Finset J) (j : J) : Option V :=
  if h : ∃ i, j ∈ T i then some (Classical.choose h) else none

theorem localSignOwner_none (T : V → Finset J) (j : J) :
    localSignOwner T j = none ↔ ∀ i, j ∉ T i := by
  by_cases h : ∃ i, j ∈ T i
  · simp [localSignOwner, h, not_forall, not_not]
  · simp only [localSignOwner, dif_neg h, true_iff]
    simpa only [not_exists] using h

theorem localSignOwner_of_mem (T : V → Finset J)
    (hT : ∀ i i', i ≠ i' → Disjoint (T i) (T i')) (i : V) (j : J) (hj : j ∈ T i) :
    localSignOwner T j = some i := by
  have he : ∃ i, j ∈ T i := ⟨i, hj⟩
  rw [localSignOwner, dif_pos he]
  have hc : Classical.choose he = i := by
    by_contra hn
    exact (Finset.disjoint_left.mp (hT _ _ hn)) (Classical.choose_spec he) hj
  rw [hc]

theorem disjoint_sign_resampling {A : Type*} (T : V → Finset J)
    (hT : ∀ i i', i ≠ i' → Disjoint (T i) (T i'))
    (F : V → (J → Bool) → A) (g : (J → Bool) → (V → A) → ℝ)
    (hF : ∀ i ζ ζ', (∀ j ∈ T i, ζ j = ζ' j) → F i ζ = F i ζ')
    (hg : ∀ ζ ζ' x, (∀ j, (∀ i, j ∉ T i) → ζ j = ζ' j) → g ζ x = g ζ' x) :
    independentSigns.expect (fun ζ => g ζ (fun i => F i ζ)) =
      independentSigns.expect (fun base =>
        (FiniteLaw.independent (fun _ : V => independentSigns (ι := J))).expect
          (fun fresh => g base (fun i => F i (fresh i)))) := by
  apply owned_sign_resampling (localSignOwner T) F g
  · intro i ζ ζ' h
    apply hF i ζ ζ'
    intro j hj
    exact h j (localSignOwner_of_mem T hT i j hj)
  · intro ζ ζ' x h
    apply hg ζ ζ' x
    intro j hj
    exact h j ((localSignOwner_none T j).mpr hj)

end CausalLowerbound.PartC
