import CausalLowerbound.PartB.LagrangeCoefficients

/-! An undirected complete graph with each edge represented exactly once.
The incidence fibers are equivalent to the other vertices. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartB.ShellGeometry
open ConfigurationShells

variable {V d : Type*} [Fintype V] [LinearOrder V] [Fintype d] [DecidableEq d]

abbrev CompleteEdge (V : Type*) [LinearOrder V] := {p : V × V // p.1 < p.2}
def edgeLeft (e : CompleteEdge V) : V := e.val.1
def edgeRight (e : CompleteEdge V) : V := e.val.2

theorem edgeLeft_ne_right (e : CompleteEdge V) : edgeLeft e ≠ edgeRight e := ne_of_lt e.property

def otherVertex (i : V) (e : {e : CompleteEdge V // incident edgeLeft edgeRight i e}) : V :=
  if edgeLeft e.val = i then edgeRight e.val else edgeLeft e.val

theorem otherVertex_ne (i : V) (e : {e : CompleteEdge V // incident edgeLeft edgeRight i e}) :
    otherVertex i e ≠ i := by
  rcases e with ⟨e, he⟩
  unfold otherVertex
  split_ifs with h
  · intro hb
    exact edgeLeft_ne_right e (h.trans hb.symm)
  · exact h

def incidentEdgeOfNeighbor (i : V) (j : {j : V // j ≠ i}) :
    {e : CompleteEdge V // incident edgeLeft edgeRight i e} :=
  if h : i < j.val then ⟨⟨(i, j.val), h⟩, Or.inl rfl⟩
  else ⟨⟨(j.val, i), lt_of_le_of_ne (le_of_not_gt h) j.property⟩, Or.inr rfl⟩

theorem otherVertex_edgeOfNeighbor (i : V) (j : {j : V // j ≠ i}) :
    otherVertex i (incidentEdgeOfNeighbor i j) = j.val := by
  unfold incidentEdgeOfNeighbor
  split_ifs <;> simp [otherVertex, edgeLeft, edgeRight, j.property]

def incidentNeighborEquiv (i : V) :
    {e : CompleteEdge V // incident edgeLeft edgeRight i e} ≃ {j : V // j ≠ i} where
  toFun e := ⟨otherVertex i e, otherVertex_ne i e⟩
  invFun := incidentEdgeOfNeighbor i
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    rcases e with ⟨⟨⟨l, r⟩, hlr⟩, hi⟩
    change l = i ∨ r = i at hi
    rcases hi with rfl | rfl
    · simp [incidentEdgeOfNeighbor, otherVertex, edgeLeft, edgeRight, hlr]
    · simp [incidentEdgeOfNeighbor, otherVertex, edgeLeft, edgeRight,
        ne_of_lt hlr, not_lt.mpr hlr.le]
  right_inv j := Subtype.ext (otherVertex_edgeOfNeighbor i j)

def pairLinear (u v : d → ℝ) : MvPolynomial (d × Bool) ℝ :=
  ∑ k : Option (d × Bool), MvPolynomial.monomial (atomDegree k)
    (atomSign k * elementaryCoefficient u v k)

def completeLagrangePolynomial (i : V) (u : V × d → ℝ) : MvPolynomial (d × Bool) ℝ :=
  ∏ j : {j : V // j ≠ i}, pairLinear (configurationSite u i) (configurationSite u j.val)

def completeVertexProduct (i : V) (u : V × d → ℝ) : ℝ :=
  ∏ j : {j : V // j ≠ i}, truncatedDistance (configurationSite u i) (configurationSite u j.val)

theorem incident_graphFactor (i : V)
    (e : {e : CompleteEdge V // incident edgeLeft edgeRight i e}) (k : Option (d × Bool))
    (u : V × d → ℝ) :
    graphFactor edgeLeft edgeRight (e.val, incidentOrientation edgeRight i e.val, k) u =
      elementaryCoefficient (configurationSite u i) (configurationSite u (otherVertex i e)) k := by
  rcases e with ⟨e, he⟩
  rcases he with h | h
  · have hn : edgeRight e ≠ i := by intro hr; exact edgeLeft_ne_right e (h.trans hr.symm)
    simp [graphFactor, incidentOrientation, otherVertex, h, hn]
  · have hn : edgeLeft e ≠ i := by intro hl; exact edgeLeft_ne_right e (hl.trans h.symm)
    simp [graphFactor, incidentOrientation, otherVertex, h, hn]

theorem lagrangePolynomial_complete (i : V) (u : V × d → ℝ) :
    lagrangePolynomial edgeLeft edgeRight i u = completeLagrangePolynomial i u := by
  unfold lagrangePolynomial completeLagrangePolynomial
  rw [← (incidentNeighborEquiv i).prod_comp]
  apply Finset.prod_congr rfl
  intro e _
  unfold lagrangeLinear pairLinear
  apply Finset.sum_congr rfl
  intro k _
  rw [incident_graphFactor]
  rfl

theorem vertexProduct_complete (i : V) (u : V × d → ℝ) :
    vertexProduct edgeLeft edgeRight (graphDistance edgeLeft edgeRight u) i =
      completeVertexProduct i u := by
  unfold vertexProduct
  rw [← Finset.prod_filter]
  rw [Finset.prod_subtype (p := incident edgeLeft edgeRight i) _ (by simp)]
  unfold completeVertexProduct
  rw [← (incidentNeighborEquiv i).prod_comp]
  apply Finset.prod_congr rfl
  intro e _
  change truncatedDistance (configurationSite u (edgeLeft e.val)) (configurationSite u (edgeRight e.val)) =
    truncatedDistance (configurationSite u i) (configurationSite u (otherVertex i e))
  rcases e with ⟨e, he⟩
  rcases he with h | h
  · simp [otherVertex, h]
  · have hn : edgeLeft e ≠ i := by intro hl; exact edgeLeft_ne_right e (hl.trans h.symm)
    simp [otherVertex, h, hn, truncatedDistance_symm]

def permuteConfiguration (σ : Equiv.Perm V) (u : V × d → ℝ) : V × d → ℝ :=
  fun p => u (σ p.1, p.2)

def neighborPermutation (σ : Equiv.Perm V) (i : V) : {j : V // j ≠ i} ≃ {j : V // j ≠ σ i} where
  toFun j := ⟨σ j.val, fun h => j.property (σ.injective h)⟩
  invFun j := ⟨σ.symm j.val, fun h => j.property (by simpa using congrArg σ h)⟩
  left_inv j := by ext; simp
  right_inv j := by ext; simp

theorem completeLagrangePolynomial_permute (σ : Equiv.Perm V) (i : V) (u : V × d → ℝ) :
    completeLagrangePolynomial i (permuteConfiguration σ u) = completeLagrangePolynomial (σ i) u := by
  unfold completeLagrangePolynomial
  exact (neighborPermutation σ i).prod_comp
    (fun j => pairLinear (configurationSite u (σ i)) (configurationSite u j.val))

theorem completeVertexProduct_permute (σ : Equiv.Perm V) (i : V) (u : V × d → ℝ) :
    completeVertexProduct i (permuteConfiguration σ u) = completeVertexProduct (σ i) u := by
  unfold completeVertexProduct
  exact (neighborPermutation σ i).prod_comp
    (fun j => truncatedDistance (configurationSite u (σ i)) (configurationSite u j.val))

theorem complete_lagrangeCoefficient_permute (σ : Equiv.Perm V) (i : V)
    (ν : d × Bool →₀ ℕ) (u : V × d → ℝ) :
    lagrangeCoefficient edgeLeft edgeRight i ν (permuteConfiguration σ u) =
      lagrangeCoefficient edgeLeft edgeRight (σ i) ν u := by
  simp only [lagrangeCoefficient, lagrangePolynomial_complete, completeLagrangePolynomial_permute]

theorem complete_graphTaper_permute (σ : Equiv.Perm V) (t : ℝ) (u : V × d → ℝ) :
    graphTaper edgeLeft edgeRight taperCutoff t (graphDistance edgeLeft edgeRight (permuteConfiguration σ u)) =
      graphTaper edgeLeft edgeRight taperCutoff t (graphDistance edgeLeft edgeRight u) := by
  simp only [graphTaper, vertexProduct_complete, completeVertexProduct_permute]
  exact Equiv.prod_comp σ (fun i => taperCutoff (completeVertexProduct i u / t))

end CausalLowerbound.PartB.ShellGeometry
