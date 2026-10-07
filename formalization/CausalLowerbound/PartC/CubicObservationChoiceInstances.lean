import CausalLowerbound.PartC.CubicObservationFactors

/-! Fix the finite enumeration of cubic choices before specializing the
ordered carrier slots. This keeps sums over choices independent of the
local decidable-equality instance used for the physical Fin Q slots. -/

noncomputable section
set_option autoImplicit false
open scoped Classical

namespace CausalLowerbound.PartC

def cubicObservationChoiceFintype (K : Type*) [Fintype K] :
    Fintype (CubicObservationChoice K) := inferInstance

def cubicObservationChoiceDecidableEq (K : Type*) [DecidableEq K] :
    DecidableEq (CubicObservationChoice K) := inferInstance

end CausalLowerbound.PartC
