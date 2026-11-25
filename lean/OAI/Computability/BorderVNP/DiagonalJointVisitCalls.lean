import OAI.Computability.BorderVNP.DiagonalJointSparseWindow

/-! # The private-call state at the end of an actual joint preparation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PinStart

open VPVNP.BurstRAM BorderVNP.Cube TeamContraction CompactMachine CellMacro.Generator
open TeamContraction.ProcessorSlots

variable {R n w d b h K s : ℕ} (id : TableEntry d b h K s → ℕ)
    (U : Fin (R+1) → PinStart SparseExterior.driver n w)
local notation3 (prettyPrint := false) "mac(" u ")" => install SparseExterior.driver n (U u).routines

/-- The original full pre-call return and its last argument visit have the
same register and memory contents. -/
theorem visits_state {u} (p : (U u).Prefix id) : p.2.val.2=(visits id U p).arguments.val.2 := by
  have eq := SignedPrep.visitsEquiv_outState id (U u).pub mac(u) (visits id U p)
  simpa only [visits,Equiv.apply_symm_apply] using eq

/-- The very same private-call trace starting from the last actual argument
visit, with the same returned bank, memory and instruction transcript. -/
def callAtArguments {u} (p : (U u).Prefix id)
    (call : Returns callOwnedCells (U u).pub mac(u) p.2.val.2.1 p.2.val.2.2) :
    let v := visits id U p
    Returns callOwnedCells (U u).pub mac(u) v.arguments.val.2.1 v.arguments.val.2.2 :=
  ⟨call.val, by rw [← visits_state id U p]; exact call.property⟩

end RoutingISA.Evaluator.PinStart

end BorderVNP
end Computability
end OAI
