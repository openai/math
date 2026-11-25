import OAI.Hierarchy.DescentTerminalResetRoleArity
import OAI.Hierarchy.DescentOrdinaryUnfundedArity

namespace OAI
/-! # The funding flag and structural arity at the end of the same reset execution -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs
open DescentSixParty DescentSIMDLookup DescentPackedColony DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} {u : a.DateInputs floor w} (z : u.FinalInputs)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "md" => (v).metadata
local notation "c" => (md).chart
local notation "meta" => (v).primitiveEnd b

theorem dated_node_fields (fit : z.Room) {before mid dst : Memory w}
    (ran : (date z).Runs before dst) (operands : u.throughOperandDate.Runs before mid)
    (amount : Fin (c).blocks→Fin (c).hosts→Fin (c).groups→Cell (md).paidBits)
    (sp : Fin (c).blocks→Fin (c).nodes→Fin u.operand.slots→Fin (c).hosts→Fin (c).groups→Cell (md).spanBits)
    (arity : Fin (c).blocks→Fin (c).nodes→Fin (c).hosts→Fin (c).groups→ℕ)
    (bounded : ∀x n h g,arity x n h g≤u.operand.slots)
    (live : ∀x n j h g,sp x n j h g≠0 ↔ j.val<arity x n h g)
    (count : ∀x,Source ((paid u) x) (amount x) (c).lanes (z.tokenImage (z.roleInput mid)))
    (ranges : ∀x n j,Source (z.spans x n j) (sp x n j) (c).lanes (z.tokenImage (z.roleInput mid)))
    (f : Fin 2) (x : Fin (c).blocks) :
    Reads ((c).bank ((c).inputsEnd meta (md).paidBits (md).spanBits) f x)
      (fun h g=>encode (c).bits (c).nodes (fun n=>if f=0 then
        (if n.val<(amount x h g).val then 1 else 0) else (arity x n h g:Cell (c).bits))) (c).lanes dst:=by
  rw [PhysicalReset.date_image z fit ran operands]
  exact (c).metadataPair meta (md).paidBits (md).spanBits (paid u) z.spans (z.tokenImage (z.roleInput mid))
    amount sp arity bounded live fit.count fit.spans count ranges fit.endFits f x

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs

end OAI
