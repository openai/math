import OAI.Hierarchy.DescentDatedOperandTableFrame
import OAI.Hierarchy.DescentTerminalResetDatedFields

namespace OAI
/-! Sources in the actual operand lookup input after the final change of packed width. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentSIMDLookup DescentPackedZip ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor

theorem kept_entry (ok : u.Ready) (m : Memory w) (i : Fin (v).receiver.fields)
    {H G : ℕ} (x : Fin H→Fin G→Cell (v).setup.fieldBits)
    (fits : (u.rawOperands.kept i).Fits w ((v).keepBase b))
    (read : Source (u.rawOperands.kept i) x (v).receiver.lanes
      (((v).setup.code ((v).operandFloor b) w u.bank u.laws).image (u.beforeSetupImage ok m))) :
    Source (u.operand.kept i) (fun h g=>(x h g).val : Fin H→Fin G→Cell (v).receiver.valueBits)
       (v).receiver.lanes (u.operandEntry ok m) :=by
  have ord:=(v).operand_order b
  exact (v).keptValue_source b _ _ x fits read ((ord.1.trans (ord.2.trans ((v).final_ge b))).trans_lt ok.full)

theorem operand_entry_prefix (ok : u.Ready) (m : Memory w) :
    ∀z,z<(v).operandStart b→u.sheetsResult ok m z=u.operandEntry ok m z:=u.emitted_sheets_kept ok m

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
