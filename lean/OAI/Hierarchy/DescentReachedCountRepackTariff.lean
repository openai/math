import OAI.Hierarchy.DescentReachedCountRepackBill
import OAI.Hierarchy.DescentReachedCountRepitch
import OAI.Hierarchy.DescentReachedCountRate
import OAI.Hierarchy.DescentResetCanvasIngressRate

namespace OAI
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.RoleCounts.Repitch
open DescentPackedColony DescentSIMDLookup DescentStaticWordColumn DescentDatedAddressBook DescentPaidResidentCount
open ProtocolRAM Filter
noncomputable section
set_option quotPrecheck false
variable (H G old M k paths b : ℕ)
local notation "S" => shape H G old M k b
local notation "L" base => count H G old M k paths b base

theorem price (base w unit : ℕ) (P : Ports paths) (atom : ℕ→Expr) (cost : ∀j<2^k,(atom j).work ≤ unit)
    (pos : 0 < old) (live : 0<M) :
    let p:=phase H G old M k paths b base w P atom
    p.ticks+7*names p.program ≤ bill H G old M k paths b base unit := by
  intro p
  let es:=pages H G old M k b base
  have seven : ∀j<(L base).blocks,(es j).work≤7:=fun _ _=>le_rfl
  have first:=DescentVenueSlabs.ExprInputs.price (S) (fun j=>atom j.val) base w unit
    (fun j=>cost _ j.isLt) pos live
  have t:=(L base).ticks_bound P es 7 seven
  have hw:=(L base).text_bound (w:=w) P es 7 seven
  change (_+(L base).ticks P es)+7*names ((DescentVenueSlabs.ExprInputs.program (S) _ base w).seq
    ((L base).program w P es))≤_
  rw [names_seq]
  dsimp only [bill,DescentVenueSlabs.ExprInputs.phase]
  norm_num1 at t
  omega

end
end Hierarchy.DescentOrdinaryAtomFieldRAM.RoleCounts.Repitch

end OAI
