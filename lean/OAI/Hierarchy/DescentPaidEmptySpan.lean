import OAI.Hierarchy.DescentResetSelectedPrimaryRange
import OAI.Hierarchy.DescentRetainedAssignedDigits

namespace OAI
/-! # Reading a zero range digit from the physical request for a retained actor -/

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentSIMDLookup DescentRetainedRangeDigits
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {z : a.Atlas} {roots : a.RootInputs} {menu : OperandMenu z roots}
local notation "cfg" => publicOperands z roots menu.payload
local notation "C" => a.successor.setup
local notation "L" => (C).retained
variable {U : ℕ} {name : Fin U→Fin a.successor.setup.placement.sparse}
    {which : a.successor.setup.seven.control.Targets} {X : a.successor.setup.seven.Packets} {panels : a.successor.setup.retained.Strips}
    {host : a.successor.setup.placement.oldHosts=a.successor.setup.retained.hosts} {group : a.successor.setup.placement.groups*a.successor.setup.placement.blocks=a.successor.setup.retained.grouped}
    {block : Fin a.successor.setup.placement.blocks} {rack : Fin a.successor.setup.placement.newHosts} {g : Fin a.successor.setup.placement.groups}
    {arg : Fin a.successor.setup.retained.args} {slot : Fin a.successor.setup.retained.nodes} {f : Fin 3}
    {values : (publicOperands z roots menu.payload).Data a.successor.middle.rotorBits}
    {blank : ((publicOperands z roots menu.payload).oldConfig.header ((publicOperands z roots menu.payload).basic values) 0).val=0 → ((publicOperands z roots menu.payload).reg values 1).val=0}
    {physical : ∀inside : rack.val<U,((publicOperands z roots menu.payload).oldConfig.header ((publicOperands z roots menu.payload).basic values) 0).val≠0 →
      ((publicOperands z roots menu.payload).reg values 3).val=(a.successor.setup.placement.shape (name ⟨rack.val,inside⟩)).val}
local notation "key" => (L).outputID 1 (page f) arg slot
local notation "data" => (C).assignedDigits host group which X panels
local notation "measure" => menu.spanValue name data key block rack g values
  (finProdFinEquiv (arg,slot)) (page f) blank physical

/-- A retained blank source contributes zero after both native word casts on the
same issued actor. This also applies to the length field at an unused node. -/
theorem paid_empty_span {valueBits amount : ℕ}
    (emitted : amount=((measure).val : Cell valueBits).val)
    {alive : rack.val<U}
    (keep : menu.keep ((C).placement.shape (name ⟨rack.val,alive⟩))=true)
    (zero : (C).seven.decoded which X panels key ((C).placement.shape (name ⟨rack.val,alive⟩))
      (((C).placement.previous (name ⟨rack.val,alive⟩)).cast host)
      ((finProdFinEquiv (g,block)).cast group)=0) : amount=0 := by
  have read := menu.selected_primary_decoded name which X panels host group block rack g alive
    arg slot f values blank physical keep
  change (measure)=_ at read
  exact emitted.trans (by simp [read,zero])

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
