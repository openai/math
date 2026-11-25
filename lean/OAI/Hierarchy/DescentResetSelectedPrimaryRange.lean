import OAI.Hierarchy.DescentResetSelectedRange
import OAI.Hierarchy.DescentNativeRangePadding

namespace OAI
/-! # The three selected reset digits on a retained primary node -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu
open DescentSIMDLookup DescentRetainedRangeDigits DescentRetainedControl DescentRotorWindowArchive
open DescentResetOperandSetup.Chart DescentPackedZip
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {z : a.Atlas} {roots : a.RootInputs} (menu : OperandMenu z roots)
local notation "cfg" => publicOperands z roots menu.payload
local notation "C" => a.successor.setup
local notation "L" => (C).retained
variable {U : ℕ} (name : Fin U→Fin a.successor.setup.placement.sparse) (which : a.successor.setup.seven.control.Targets)
    (X : a.successor.setup.seven.Packets) (panels : a.successor.setup.retained.Strips)
    (host : a.successor.setup.placement.oldHosts=a.successor.setup.retained.hosts) (group : a.successor.setup.placement.groups*a.successor.setup.placement.blocks=a.successor.setup.retained.grouped)
    (block : Fin a.successor.setup.placement.blocks) (rack : Fin a.successor.setup.placement.newHosts) (g : Fin a.successor.setup.placement.groups)
    (alive : rack.val<U)
local notation "shp" => (C).placement.shape (name ⟨rack.val,alive⟩)
local notation "prev" => ((C).placement.previous (name ⟨rack.val,alive⟩)).cast host
local notation "cursor" => (finProdFinEquiv (g,block)).cast group
local notation "Y" => fun z' : Fin ((L).outputs*(C).placement.shapes) =>
  let pair:=finProdFinEquiv.symm z'
  DescentResetOperandSetup.Chart.reindexed host group ((C).seven.decoded which X panels pair.1 pair.2)
local notation "take_" => ownerAt (C) which X shp prev cursor
local notation "less_" => priorAt (C) X prev cursor
local notation "raw" => (L).site panels prev cursor
local notation "returned" => (L).routedWord take_ less_ raw
variable (arg : Fin a.successor.setup.retained.args) (slot : Fin a.successor.setup.retained.nodes) (f : Fin 3)
local notation "idx" => (finProdFinEquiv (arg,slot) : Fin (cfg).mouths)
local notation "key" => (L).outputID 1 (page f) arg slot
variable (values : (publicOperands z roots menu.payload).Data a.successor.middle.rotorBits)
    (blank : ((publicOperands z roots menu.payload).oldConfig.header ((publicOperands z roots menu.payload).basic values) 0).val=0 → ((publicOperands z roots menu.payload).reg values 1).val=0)
    (physical : ∀inside : rack.val<U,((publicOperands z roots menu.payload).oldConfig.header ((publicOperands z roots menu.payload).basic values) 0).val≠0 →
      ((publicOperands z roots menu.payload).reg values 3).val=(a.successor.setup.placement.shape (name ⟨rack.val,inside⟩)).val)
    (primary : menu.keep (a.successor.setup.placement.shape (name ⟨rack.val,alive⟩))=true)
local notation "measured" => menu.spanValue name Y key block rack g values idx (page f) blank physical

include primary in
theorem selected_primary_decoded :
    measured=(((C).seven.decoded which X panels key shp prev cursor).val : Cell (C).fieldBits) := by
  rw [menu.spanValue_primary name Y key block rack g values idx (page f) blank physical alive primary]
  simp only [DescentRetainedTargetPlacement.Chart.compact,DescentResetDenseOperand.dense,alive,dite_eq_left,
    DescentRetainedTargetPlacement.Chart.selected,primary,reindexed]
  erw [ite_true,finProdFinEquiv.symm_apply_apply]
  rfl

include primary in
theorem selected_previous (order : Fin a.successor.setup.retained.donors≃Fin a.successor.setup.retained.donors) (rank : ∀i,neighbors less_ i=(order i).val)
    (d : Fin a.successor.setup.retained.donors) (n : Fin a.successor.setup.retained.previousNodes) (yes : take_ d=true)
    (valid : n.val<a.successor.setup.retained.originalCount raw d) (number : slot.val=a.successor.setup.retained.offset returned (order d)+n.val)
    (j : Fin (L).previousArgs) (same : arg.val=j.val)
    (present : j.val<((L).entry raw d n (L).arityField).val) :
    measured=(((L).entry raw d n ((L).operandField (page f) j)).val : Cell (C).fieldBits) := by
  rw [menu.selected_primary_decoded name which X panels host group block rack g alive arg slot f values blank physical primary]
  exact congrArg (fun v : Cell (L).bits => (v.val : Cell (C).fieldBits))
    (decoded_range (C) which X panels shp prev cursor 1 order rank d n j yes valid present slot number arg same f)

include primary in
theorem selected_previous_padding (order : Fin a.successor.setup.retained.donors≃Fin a.successor.setup.retained.donors) (rank : ∀i,neighbors less_ i=(order i).val)
    (d : Fin a.successor.setup.retained.donors) (n : Fin a.successor.setup.retained.previousNodes) (yes : take_ d=true)
    (valid : n.val<a.successor.setup.retained.originalCount raw d) (number : slot.val=a.successor.setup.retained.offset returned (order d)+n.val)
    (past : ((L).entry raw d n (L).arityField).val≤arg.val) :
    measured=0 := by
  rw [menu.selected_primary_decoded name which X panels host group block rack g alive arg slot f values blank physical primary]
  exact (congrArg (fun v : Cell (L).bits => (v.val : Cell (C).fieldBits))
    (decoded_padding (C) which X panels shp prev cursor 1 order rank d n yes valid slot number arg past f)).trans (by simp)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI
