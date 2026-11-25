import OAI.Hierarchy.DescentResetSpanDispatch
import OAI.Hierarchy.DescentResetConvertedOld
import OAI.Hierarchy.DescentPhysicalOperandLaneSum
import OAI.Hierarchy.DescentRetainedRangeDigits

namespace OAI
/-! # The selected retained, private rotor and public range words on the shared output row -/
namespace Hierarchy.DescentResetOperandSetup.Chart
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentPackedZip DescentSIMDLookup DescentOperandFamilyBook
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (C : DescentResetOperandSetup.Chart) {H G w : ℕ} (base : ℕ) (laws : C.Laws)
variable (x : Fin C.placement.blocks) (arg : Fin C.retained.args) (node : Fin C.retained.nodes)
    (old : Fin C.inputs→Expr) (rotor : Fin 4→Expr) (surface : Fin C.fallbackInputs→Expr)
local notation "mouth" => (finProdFinEquiv (arg,node) : Fin C.members)
theorem selected_range (m : Memory w) (f : Fin 3)
    (prv left right target : Values H G C.fieldBits)
    (seen : Source (C.oldValue base x arg node (DescentRetainedRangeDigits.page f)) prv C.lanes m)
    (root : Source (expr laws.rotorFields C.lanes (C.rotorFields base)
      (finProdFinEquiv (DescentRetainedRangeDigits.page f,mouth)) rotor) left C.lanes m)
    (tree : Source (expr laws.fallbackFields C.lanes (C.fallbackFields base)
      (finProdFinEquiv (DescentRetainedRangeDigits.page f,mouth)) surface) right C.lanes m)
    (amount : ∀h g,(target h g).val=(prv h g).val+(left h g).val+(right h g).val) :
    Source (C.selected base laws (some (DescentRetainedRangeDigits.page f)) x arg node old rotor surface) target C.lanes m := by
  have different : ¬(DescentRetainedRangeDigits.page f=2 ∨ DescentRetainedRangeDigits.page f=3) := by
    fin_cases f <;> decide
  let pair : Values H G C.fieldBits:=fun h g=>⟨(left h g).val+(right h g).val,by
    have eqn:=amount h g
    have bound:=(target h g).isLt
    omega⟩
  have middle:=sum_source m pair left right _ _ root tree (fun _ _=>rfl)
  have oldRead : Source (.op .add (C.oldValue base x arg node (DescentRetainedRangeDigits.page f)) (.lit 0)) prv C.lanes m:=by
    intro j
    change (C.oldValue base x arg node (DescentRetainedRangeDigits.page f)).eval m _+0=_
    rw [add_zero,seen j]
  simpa only [selected,ite_eq_right different] using
    (sum_source m target prv pair _ _ oldRead middle (fun h g=>by simpa only [pair,Nat.add_assoc] using amount h g))

end
end Hierarchy.DescentResetOperandSetup.Chart

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentSIMDLookup DescentPackedZip DescentOperandFamilyBook
open DescentResetOperandSetup DescentRetainedTargetPlacement
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {z : a.Atlas} {roots : a.RootInputs} (menu : OperandMenu z roots)
local notation "cfg" => publicOperands z roots menu.payload
local notation "C" => a.successor.setup
variable {w : ℕ} (base : ℕ) (s : a.successor.setup.Sources) (f : a.successor.setup.Laws) (m : Memory w) {U : ℕ}
    (name : Fin U→Fin a.successor.setup.placement.sparse)
    (tables : Fin (a.successor.setup.retained.outputs*a.successor.setup.placement.shapes)→Fin a.successor.setup.placement.oldHosts→
      Fin (a.successor.setup.placement.groups*a.successor.setup.placement.blocks)→Cell a.successor.setup.retained.bits)
    (signed : Fin a.successor.setup.strip→Fin a.successor.setup.placement.oldHosts→Fin (a.successor.setup.placement.groups*a.successor.setup.placement.blocks)→Cell a.successor.setup.signedBits)
local notation "final" => ((C).code base w s f).image m
local notation "placed_" => ((C).sources base w s).image m
variable (block : Fin a.successor.setup.placement.blocks) (arg : Fin a.successor.setup.retained.args) (node : Fin a.successor.setup.retained.nodes)
    (old : Fin a.successor.setup.inputs→Expr) (rotor : Fin 4→Expr) (surface : Fin a.successor.setup.fallbackInputs→Expr)
    (digit : Fin 3)
local notation "field" => DescentRetainedRangeDigits.page digit
local notation "j" => (C).retained.outputID 1 field arg node
local notation "mouth" => (finProdFinEquiv (arg,node) : Fin (cfg).mouths)
variable (data : Fin a.successor.setup.placement.newHosts→Fin a.successor.setup.placement.groups→(publicOperands z roots menu.payload).Data a.successor.middle.rotorBits)
local notation "public_" h:arg g:arg => (cfg).column z.board (C).fieldBits (some field) mouth (data h g)
local notation "private_" h:arg g:arg => ((cfg).rotor.flatReg z.board (cfg).multiplicity (cfg).grain
  (cfg).split node.val arg.val (field).succ ((cfg).reg (data h g)) : Cell (C).fieldBits)
variable (blank : ∀h g,((publicOperands z roots menu.payload).oldConfig.header ((publicOperands z roots menu.payload).basic (data h g)) 0).val=0 → ((publicOperands z roots menu.payload).reg (data h g) 1).val=0)
    (physical : ∀h g,∀hv : h.val<U,((publicOperands z roots menu.payload).oldConfig.header ((publicOperands z roots menu.payload).basic (data h g)) 0).val≠0 →
      ((publicOperands z roots menu.payload).reg (data h g) 3).val=(a.successor.setup.placement.shape (name ⟨h.val,hv⟩)).val)

theorem selected_range_source (ready : (C).Ready s w base) (room : (C).endAddress base<2^w)
    (moved : (C).Moved base s name placed_ tables signed) (primary : s.primary=menu.keep)
    (root : Source (expr f.rotorFields (C).lanes ((C).rotorFields base) (finProdFinEquiv (field,mouth)) rotor)
      (fun h g=>private_ h g) (C).lanes final)
    (tree : Source (expr f.fallbackFields (C).lanes ((C).fallbackFields base) (finProdFinEquiv (field,mouth)) surface)
      (fun h g=>public_ h g) (C).lanes final) :
    Source ((C).selected base f (some field) block arg node old rotor surface)
      (fun h g=>menu.spanValue name tables j block h g (data h g) mouth field (blank h g) (physical h g)) (C).lanes final :=by
  have seen:=(C).oldValue_source base s f m room name tables signed moved ready block arg node field
  rw [primary] at seen
  apply (C).selected_range base f block arg node old rotor surface final digit _ _ _ _ seen root tree
  intro h g
  simp only [spanValue,Equiv.symm_apply_apply]

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI
