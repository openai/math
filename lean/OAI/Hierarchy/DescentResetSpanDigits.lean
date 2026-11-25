import OAI.Hierarchy.DescentResetSpanDispatch
import OAI.Hierarchy.DescentResetRetainedCableValue
import OAI.Hierarchy.DescentRangePage

namespace OAI
/-! # Normalization of an actual paid operand field at a registered range address -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu
open DescentSIMDLookup DescentDenseHostOrder DescentResetOperandSetup DescentResetPublicOperandBook
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {z : a.Atlas} {roots : a.RootInputs} (menu : OperandMenu z roots)
local notation "C" => a.successor.setup
local notation "r" => a.successor.middle.rootDepth
local notation "cfg" => publicOperands z roots menu.payload
variable {U : ℕ} (name : Fin U→Fin a.successor.setup.placement.sparse)
variable (Y : Fin (a.successor.setup.retained.outputs*a.successor.setup.placement.shapes)→Fin a.successor.setup.placement.oldHosts→
    Fin (a.successor.setup.placement.groups*a.successor.setup.placement.blocks)→Cell a.successor.setup.retained.bits)
variable (j : Fin a.successor.setup.retained.outputs) (block : Fin a.successor.setup.placement.blocks)
variable (host : Fin a.successor.setup.placement.newHosts) (g : Fin a.successor.setup.placement.groups)
local notation "table" => DescentRetainedTargetPlacement.Chart.compact (C).placement (C).seven.batch
  menu.keep name Y j block
local notation "ret" => (((table) host g).val : Cell (C).fieldBits)
variable (x : (publicOperands z roots menu.payload).Data a.successor.middle.rotorBits) (arg : Fin (publicOperands z roots menu.payload).args) (node : Fin (publicOperands z roots menu.payload).nodes)
local notation "index" => (finProdFinEquiv (arg,node) : Fin (cfg).mouths)
local notation "f_" f:arg => DescentRetainedRangeDigits.page f
local notation "private_" f:arg => ((cfg).rotor.flatReg z.board (cfg).multiplicity (cfg).grain (cfg).split
    node.val arg.val (f_ f).succ ((cfg).reg x) : Cell (C).fieldBits)
local notation "public_" f:arg => (cfg).column z.board (C).fieldBits (some (f_ f)) index x
variable (blank : ((publicOperands z roots menu.payload).oldConfig.header ((publicOperands z roots menu.payload).basic x) 0).val=0 → ((publicOperands z roots menu.payload).reg x 1).val=0)
variable (physical : ∀hv : host.val<U,((publicOperands z roots menu.payload).oldConfig.header ((publicOperands z roots menu.payload).basic x) 0).val≠0 →
    ((publicOperands z roots menu.payload).reg x 3).val=(a.successor.setup.placement.shape (name ⟨host.val,hv⟩)).val)

theorem issued_range_digit (row : (C).cable.Input) (f : Fin 3) :
    (((ret).val+((C).cable.priceField (f_ f) row).val+(private_ f).val+(public_ f).val : ℕ) : Cell (C).fieldBits)=
      menu.spanValue name Y j block host g x index (f_ f) blank physical := by
  have free : (C).cable.priceField (f_ f) row=0:=by
    fin_cases f <;> rfl
  have amount : (ret).val+(private_ f).val+(public_ f).val =
      (menu.spanValue name Y j block host g x index (f_ f) blank physical).val := by
    simp only [spanValue, Equiv.symm_apply_apply]
  have room := amount.trans_lt (menu.spanValue name Y j block host g x index (f_ f) blank physical).isLt
  rw [free, Fin.val_zero, Nat.add_zero]
  exact Fin.ext ((Fin.val_cast_of_lt room).trans amount)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI
