import OAI.Hierarchy.DescentDeclaredOperandEntry
import OAI.Hierarchy.DescentPhysicalIssuedOperandColumns

namespace OAI
/-! Posted menu slots and the seven-component node ledger use the same public ordinal. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open ProtocolRAM DescentPackedZip DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
set_option quotPrecheck false
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "C" => (v).setup
local notation "base" => (v).operandFloor b
local notation "ctrl" => (v).controlRegisters
local notation "actor" => (v).actor
local notation "origin" => (v).middle.stop b
local notation "start" => (v).controlFloor b
variable (f : Fin 7) (arg : Fin a.successor.setup.retained.args) (x : Fin a.successor.receiver.blocks) (n : Fin a.successor.setup.retained.nodes)
local notation "i" => (v).operandOrdinal u.operand f arg x n
local notation "slot" => x.cast u.operandBlocks
local notation "reg" => (ctrl).ports start (a.c/2) (slot).val ((actor).directory origin).inverse
  ((actor).depths origin) ((actor).levels origin)
local notation "pub" => u.menu.publicInput u.shape floor u.count u.hub u.g u.Y ((ctrl).live start (slot).val) reg (slot).val
local notation "old" => (C).carried base slot arg n ((v).retainedHub b slot) ((v).retainedTicket b slot)
local notation "src" mode:arg => (C).selected base u.laws mode slot arg n old reg pub

theorem raw_ordinal_fields :
    u.rawOperands.query i=src none ∧ u.rawOperands.kept i=src (some f):=by
  dsimp only [rawOperands, operand, OperandMenu.renderer, ResetOutput.operandOrdinal, ResetOutput.operandOrder]
  simp only [Equiv.symm_apply_apply]
  exact ⟨rfl, rfl⟩

theorem operand_ordinal_fields {H G : ℕ} (ok : u.Ready) (m : Memory w)
    (q : Fin H→Fin G→Cell (v).receiver.queryBits) (raw : Fin H→Fin G→Cell (C).fieldBits)
    (qfit : (u.rawOperands.query i).Fits w ((v).keepBase b))
    (kfit : (u.rawOperands.kept i).Fits w ((v).keepBase b))
    (found : Source (src none) q (v).receiver.lanes (((C).code base w u.bank u.laws).image (u.beforeSetupImage ok m)))
    (values : Source (src (some f)) raw (v).receiver.lanes (((C).code base w u.bank u.laws).image (u.beforeSetupImage ok m))) :
    Source (u.operand.query i) q (v).receiver.lanes (u.operandEntry ok m) ∧
    Source (u.operand.kept i) (fun h g=>(raw h g).val:Fin H→Fin G→Cell (v).receiver.valueBits)
      (v).receiver.lanes (u.operandEntry ok m):=by
  have index:=u.raw_ordinal_fields f arg x n
  rw [←index.1] at found
  rw [←index.2] at values
  have order:=(v).operand_order b
  have high:=((order.1.trans order.2).trans ((v).final_ge b)).trans_lt ok.full
  have installed:=(v).keep_any b (((C).code base w u.bank u.laws).image (u.beforeSetupImage ok m)) high
  refine ⟨fun t=>?_,u.kept_entry ok m i raw kfit values⟩
  exact (eval_below (u.rawOperands.query i) _ _ _ qfit (fun j hj=>installed.frame j (.inl hj))).trans (found t)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
