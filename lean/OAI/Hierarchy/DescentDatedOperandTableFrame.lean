import OAI.Hierarchy.DescentDatedPacketSnapshot

namespace OAI
/-! # The original reset's final node-field publisher preserves the installed operand menus -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs
open DescentPackedZip DescentSIMDLookup ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "base" => (v).operandFloor b
local notation "chart" => (v).setup

theorem emitted_sheets_kept (ok : u.Ready) (atActors : Memory w) :
    ∀z,z<(v).operandStart b→u.sheetsResult ok atActors z=
      ((v).keepBook b w).image (((chart).code base w u.bank u.laws).image (u.beforeSetupImage ok atActors)) z :=by
  let native:=((chart).code base w u.bank u.laws).image (u.beforeSetupImage ok atActors)
  let printed:=((v).keepBook b w).image native
  let r:=(v).renderFromRanks ((v).linkedRankInputs u.sectors ((v).sheetsStart b)) b
  have widths : (v).receiver.fields=(v).nodeNames*(v).nodes:=by
    simpa only [ok.nodes,ok.slots,ResetOutput.nodeNames] using u.operand.channels
  have prior : (v).operandDictionaryEnd b+((v).nodeNames*(v).nodes)*
      DescentResetNodeBooks.rows (v).receiver.hosts (v).receiver.groups (v).receiver.lanes≤(v).scalarEnd b:=by
    change (v).operandDictionaryEnd b+_≤(v).operandDictionaryEnd b+(v).receiver.fields*_
    rw [widths]
    rfl
  have early:=(v).operand_order b
  have body:=(v).operand_any u.operand r b printed ok.fields (((v).final_ge b).trans_lt ok.full)
  have nodes:=DescentResetNodeBooks.any ((v).scalarEnd b) ((v).operandDictionaryEnd b) (v).nodeNames
    (v).nodes (v).receiver.hosts (v).receiver.groups (v).nodeBits (v).receiver.lanes
    ((v).operandMemory u.operand r b printed) prior ok.full
  intro z hz
  exact (nodes.2 z (.inl (hz.trans_le (early.1.trans early.2)))).trans (body.2.1 z (.inl hz))

theorem operand_pages_kept (ok : u.Ready) (atActors : Memory w) :
    ∀z,z<(chart).endAddress base→u.sheetsResult ok atActors z=
      ((chart).code base w u.bank u.laws).image (u.beforeSetupImage ok atActors) z :=by
  have order:=(v).operand_order b
  have bound:=((order.1.trans order.2).trans ((v).final_ge b)).trans_lt ok.full
  let native:=((chart).code base w u.bank u.laws).image (u.beforeSetupImage ok atActors)
  have cast:=(v).keep_any b native bound
  intro z hz
  exact (u.emitted_sheets_kept ok atActors z (hz.trans_le ((v).keep_before b))).trans (cast.frame z (.inl hz))

theorem kept_posted (ok : u.Ready) (atActors : Memory w) (i : Fin (v).receiver.fields)
    {H G : ℕ} (values : Fin H→Fin G→Cell (chart).fieldBits)
    (fit : (u.rawOperands.kept i).Fits w ((v).keepBase b))
    (seen : Source (u.rawOperands.kept i) values (v).receiver.lanes
       (((chart).code base w u.bank u.laws).image (u.beforeSetupImage ok atActors))) :
    Source (u.operand.kept i) (fun h g=>(values h g).val : Fin H→Fin G→Cell (v).receiver.valueBits)
      (v).receiver.lanes (u.sheetsResult ok atActors) :=by
  have order:=(v).operand_order b
  have room:=((order.1.trans order.2).trans ((v).final_ge b)).trans_lt ok.full
  have cast:=(v).keptValue_source b _ _ values fit seen room
  have small:=(v).keptValue_fits b _ fit room
  intro p
  exact (eval_below _ _ _ _ small (u.emitted_sheets_kept ok atActors)).trans (cast p)

/-- Any of the protected bank expressions can be evaluated after the final node copies. -/
theorem operand_page_source (ok : u.Ready) (atActors : Memory w) {H G bits : ℕ} (e : Expr)
    (values : Fin H→Fin G→Cell bits) (lanes : ℕ) (fit : e.Fits w ((chart).endAddress base))
    (seen : Source e values lanes (((chart).code base w u.bank u.laws).image (u.beforeSetupImage ok atActors))) :
    Source e values lanes (u.sheetsResult ok atActors) :=fun q=>
      (eval_below e _ _ _ fit (u.operand_pages_kept ok atActors)).trans (seen q)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.DateInputs

end OAI
