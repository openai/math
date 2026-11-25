import OAI.Hierarchy.DescentResetConvertedOld
import OAI.Hierarchy.DescentRetainedOperandDateTables

namespace OAI
/-! Native donor and signed operands of the retained lookup on the reset's completed setup memory. -/
namespace Hierarchy.DescentResetOperandSetup.Chart
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOperandFamilyBook
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (C : DescentResetOperandSetup.Chart)
variable {w : ℕ} (base : ℕ) (s : C.Sources) (laws : C.Laws) (m : Memory w)
local notation "p" => (C.sources base w s).image m
local notation "dst" => (C.code base w s laws).image m
local notation "Vals" b => (Fin C.placement.newHosts→Fin C.placement.groups→Cell b)
variable (space : C.endAddress base<2^w) (ready : C.Ready s w base)

include space ready in
private theorem convert_at_width (i : Fin C.inputs) {bits : ℕ} (width : C.width i=bits)
    (src : Expr) (R : Vals bits) (fit : src.Fits w (C.placed base))
    (seen : Source src R C.lanes p) :
    Source (C.converted base i src) (fun h g=>(R h g).val : Vals C.fieldBits) C.lanes dst:=by
  subst bits
  exact C.converted_moved base s laws m space ready i src R fit seen

variable {U : ℕ} (name : Fin U→Fin C.placement.sparse)
    (Y : Fin (C.retained.outputs*C.placement.shapes)→Fin C.placement.oldHosts→
      Fin (C.placement.groups*C.placement.blocks)→Cell C.retained.bits)
    (signed : Fin C.strip→Fin C.placement.oldHosts→Fin (C.placement.groups*C.placement.blocks)→Cell C.signedBits)
variable (x : Fin C.placement.blocks) (a : Fin C.retained.args) (n : Fin C.retained.nodes)
variable (hub : Fin C.placement.newHosts→Fin C.placement.groups→Cell C.fieldBits)
    (fee : Fin C.strip→Fin C.placement.newHosts→Fin C.placement.groups→Cell C.fieldBits)

private theorem port_bound {i strip : ℕ} (first : ¬i<4) (fourth : i≠4) (fifth : i≠5)
    (signed : i<6+strip) : i-6<strip := by omega

private theorem fee_bound {i strip : ℕ} (high : i<6+2*strip) (later : ¬i<6+strip) :
    i-(6+strip)<strip := by omega

/-- Host and ticket fields are already widened before the retained search. The signed donor sheet
and both old operand headers share the original selected compact host and output block. -/
def carriedRow (h : Fin C.placement.newHosts) (g : Fin C.placement.groups) (i : Fin C.inputs) : Cell C.fieldBits :=
  if lt4:i.val<4 then
    (DescentRetainedTargetPlacement.Chart.compact C.placement C.seven.batch s.primary name Y
      (C.retained.outputID 0 ⟨i.val,lt4.trans_le (by decide : 4≤7)⟩ a n) x h g).val
  else if fourth : i.val=4 then
    (DescentRetainedTargetPlacement.Chart.compact C.placement C.seven.batch s.primary name Y
      (C.retained.donorID n) x h g).val
  else if fifth : i.val=5 then hub h g
  else if signedAt:i.val<6+C.strip then
    (C.placement.compact C.signedFields (fun _=>true) name signed
      ⟨i.val-6,port_bound lt4 fourth fifth signedAt⟩ x h g).val
  else fee ⟨i.val-(6+C.strip),fee_bound i.isLt signedAt⟩ h g

variable (moved : C.Moved base s name ((C.sources base w s).image m) Y signed) (mark : Expr) (ticket : Fin C.strip→Expr)
variable (markRead : Source mark hub C.lanes ((C.code base w s laws).image m))
    (feeRead : ∀j,Source (ticket j) (fee j) C.lanes ((C.code base w s laws).image m))
include space ready moved markRead feeRead in
theorem carried_source (i : Fin C.inputs) :
    Source (C.carried base x a n mark ticket i)
      (fun h g=>C.carriedRow s name Y signed x a n hub fee h g i) C.lanes dst:=by
  have lim:C.placed base≤C.endAddress base:=
    ((C.packets.join _).1.trans (C.packets.join _).2).trans
      ((show C.packetEnd base≤C.publicEnd base from Nat.le_add_right ..).trans (C.public_snapshots base s laws m ready space).2.1)
  have oldFit (j : Fin C.retained.outputs) : (C.oldField base x j).Fits w (C.placed base):=by
    have z:=DescentRetainedTargetPlacement.Chart.validBank C.placement C.seven.batch
      (C.seven.place base) (((C.before base).2.2.trans lim).trans_lt space) j x
    exact ⟨⟨z.1.1,z.1.2.1,z.1.2.2.trans (C.before base).2.2⟩,trivial⟩
  have portFit (j : Fin C.strip) : (C.portField base x j).Fits w (C.placed base):=by
    have z:=C.placement.validBank C.signedFields (C.placedSigned base) (lim.trans_lt space) j x
    exact ⟨z.1,trivial⟩
  by_cases first:i.val<4
  · simpa only [carried,carriedRow,dite_eq_left first] using
      C.convert_at_width base s laws m space ready i (bits:=C.retained.bits)
        (by simp [width,show i.val<5 by omega]) _ _ (oldFit _) (moved.retained _ x)
  by_cases fourth:i.val=4
  · simpa only [carried,carriedRow,dite_eq_right first,dite_eq_left fourth] using
      C.convert_at_width base s laws m space ready i (bits:=C.retained.bits)
        (by simp [width,show i.val<5 by omega]) _ _ (oldFit _) (moved.retained _ x)
  by_cases fifth:i.val=5
  · simpa only [carried,carriedRow,dite_eq_right first,dite_eq_right fourth,dite_eq_left fifth] using markRead
  by_cases slot:i.val<6+C.strip
  · let j : Fin C.strip := ⟨i.val-6,port_bound first fourth fifth slot⟩
    simp only [carried,carriedRow,dite_eq_right first,dite_eq_right fourth,dite_eq_right fifth,dite_eq_left slot]
    exact C.convert_at_width base s laws m space ready i (bits:=C.signedBits)
        (by simp [width,show ¬i.val<5 by omega,fifth,slot]) _ _ (portFit j) (moved.panel j x)
  · simpa only [carried,carriedRow,dite_eq_right first,dite_eq_right fourth,dite_eq_right fifth,dite_eq_right slot] using feeRead _

end
end Hierarchy.DescentResetOperandSetup.Chart

end OAI
