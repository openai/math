import OAI.Hierarchy.DescentRetainedTargetPlacement
import OAI.Hierarchy.DescentResetRetainedPlacementTariff
import OAI.Hierarchy.DescentResetStemProjectExprTariff

namespace OAI
/-! # Instruction and hardware invoice for compact reset operand relocation -/
namespace Hierarchy.DescentRetainedTargetPlacement.Chart
open DescentSIMDLookup DescentPackedZip Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open DescentStaticWordColumn (names names_seq)
noncomputable section
variable (v : DescentResetRetainedPlacement.Chart) (b : DescentResetRetainedPlacement.Batch)

def invoice (T : ℕ) :=
  let r:=(route v b 0).size
  let s:=(dir v b 0).size
  let N:=b.fields*v.blocks
  let L:=19+26*24
  v.stemInvoice (expanded v b) T+(4+10*r+7*(15*(r+1)))+(4+10*s+7*(15*(s+1)))+
    (4+N*(4+v.rows*(2*L+4)))+7*(15+N*(11+4*L))

theorem tariff (floor w : ℕ) (keep : Fin v.shapes→Bool) (src : Fin (b.fields*v.shapes)→Expr) (cnt inv : Bank)
    (T : ℕ) (bounded : ∀i,(src i).work≤T) (old : 0<b.inputLanes) (blocks : 0<v.blocks) (lanes : 0<v.lanes) :
    ticks v b floor src cnt inv+7*names (program v b floor w keep src cnt inv)≤ invoice v b T :=by
  have base:=DescentResetStemProjectExpr.tariff floor v.oldHosts v.groups v.blocks b.bits b.inputLanes v.lanes
    w src T bounded old blocks lanes
  change v.projectedTicks (expanded v b) floor src+7*names (v.projectedCode (expanded v b) floor w src)≤v.stemInvoice (expanded v b) T at base
  let terms:=List.ofFn (term v b floor cnt inv)
  let L:=19+26*24
  have work (q : Expr) (inList : q∈terms) : q.work≤L:=by
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp inList
    exact (dir v b floor).load_work cnt inv _
  have clocked:=ProbeStage.Native.columns_clock v.rows (samples v b floor) L terms work
  have named:=ProbeStage.Native.columns_text w v.rows (samples v b floor) L terms work
  change names (ProtocolRAM.program w (ProbeStage.Native.columns v.rows (samples v b floor) terms))≤_ at named
  have size : terms.length=b.fields*v.blocks:=List.length_ofFn
  rw [size] at clocked named
  have nameA:=DescentStaticWordColumn.names_mount w (route v b floor).base (literal v keep) (route v b floor).size
  have nameB:=DescentStaticWordColumn.names_mount w (dir v b floor).first (dir v b floor).literal (dir v b floor).size
  change names ((dir v b floor).setup w)=_ at nameB
  unfold ticks program invoice
  rw [names_seq,names_seq,names_seq,nameA,nameB]
  change _+7*(((_+_)+_)+names (ProtocolRAM.program w (ProbeStage.Native.columns v.rows (samples v b floor) terms)))≤_
  change _≤v.stemInvoice (expanded v b) T+(4+10*(route v b floor).size+7*(15*((route v b floor).size+1)))+
    (4+10*(dir v b floor).size+7*(15*((dir v b floor).size+1)))+
    (4+(b.fields*v.blocks)*(4+v.rows*(2*L+4)))+7*(15+(b.fields*v.blocks)*(11+4*L))
  clear size
  dsimp only [terms] at clocked named ⊢
  omega

end
end Hierarchy.DescentRetainedTargetPlacement.Chart

end OAI
