import OAI.Hierarchy.DescentResetRetainedPlacement
import OAI.Hierarchy.DescentResetStemProjectExprTariff

namespace OAI
/-! # Instruction and hardware invoice for compact reset operand relocation -/
namespace Hierarchy.DescentResetRetainedPlacement.Chart
open DescentSIMDLookup DescentPackedZip Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open DescentStaticWordColumn (names names_seq)
noncomputable section
variable (v : DescentResetRetainedPlacement.Chart) (b : DescentResetRetainedPlacement.Batch)

def stemInvoice (T : ℕ) :=
  4096*DescentResetStemProject.volume b.fields v.oldHosts v.groups v.blocks b.bits b.inputLanes v.lanes+
    (4+b.fields*(4+v.oldHosts*chunks (v.groups*v.blocks) b.inputLanes*(2*T+4)))+
    7*(15+b.fields*(11+4*T))

def invoice (T : ℕ) :=
  let r:=(v.route b 0).size
  let s:=(v.dir b 0).size
  let N:=b.fields*v.blocks
  let L:=19+26*24
  v.stemInvoice b T+(4+10*r+7*(15*(r+1)))+(4+10*s+7*(15*(s+1)))+
    (4+N*(4+v.rows*(2*L+4)))+7*(15+N*(11+4*L))

theorem tariff (floor w : ℕ) (keep : Fin v.shapes→Bool) (src : Fin b.fields→Expr) (cnt inv : Bank)
    (T : ℕ) (bounded : ∀i,(src i).work≤T) (old : 0<b.inputLanes) (blocks : 0<v.blocks) (lanes : 0<v.lanes) :
    v.ticks b floor src cnt inv+7*names (v.code b floor w keep src cnt inv)≤v.invoice b T :=by
  have base:=DescentResetStemProjectExpr.tariff floor v.oldHosts v.groups v.blocks b.bits b.inputLanes v.lanes
    w src T bounded old blocks lanes
  change v.projectedTicks b floor src+7*names (v.projectedCode b floor w src)≤v.stemInvoice b T at base
  let terms:=List.ofFn (v.term b floor cnt inv)
  let L:=19+26*24
  have work (q : Expr) (inList : q∈terms) : q.work≤L:=by
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp inList
    exact (v.dir b floor).load_work cnt inv _
  have clocked:=ProbeStage.Native.columns_clock v.rows (v.samples b floor) L terms work
  have named:=ProbeStage.Native.columns_text w v.rows (v.samples b floor) L terms work
  change names (ProtocolRAM.program w (ProbeStage.Native.columns v.rows (v.samples b floor) terms))≤_ at named
  have size : terms.length=b.fields*v.blocks:=List.length_ofFn
  rw [size] at clocked named
  have nameA:=DescentStaticWordColumn.names_mount w (v.projected b floor) (v.literal keep) (v.route b floor).size
  have nameB:=DescentStaticWordColumn.names_mount w (v.dir b floor).first (v.dir b floor).literal (v.dir b floor).size
  change names ((v.dir b floor).setup w)=_ at nameB
  unfold ticks code invoice
  rw [names_seq,names_seq,names_seq,nameA,nameB]
  change _+7*(((_+_)+_)+names (ProtocolRAM.program w (ProbeStage.Native.columns v.rows (v.samples b floor) terms)))≤_
  change _≤v.stemInvoice b T+(4+10*(v.route b floor).size+7*(15*((v.route b floor).size+1)))+
    (4+10*(v.dir b floor).size+7*(15*((v.dir b floor).size+1)))+
    (4+(b.fields*v.blocks)*(4+v.rows*(2*L+4)))+7*(15+(b.fields*v.blocks)*(11+4*L))
  clear size
  dsimp only [terms] at clocked named ⊢
  omega

end
end Hierarchy.DescentResetRetainedPlacement.Chart

end OAI
