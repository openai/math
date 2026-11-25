import OAI.Hierarchy.TaggedWirePacketMiddleColumns
import OAI.Hierarchy.ProbeFixedWideBallotFields
import OAI.Hierarchy.TaggedWidePlacement
import OAI.Hierarchy.TaggedWideOriginalRoleShelf
import OAI.Hierarchy.TaggedWireRoleIndices
import OAI.Hierarchy.TaggedWireRolePageCore

namespace OAI
/-! # Exact dated column counts for the two physical packet geometries -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage CoreBoard ProtocolRAM.StripDirectory Strip
open HistoryRoles RoleProgram WideCPU
open scoped Classical
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (h width : ℕ)
local notation "N" => Stages h (2^v.W)
local notation "P" => v.widePlacement h width

def widePacketRoles := max (Fintype.card (PayloadRole N k⊕TreeLink (PayloadStrip.edgeCount N) k))
  (Fintype.card (PurchasedRole v.depth k⊕TreeLink (ChainStrip.edgeCount v.depth) k))

def widePacketDegree := HistoryRoles.stride k v.sampler.degree v.wideJobs

def widePacketShape : Event→WideCPU.Shape
  | .attempt a=>
    let old:=v.wideBallotShape P h width (.attempt a)
    ⟨old.candidates,old.parties,old.columns+((v.widePacketRoles h*3)*5+(v.widePacketDegree+v.widePacketDegree))+old.parties+WireTelescope.PacketTurns.middleColumns (v.widePacketRoles h)⟩
  | .feed _=>⟨0,0,0⟩

/-- Start of the two actual released and installed width banks in a ballot row. -/
def widePacketLowStart : Event→ℕ
  | .attempt a=>(v.wideBallotShape P h width (.attempt a)).columns+(v.widePacketRoles h*3)*5
  | .feed _=>0

def widePacketLowColumn (a : Attempt) (side : Bool) (q : Fin v.widePacketDegree) :
    Fin (v.widePacketShape h width (.attempt a)).columns :=
  ⟨v.widePacketLowStart h width (.attempt a)+side.toNat*v.widePacketDegree+q.val,by
    have lt:=q.isLt
    cases side <;> simp only [widePacketShape,widePacketLowStart,Bool.toNat_false,Bool.toNat_true,
      Nat.zero_mul,Nat.one_mul] <;> omega⟩

@[simp] theorem widePacket_low_column (a : Attempt) (side : Bool) (q : Fin v.widePacketDegree) :
    (v.widePacketLowColumn h width a side q).val=v.widePacketLowStart h width (.attempt a)+side.toNat*v.widePacketDegree+q.val := rfl

theorem widePacket_low_extent (a : Attempt) : v.widePacketLowStart h width (.attempt a)+2*v.widePacketDegree≤
    (v.widePacketShape h width (.attempt a)).columns := by
  simp only [widePacketLowStart,widePacketShape]
  omega

def widePacketPhysical := Fintype.card (RoleProgram.Old h v.W k (P).catalogue.rows)
def widePacketShelf := (siteLast h (2^v.W) k+1)*v.widePacketDegree


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
