import OAI.Hierarchy.TaggedWideCalendarOuterRead
import OAI.Hierarchy.TaggedWirePacketNeighborSlots
import OAI.Hierarchy.TaggedWidePassApertures

namespace OAI
/-! # Reading a complete carried role bank from the original dated state -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.LedgerStep
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing Diagonal TraceWords
open Tagged Tagged.WideStack Tagged.WideControlJoin WireTelescope WireTelescope.CalendarTape
open ProtocolRAM.Calendar Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
set_option quotPrecheck false

variable {X R D Ex Se : Type} [Fintype R] [Fintype D] [Fintype Ex] [Fintype Se] {K degree cap : ℕ}
    (slot : Event→Slot X) (shape : X→Widths K) (es : List Event) (start : X) (path : Path slot es start)
    (room : R→ℕ) (socket : R↪Fin (K*degree))
    (cells : ∀x,(Σs,SiteBit (shape x) s)↪((r:R)×Fin (room r)))
    (z : SiteChoices slot shape es start path)
local notation "allBits" => placedBits slot shape es start path (timelineFin slot shape cells es start path) z
variable (wire : Fin ((es.length+1)*Fintype.card ((r:R)×Fin (room r)))→D) (j : Fin es.length) (s : Fin K) (side : Bool)
local notation "date" => if side then j.succ else j.castSucc
local notation "state" => datedState slot shape s es start path date (z s)
variable (G : Gate) (ex : Ex→Bool) (sel : Se→Bool) (data : D→Bool) (out : Memory G.W)
local notation "seen" => Sum.elim ex (Sum.elim sel (Sum.elim data (G.terminal out)))
local notation "words" => outerWord G es room socket wire j s side


open PassiveWindow
variable {n : ℕ} (ends : Fin n→Chord K) (qty : Fin n→ℕ) (port : Fin n×Bool↪R)
    (fit : ∀i b,qty i≤room (port (i,b))) (capFit : ∀i,qty i≤cap)
    (here : ∀i b,(finProdFinEquiv.symm (socket (port (i,b)))).1=(portGraph K).vertex (ends i) b)
    (shapeAt : AdaptiveProbe.installedWidths ends qty=shape (boundaryState slot es start path (if side then j.succ else j.castSucc)))
    (numbered : cells (boundaryState slot es start path (if side then j.succ else j.castSucc))=(NamedAperture.transport shapeAt).symm.toEmbedding.trans
      (NamedAperture.place ends qty port room fit))
local notation "atSlot" => PacketNeighbor.localSlot ends qty port socket here s
include fit numbered in
omit [Fintype D] [Fintype Ex] [Fintype Se] in
/-- Every occupied input of the physical local gather reads the live digit
at the correct preceding-row prefix, also when two rows have identical ends. -/
theorem outer_carried_read {total : Widths K} (actual : AdaptiveProbe.installedWidths ends qty=total)
    (history : ∀a,data (wire a)=allBits a) :
    let parts:=carried ends qty s capFit atSlot actual
    let x:=cast (congrArg (fun U=>State U s) (shapeAt.symm.trans actual)) state
    ∀i p,parts.owner i=some p→∀u:Fin (parts.width i),
      Sum.elim seen id (words i (u.castLE (parts.within i)))=(x p).val.testBit (parts.base i+u.val) := by
  subst total
  intro parts x
  apply carried_reads ends qty s capFit atSlot rfl x (fun q j=>Sum.elim seen id (words q j))
  intro a u
  let pp : (bitGraph (rowGraph ends) qty).Port s:=⟨(⟨a.val.val.1,u⟩,a.val.val.2),a.val.property⟩
  have seenAt:=outer_original_row slot shape es start path room socket cells z wire j s side G ex sel data out
    ends qty port fit shapeAt numbered history pp (atSlot a) (PacketNeighbor.local_addr ends qty port socket here s a)
    (u.isLt.trans_le (capFit _))
  exact seenAt.trans (NamedAperture.rowBit_prefix ends qty x pp).symm

end Hierarchy.ProbeStage.CoreBoard.LedgerStep
end

end OAI
