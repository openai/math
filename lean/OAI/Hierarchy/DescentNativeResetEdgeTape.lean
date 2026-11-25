import OAI.Hierarchy.DescentResetCableSlots
import OAI.Hierarchy.DescentDenseHostTape
import OAI.Hierarchy.DescentOrderedReentry

namespace OAI
/-! # Emitting dense chronological IDs for the genuine ordered reset graph -/

namespace Hierarchy.DescentSixParty.ResetInput
open DescentResetTrunks DescentOrderedReset DescentCableUnbundling DescentStageEdgeReceipt
open ThreeFlat.RAM Computability.VPVNP.BurstRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} {h C Ht : ℕ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z)
variable {U N : ℕ} (vertex : Z.V↪Fin U) (key : A.graph.Edge↪Fin N)
local notation "W" => reenter Z T
local notation "cnt" => (fun e => Computability.BorderVNP.Crossing.Network.width (World.graph (MarkedWorld.toWorld W)) e / Z.unit)
local notation "Y" => (2^Z.n:ℕ)
local notation "baseSlots" => (U*2^Z.k)
local notation "termSlots" => (U*(2^(Z.k+1)*(Y+1)))
local notation "ports" => (baseSlots*Y+termSlots*2^Ht)
local notation "inside" => ((2*(baseSlots+termSlots))*max (Fintype.card (Computability.BorderVNP.Crossing.Network.Edge (DescentCommonPalette.rotor Z.graph))) (2^(Ht+1)))
local notation "slotCount" => (2*N+(termSlots+(ports+inside)))

def installedResetOrdinal : (W).graph.Edge↪Fin slotCount :=
  (installedWireNames A T.home Z.placement.input T.hub
    (funext fun e => (Z.allWidths e).symm) Z.bank Z.tables).toEmbedding.trans
    (DescentResetCableSlots.complete Z.placement vertex T.code (fun t=>(T.codeLegal t).2)
      Ht T.bookHeight Z.graph Z.positive Z.pay Z.circuit d key)

local notation "parentRank" => Function.Embedding.trans (installedResetOrdinal Z T vertex key) DescentResetWireTags.digit
local notation "part" => pieceUnit (World.graph (MarkedWorld.toWorld W)) (MarkedWorld.core W) cnt Z.unit

def nativeResetEdges : Tape (orderedOrdinary Z T key).graph.Edge where
  Parent:=(W).graph.Edge
  order:=(chronological (W).graph (W).core cnt Z.unit parentRank (parentRank).injective).toEmbedding
  slots:=slotCount
  rank:=parentRank
  inSlots e:=(installedResetOrdinal Z T vertex key e).isLt
  span:=DescentCableUnbundling.span (W).graph (W).core cnt
  owner e:=(part e).1
  offset e:=(part e).2.val
  offsetFits e:=(part e).2.isLt
  read e:=chronological_read (W).graph (W).core cnt Z.unit parentRank (parentRank).injective e

theorem nativeResetEdges_read {w counts starts : ℕ} (memory : Memory w)
    (sep : counts+slotCount≤ starts) (fits : starts+slotCount+1<2^w)
    (loaded : ∀i<slotCount,memory (counts+i)=(DescentEdgeTapePrefix.row (DescentCableUnbundling.span (W).graph (W).core cnt) parentRank i:Word w)) :
    let t:=nativeResetEdges Z T vertex key
    let out:=ProtocolRAMEndpointPrefix.image starts (DescentEdgeTapePrefix.before t.span t.rank) memory t.slots
    (ProtocolRAMEndpointPrefix.exclusive w counts starts t.slots).Exec memory out (10+(3+12*t.slots)) ∧
      ∀e,out (starts+(installedResetOrdinal Z T vertex key (part e).1).val)+((part e).2.val:Word w)=((t.order e).val:Word w) :=
  (nativeResetEdges Z T vertex key).native memory sep fits loaded

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
