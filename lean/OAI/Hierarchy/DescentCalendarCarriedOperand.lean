import OAI.Hierarchy.DescentCalendarLiveOperandQuery
import OAI.Hierarchy.DescentRetainedOriginalUnit

namespace OAI
/-! A four-register old cable resolves to its unique true successor grain and authentic field word. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentStageEdgeReceipt
open DescentParallelBase DescentResetSignedScan DescentNextSignedWindow DescentCableDonorNames
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
open scoped Fin.CommRing
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "cnt" => fun e=>(coarse).graph.width e/(Z).unit
local notation "world" => (Z).orderedOrdinary T birth
local notation "tape" => (Z).nativeResetEdges T vertexCode birth
local notation "index" => (tape).order.trans Fin.valEmbedding
local notation "dense" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding
local notation "groups" => S.groupCount (i+1)
local notation "rawSite" => B.raw.siteFrom (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=groups)) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "sparse" => DescentResetLocalOrder.allCode B.raw index S B.valid rawSite
local notation "renameEdge" => DescentPhysicalOrder.rename sparse
local notation "next" => B.reblock.result
local notation "A" => B.next.placement
local notation "ord" => B.next.order.trans Fin.valEmbedding
local notation "stream'" => Stage.stream A ord
local notation "board" => Stage.source A ord
local notation "wt" => weight B
local notation "grains" => emit B
local notation "piece'" => piece B
local notation "base'" => first B


open scoped BigOperators
open DescentNextSignedWindow
local notation "C₀" => blocks B
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "live" => fun e : (coarse).graph.Edge=>e∈(coarse).core
local notation "fit" => Stage.measured A ord S B.next.valid
variable (names : Stage.Host (Fin (S.groupCount (i+1))) B.next.V k ↪ ℕ)

open DescentNextSignedWindow.Native
open DescentDatedAddressBook.ResetOutput DescentSIMDLookup DescentOperandStateBanks
open DescentResetOperandComponents DescentResetOperandSlices
set_option quotPrecheck false
local notation "unitAt" host => GrainPorts.Unit A ord C₀ host
local notation "faceAt" host:max u:max => Roster.face A ord C₀ host u
local notation "peerAt" host:max u:max => DescentResetWindowFields.neighbor A ord S B.next.valid names C₀ host (faceAt host u)
local notation "liveAt" host:max u:max => Stage.live A ord S B.next.valid names host (GrainPorts.port A ord C₀ host u)


open DescentIssuedFallbackPanel DescentOperandCandidateLookup
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "before" => input.order.trans Fin.valEmbedding
local notation "digitsIn" => S.resetInputDigits ctl.base ctl.radix i
local notation "addr" j => localAddress (c:=(T).commonDepth) input.placement before S input.valid digitsIn B.frame.basis false (beforeStem B j)


local notation "oldHost" side:max edge:max => (blocks B).src (carriedParent B side edge)
local notation "actual" side:max edge:max => carriedUnit B side edge
local notation "land" edge => (T).home ((old).graph.dst edge)

theorem carried_operand_query (edge : (old).graph.Edge)
    (shape : DescentResetRetainedCableLaw.Shape) (x : shape.Input) (donor : shape.Donor)
    (side : Bool) (slot : shape.Slot) (foundAt : shape.found x=some (donor,side,slot))
    (cap : shape.cap=input.placement.cap)
    (donors : shape.donors=2^((S.groupWidth k tail i+k)-(T).commonDepth))
    (lo : side=false → donor.val=(addr edge).1.val) (localSlot : side=false → slot.val=(addr edge).2.val)
    (room : 2*totalLocal B<2^shape.queryBits) :
    shape.query x=code room (some (grainSlot B (oldHost side edge) (actual side edge))) := by
  cases side
  · exact outgoing_operand_query B _ _ edge rfl rfl shape x donor slot foundAt cap (lo rfl) (localSlot rfl) room
  · exact incoming_operand_query B _ _ (land edge) rfl rfl shape x donor slot foundAt cap donors room

theorem carried_operand_value (edge : (old).graph.Edge)
    (shape : DescentResetRetainedCableLaw.Shape) (x : shape.Input) (donor : shape.Donor)
    (side : Bool) (slot : shape.Slot) (foundAt : shape.found x=some (donor,side,slot))
    (tag : (shape.header x 0).val=1) (pos : 0<shape.units)
    (ticket : side=true→shape.ticket x donor slot=earlierIncoming B edge)
    (hub : side=true→decide ((shape.hubCell x).val=1)=(T).hub (land edge))
    (small : shape.oldIndex x donor side slot<2^shape.fieldBits)
    {labelBits : ℕ} (earlier : Field→Cell shape.fieldBits) (label : Cell labelBits)
    (span : Span) (prevPeer prevSerial prevChunk signed coeff : ℕ)
    (archive : ∀f,(earlier f).val=(Pointer.cable prevPeer prevSerial prevChunk).fields span f)
    (width : max ((A).degree+1) ((A).cap+1)≤2^signed) (f : Field) :
    let u:=actual side edge
    let baseHost:=oldHost side edge
    let r:=grainRecord B names baseHost u
    let child:=liveAt baseHost u
    let target:=(Pointer.cable child.neighbor.val (child.wire.val-child.within.val)
      (if r.marked then shape.oldIndex x donor side slot%shape.units else shape.oldIndex x donor side slot)).fields span f
    target<2^coeff →
    (((DescentResetRetainedPages.kept f (earlier 0) (earlier f) label).val+
      (shape.priceField f x).val : ℕ):Cell coeff).val+
      (nativeCandidateField signed coeff f (candidateRows B names baseHost (grainSlot B baseHost u))).val=target := by
  obtain ⟨offset,marked⟩:=carried_unit_read B names shape x donor side slot edge pos ticket hub
  exact live_operand_field B names _ (actual side edge) shape x donor side slot foundAt tag pos small
    offset earlier label span prevPeer prevSerial prevChunk signed coeff archive marked width f

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
