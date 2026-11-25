import OAI.Hierarchy.DescentResetNativeWindows
import OAI.Hierarchy.DescentDatedResetOperands
import OAI.Hierarchy.DescentResetRetainedCableValue

namespace OAI
/-! Native tag, peer, and serial at the candidate of an actual oriented output grain.
The row is read through both the signed word and the destination coefficient word. -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSIMDLookup DescentNextSignedWindow DescentOperandStateBanks DescentResetOperandComponents
noncomputable section
set_option quotPrecheck false
open scoped Fin.CommRing

def nativeCandidateField {D cap : ℕ} (signed coeff : ℕ) (f : Field) (r : Option (Record D cap)) : Cell coeff :=
  (((pointerField f).elim (0 : Cell signed) (fun i=>(Native.fields r i : Cell signed))).val : Cell coeff)

theorem no_candidate_field {D cap} (signed coeff : ℕ) (f : Field) :
    nativeCandidateField (D:=D) (cap:=cap) signed coeff f none=0 := by
  fin_cases f <;> simp [nativeCandidateField,pointerField,Native.fields]

theorem live_candidate_field {D cap signed coeff : ℕ} (r : Record D cap) (f : Field)
    (source : fresh r.neighbor.val r.shared f<2^signed) (dest : fresh r.neighbor.val r.shared f<2^coeff) :
    (nativeCandidateField signed coeff f (some r)).val=fresh r.neighbor.val r.shared f := by
  have repr : (pointerField f).elim (0:Cell signed) (fun i=>(Native.fields (some r) i : Cell signed)) =
      (fresh r.neighbor.val r.shared f : Cell signed) := by
    fin_cases f <;> rfl
  rw [nativeCandidateField,repr,Fin.val_cast_of_lt source,Fin.val_cast_of_lt dest]

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

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
local notation "unitAt" host => GrainPorts.Unit A ord C₀ host
local notation "faceAt" host:max u:max => Roster.face A ord C₀ host u
local notation "peerAt" host:max u:max => DescentResetWindowFields.neighbor A ord S B.next.valid names C₀ host (faceAt host u)
local notation "liveAt" host:max u:max => Stage.live A ord S B.next.valid names host (GrainPorts.port A ord C₀ host u)

def grainSlot (host : Host) (u : unitAt host) : Fin (2*totalLocal B) :=
  Roster.addr A ord C₀ host (localRoster B host) (faceAt host u)

def grainRecord (host : Host) (u : unitAt host) :=
  DescentResetWindowFields.record A ord S B.next.valid C₀ live host (faceAt host u) (peerAt host u)

theorem grain_recorded (host : Host) (u : unitAt host) :
    candidateRows B names host (grainSlot B host u)=some (grainRecord B names host u) :=
  Roster.mounted A ord C₀ host (localRoster B host) _ _

theorem grain_render (host : Host) (u : unitAt host) :
    render (grainRecord B names host u) u.val.1.2.val=some (liveAt host u) :=
  DescentResetWindowFields.render_actual A ord S B.next.valid names C₀ live (emission B) host u _
    (DescentResetWindowFields.near A ord S B.next.valid names C₀ host u)

/-- This is the seven-field value used by the packed kept-plus-new-candidate adder.
The serial increment is read from the mounted roster and the carried words retain their own range. -/
theorem live_operand_field (host : Host) (u : unitAt host) (shape : DescentResetRetainedCableLaw.Shape)
    (x : shape.Input) (donor : shape.Donor) (side : Bool) (slot : shape.Slot)
    (foundAt : shape.found x=some (donor,side,slot)) (tag : (shape.header x 0).val=1)
    (positive : 0<shape.units) (small : shape.oldIndex x donor side slot<2^shape.fieldBits)
    (offset : shape.oldIndex x donor side slot/shape.units=u.val.1.2.val)
    {labelBits : ℕ} (earlier : Field→Cell shape.fieldBits) (label : Cell labelBits)
    (span : Span) (prevPeer prevSerial prevChunk signed coeff : ℕ)
    (archive : ∀f,(earlier f).val=(Pointer.cable prevPeer prevSerial prevChunk).fields span f)
    (markedAt : marked (if side then .trunk else .stem) (decide ((shape.hubCell x).val=1))=
      (grainRecord B names host u).marked ∨ shape.oldIndex x donor side slot<shape.units)
    (width : max ((A).degree+1) ((A).cap+1)≤2^signed) (f : Field) :
    let r:=grainRecord B names host u
    let w₀:=liveAt host u
    let target:=(Pointer.cable w₀.neighbor.val (w₀.wire.val-w₀.within.val)
      (if r.marked then shape.oldIndex x donor side slot%shape.units else shape.oldIndex x donor side slot)).fields span f
    target<2^coeff →
    (((DescentResetRetainedPages.kept f (earlier 0) (earlier f) label).val+(shape.priceField f x).val : ℕ):Cell coeff).val+
      (nativeCandidateField signed coeff f (candidateRows B names host (grainSlot B host u))).val = target := by
  intro r w₀ target targetFits
  have render₀ : render r (shape.oldIndex x donor side slot/shape.units)=some w₀ := by
    rw [offset];exact grain_render B names host u
  have joined:=shape.recorded_fields x donor side slot foundAt tag positive small earlier label span
    prevPeer prevSerial prevChunk archive r w₀ markedAt render₀ f
  change _+_+fresh r.neighbor.val r.shared f=target at joined
  have shared : r.shared<(A).cap := by
    by_contra outside
    have full : ¬ r.shared + shape.oldIndex x donor side slot / shape.units < (A).cap := by omega
    simp [render,full] at render₀
  have capRoom: (A).cap<2^signed := (Nat.le_max_right ((A).degree+1) ((A).cap+1)).trans width
  have degRoom: (A).degree<2^signed := (Nat.le_max_left ((A).degree+1) ((A).cap+1)).trans width
  have src : fresh r.neighbor.val r.shared f<2^signed := by
    unfold DescentResetOperandComponents.fresh
    split
    · have peerPos:=r.neighbor.isLt;omega
    · split
      · exact r.neighbor.isLt.trans degRoom
      · split
        · exact shared.trans capRoom
        · omega
  have dst : fresh r.neighbor.val r.shared f<2^coeff := by omega
  have kept : (DescentResetRetainedPages.kept f (earlier 0) (earlier f) label).val+
      (shape.priceField f x).val<2^coeff :=by omega
  rw [grain_recorded,Fin.val_cast_of_lt kept,live_candidate_field r f src dst]
  exact joined

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
