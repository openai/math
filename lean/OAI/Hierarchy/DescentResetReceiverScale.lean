import OAI.Hierarchy.DescentResetReceiverPitch
import OAI.Hierarchy.DescentNamedResetSheetScale
import OAI.Hierarchy.DescentResetRootControlScale

namespace OAI
/-! # Local scalar prices for the actual dictionaries of a packed reset -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentCompiler.TerminalScale DescentSIMDLookup Filter
open DescentFallbackPeriod DescentResetMixedWordRAM DescentSixParty.PackedFlow.Padded
noncomputable section
variable {ι : ℕ→Type*} (J : ℕ→ℕ) (p : ∀h,ι h→ResetOutput)

/-- Each field below counts local nodes, finite control digits or native operand fields
of one date. The common receiver pitch is selected after measuring these quantities. -/
structure LocalInputs : Prop where
  sheets : CandidateSheets.LocalFields J (fun h i=>(p h i).sheets) (fun h i=>(p h i).front.peer.shapes)
    (fun h i=>(p h i).ticketBits)
  argumentCap : SmallAt J fun h i=>(p h i).argumentSlots
  rootBlocks : SmallAt J fun h i=>2^(p h i).middle.rootDepth
  rootHeaders : SmallAt J fun h i=>let v:=p h i;v.middle.rootControlBits v.front.donor.cap
  rootOutput : SmallAt J fun h i=>let v:=p h i;v.rootOutputBits
  actor : SmallAt J fun h i=>let v:=p h i;v.actor.unitBits
  cost : SmallAt J fun h i=>let v:=p h i;v.venue.census.broadcast
  precision : SmallAt J fun h i=>let v:=p h i;v.funded.precision
  projection : SmallAt J fun h i=>let v:=p h i;v.front.projectionBits
  rootDegree : SmallAt J fun h i=>let v:=p h i;v.middle.rootDegree
  degree : SmallAt J fun h i=>let v:=p h i;v.front.peer.oldDegree
  stemField : SmallAt J fun h i=>let v:=p h i;v.front.stemField
  privateWidth : SmallAt J fun h i=>let v:=p h i;v.front.privateBits
  wires : SmallAt J fun h i=>let v:=p h i;v.front.wireCap
  peer : SmallAt J fun h i=>let v:=p h i;v.front.peer.bits
  donor : SmallAt J fun h i=>let v:=p h i;v.front.donor.fieldBits
  donorBoard : SmallAt J fun h i=>let v:=p h i;v.front.donor.boardFields
  donorLanes : SmallAt J fun h i=>let v:=p h i;v.front.donor.laneFields
  returned : SmallAt J fun h i=>let v:=p h i;v.front.donor.returnFields
  query : SmallAt J fun h i=>let v:=p h i;v.front.donor.queryBits
  cargo : SmallAt J fun h i=>let v:=p h i;v.front.donor.cargoBits
  contact : SmallAt J fun h i=>let v:=p h i;v.front.contact.fieldBits
  oldFields : SmallAt J fun h i=>let v:=p h i;v.front.contact.oldFields
  view : SmallAt J fun h i=>let v:=p h i;v.front.contact.viewBits
  marker : SmallAt J fun h i=>let v:=p h i;v.front.contact.outputBits
  root : SmallAt J fun h i=>let v:=p h i;v.setup.packets.oldBits
  fallback : SmallAt J fun h i=>let v:=p h i;(v.setup.packets.stage 0 false).fields
  matrix : SmallAt J fun h i=>let v:=p h i;(v.setup.packets.stage 0 true).fields
  token : SmallAt J fun h i=>let v:=p h i;v.primitive.chart.bits
  tokenNodes : SmallAt J fun h i=>let v:=p h i;v.primitive.chart.nodes
  opcodes : SmallAt J fun h i=>let v:=p h i;v.primitive.rawBits
  casts : SmallAt J fun h i=>(p h i).setup.publicCasts.bound
  birthClass : SmallAt J fun h i=>(p h i).birth.classBits
  birthBits : SmallAt J fun h i=>(p h i).birth.rootBits
  birthPaid : SmallAt J fun h i=>(p h i).birth.paidBits
  birthSpan : SmallAt J fun h i=>(p h i).birth.spanBits
  oldToken : SmallAt J fun h i=>let v:=p h i;v.roleTransfer.transfer.bits
  signedQuery : SmallAt J fun h i=>let v:=p h i;v.receiver.queryBits
  signedRaw : SmallAt J fun h i=>(p h i).receiver.signedBits
  signedValue : SmallAt J fun h i=>let v:=p h i;v.receiver.valueBits
  nodeWidth : SmallAt J fun h i=>let v:=p h i;v.nodeBits
  nodes : SmallAt J fun h i=>let v:=p h i;v.nodes
  nextSigned : SmallAt J fun h i=>let v:=p h i;DescentSignedCableCodec.width v.venue.next.degree v.venue.next.cap
  paid : SmallAt J fun h i=>let v:=p h i;v.metadata.paidBits
  span : SmallAt J fun h i=>let v:=p h i;v.metadata.spanBits
  arity : SmallAt J fun h i=>let v:=p h i;v.metadata.chart.bits
  retained : SmallAt J fun h i=>let v:=p h i;v.setup.retained.bits
  signed : SmallAt J fun h i=>let v:=p h i;v.setup.signedBits
  oldOrder : SmallAt J fun h i=>let v:=p h i;v.setup.ticketBits
  newInput : SmallAt J fun h i=>let v:=p h i;v.setup.fieldBits
  donors : SmallAt J fun h i=>let v:=p h i;v.setup.retained.donors
  cap : SmallAt J fun h i=>let v:=p h i;v.setup.oldCap
  rotor : SmallAt J fun h i=>let v:=p h i;v.setup.rotorBits
  packet : SmallAt J fun h i=>let v:=p h i;v.setup.fallbackBits
  packetSize : SmallAt J fun h i=>let v:=p h i;v.setup.fallbackInputs

attribute [local irreducible] SmallAt
set_option maxHeartbeats 1800000 in
theorem group_width_scale (r : LocalInputs J p) : SmallAt J fun h i=>(p h i).groupWidth :=by
  let rootList (m : ResetMiddle) (cap : ℕ) :=
    let L:=2^m.rootDepth
    let n:=Projected.Receiver.arityLimit m.rootDegree L cap m.rotorBits m.rootDepth
    [sharedWidth m.stencil,(m.signedBits+m.signedBits)*L,m.projectBits,m.stencil.n,
     m.rootField*(n+1),m.rootField*n,m.signedBits*L,n]
  have control (v : ResetOutput) : ∀x∈rootList v.middle v.front.donor.cap,
      x≤v.middle.rootControlBits v.front.donor.cap :=v.middle.rootControl_le v.front.donor.cap
  have a0 : SmallAt J (fun h i=>let v:=p h i;let m:=v.middle;
      let n:=Projected.Receiver.arityLimit m.rootDegree (2^m.rootDepth) v.front.donor.cap m.rotorBits m.rootDepth
      sharedWidth m.stencil) :=r.rootHeaders.of_le fun h i=>control (p h i) _ (by simp [rootList])
  have a1 : SmallAt J (fun h i=>let v:=p h i;let m:=v.middle;
      let n:=Projected.Receiver.arityLimit m.rootDegree (2^m.rootDepth) v.front.donor.cap m.rotorBits m.rootDepth
      (m.signedBits+m.signedBits)*2^m.rootDepth) :=r.rootHeaders.of_le fun h i=>control (p h i) _ (by simp [rootList])
  have a2 : SmallAt J (fun h i=>let v:=p h i;let m:=v.middle;
      let n:=Projected.Receiver.arityLimit m.rootDegree (2^m.rootDepth) v.front.donor.cap m.rotorBits m.rootDepth
      m.projectBits) :=r.rootHeaders.of_le fun h i=>control (p h i) _ (by simp [rootList])
  have a3 : SmallAt J (fun h i=>let v:=p h i;let m:=v.middle;
      let n:=Projected.Receiver.arityLimit m.rootDegree (2^m.rootDepth) v.front.donor.cap m.rotorBits m.rootDepth
      m.stencil.n) :=r.rootHeaders.of_le fun h i=>control (p h i) _ (by simp [rootList])
  have a4 : SmallAt J (fun h i=>let v:=p h i;let m:=v.middle;
      let n:=Projected.Receiver.arityLimit m.rootDegree (2^m.rootDepth) v.front.donor.cap m.rotorBits m.rootDepth
      m.rootField*(n+1)) :=r.rootHeaders.of_le fun h i=>control (p h i) _ (by simp [rootList])
  have a5 : SmallAt J (fun h i=>let v:=p h i;let m:=v.middle;
      let n:=Projected.Receiver.arityLimit m.rootDegree (2^m.rootDepth) v.front.donor.cap m.rotorBits m.rootDepth
      m.rootField*n) :=r.rootHeaders.of_le fun h i=>control (p h i) _ (by simp [rootList])
  have a6 : SmallAt J (fun h i=>let v:=p h i;let m:=v.middle;
      let n:=Projected.Receiver.arityLimit m.rootDegree (2^m.rootDepth) v.front.donor.cap m.rotorBits m.rootDepth
      m.signedBits*2^m.rootDepth) :=r.rootHeaders.of_le fun h i=>control (p h i) _ (by simp [rootList])
  have c (n : ℕ) := SmallAt.const (ι := ι) J n
  have selectors := r.sheets.block.mul ((r.sheets.block.add (c 1)).clog)
  have tokenTotal := r.token.mul r.tokenNodes
  have retainedWidth := r.nodeWidth.mul r.sheets.block
  have roleTotal := r.token.mul ((c 2).mul r.nodes |>.add (c 1))
  have oldPairs := r.donors.mul ((c 2).mul r.cap)
  dsimp only [groupWidth,rootUnits,receiverUnits,List.cons_append,List.nil_append,List.sum_cons,List.sum_nil]
  apply SmallAt.add (c 1)
  apply SmallAt.add a0
  apply SmallAt.add a1
  apply SmallAt.add a2
  apply SmallAt.add a3
  apply SmallAt.add r.rootOutput
  apply SmallAt.add a4
  apply SmallAt.add a5
  apply SmallAt.add r.actor
  apply SmallAt.add r.cost
  apply SmallAt.add r.precision
  apply SmallAt.add ((r.precision.mul r.rootBlocks).add r.precision)
  apply SmallAt.add ((r.precision.add r.precision).mul r.rootBlocks)
  apply SmallAt.add (r.rootBlocks.mul (r.rootBlocks.add (c 1)).clog)
  apply SmallAt.add r.nextSigned
  apply SmallAt.add a6
  apply SmallAt.add r.projection
  apply SmallAt.add ((r.stemField.mul (r.rootDegree.add (c 2))).add r.stemField)
  apply SmallAt.add (r.privateWidth.mul (r.wires.mul (c 5)))
  apply SmallAt.add (r.stemField.add (c 2))
  apply SmallAt.add r.peer
  apply SmallAt.add ((r.donor.mul r.donorBoard).add r.donor)
  apply SmallAt.add (((r.donor.mul r.donorLanes).mul (c 2)).add (r.donor.mul r.donorLanes))
  apply SmallAt.add ((r.donor.mul r.returned).add r.donor)
  apply SmallAt.add r.donor
  apply SmallAt.add (r.query.add r.cargo)
  apply SmallAt.add (r.cargo.add r.cargo)
  apply SmallAt.add ((r.contact.mul r.oldFields).add r.contact)
  apply SmallAt.add (r.view.add r.view)
  apply SmallAt.add ((r.contact.mul (c 8)).add r.contact)
  apply SmallAt.add r.marker
  apply SmallAt.add r.sheets.meta
  apply SmallAt.add (r.root.mul r.fallback)
  apply SmallAt.add (r.root.mul r.matrix)
  apply SmallAt.add ((c 1).max ((r.nodeWidth.mul r.nodes).max ((retainedWidth.add r.nodeWidth).max (((retainedWidth.mul (((c 2).add ((c 7).mul r.argumentCap)).mul r.nodes)).add retainedWidth).max (retainedWidth.add selectors)))))
  apply SmallAt.add ((c 1).max (((roleTotal.add r.token).mul r.sheets.block).max ((r.token.mul r.sheets.block).add selectors)))
  apply SmallAt.add (r.rotor.add (c 1))
  apply SmallAt.add ((r.birthClass.add r.birthPaid).max ((r.birthSpan.add r.birthSpan).max ((r.birthClass.add r.birthBits).max (r.birthClass.add (c 1)))))
  apply SmallAt.add (r.birthBits.mul r.sheets.block)
  apply SmallAt.add r.casts
  apply SmallAt.add (r.oldToken.mul r.sheets.block)
  apply SmallAt.add r.opcodes
  apply SmallAt.add (tokenTotal.add r.token)
  apply SmallAt.add ((r.sheets.select_.max r.sheets.short).mul (r.sheets.block.add (c 1)))
  apply SmallAt.add (r.sheets.stem.max r.sheets.meta)
  apply SmallAt.add (r.sheets.meta.mul (c 10))
  apply SmallAt.add r.sheets.stem
  apply SmallAt.add (r.sheets.select_.add r.sheets.short)
  apply SmallAt.add (r.sheets.short.add r.sheets.short)
  apply SmallAt.add (((r.sheets.meta.mul (c 7)).add r.sheets.blank).max ((c 2).add (r.sheets.short.add r.sheets.short)))
  apply SmallAt.add ((r.sheets.old.mul (c 6)).add r.sheets.old)
  apply SmallAt.add r.sheets.argument
  apply SmallAt.add (((r.sheets.meta.mul (c 7)).add r.sheets.blank).max ((c 2).add (r.sheets.halo.add r.sheets.argument)))
  apply SmallAt.add ((r.stemField.mul (r.degree.add (c 2))).add r.stemField)
  apply SmallAt.add (r.projection.mul r.sheets.block)
  apply SmallAt.add (((r.stemField.add (c 2)).add (r.sheets.meta.mul (c 7))).max ((r.sheets.meta.mul (c 7)).add (r.sheets.meta.mul (c 7))))
  apply SmallAt.add ((r.sheets.meta.mul (c 7)).add r.sheets.meta)
  apply SmallAt.add (r.sheets.meta.mul r.sheets.block)
  apply SmallAt.add ((r.sheets.meta.mul (c 7)).add r.sheets.original_)
  apply SmallAt.add ((r.sheets.original_.mul (c 5)).add (r.sheets.original_.mul (c 5)))
  apply SmallAt.add ((((c 4).mul r.sheets.slots).add (c 1)).clog.add r.sheets.meta)
  apply SmallAt.add ((r.sheets.meta.mul (c 5)).add (r.sheets.meta.mul (c 5)))
  apply SmallAt.add (((c 8).mul r.sheets.meta).add r.sheets.meta)
  apply SmallAt.add (r.signedQuery.add r.signedValue)
  apply SmallAt.add (r.signedQuery.add r.signedRaw)
  apply SmallAt.add ((r.nodeWidth.mul r.nodes).add r.nodeWidth)
  apply SmallAt.add (r.paid.max (r.span.add r.arity))
  apply SmallAt.add (r.retained.max ((c 1).max (r.signed.max r.oldOrder)))
  apply SmallAt.add r.newInput
  apply SmallAt.add ((r.newInput.mul ((c 6).add ((c 2).mul oldPairs))).add r.newInput)
  apply SmallAt.add (r.newInput.add (c 2))
  apply SmallAt.add ((r.rotor.mul (c 4)).add r.rotor)
  apply SmallAt.add ((r.packet.mul r.packetSize).add r.packet)
  apply SmallAt.add (r.retained.mul r.sheets.block)
  apply SmallAt.add (r.signed.mul r.sheets.block)
  apply SmallAt.add ((r.root.mul r.fallback).mul r.sheets.block)
  apply SmallAt.add ((r.root.mul r.matrix).mul r.sheets.block)
  exact c 0

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
