import OAI.Hierarchy.DescentPhysicalResetDateOperands
import OAI.Hierarchy.DescentRetainedHomeMover
import OAI.Hierarchy.DescentResetActorCalendar
import OAI.Hierarchy.DescentDatedResetVenueRun
import OAI.Hierarchy.DescentResetHubRectangle
import OAI.Hierarchy.DescentPreparedRootInputs
import OAI.Hierarchy.DescentFundedSetup
import OAI.Hierarchy.DescentFundedCensusRoles
import OAI.Hierarchy.DescentFundedBankAddress
import OAI.Hierarchy.DescentVenueQuantityAny
import OAI.Hierarchy.DescentStageVenueAny
import OAI.Hierarchy.DescentDatedNodeMetadataPack
import OAI.Hierarchy.DescentResetMetadataInputs
import OAI.Hierarchy.DescentResetPrimitiveCheckpoint
import OAI.Hierarchy.DescentRetainedPrimitiveMover
import OAI.Hierarchy.DescentResetActorClassIssued
import OAI.Hierarchy.DescentPrimitiveBirthProgram
import OAI.Hierarchy.DescentPrimitivePreparedGuards

namespace OAI
/-! A fixed reset date through the physical successor's structure, paid counts, and retained node arities. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.Chronology DescentContacts DescentCommonHost DescentSIMDLookup
open DescentFundedCensus DescentVenueQuantityPlanes
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "F₀" => (v).funded
local notation "V₀" => (v).venue
local notation "Q" => (V₀).census
local notation "T" => (V₀).dense
local notation "V₁" => (V₀).next
local notation "M₀" => (v).metadata
local notation "M₁" => (M₀).chart
local notation "stop₀" => (v).finalEnd b
local notation "fund" => (v).fundedEnd b
local notation "dense" => (V₀).denseStart fund
local notation "venue" => (V₀).venueStart fund
local notation "roleAt" => (v).fullEnd b
local notation "movedAt" => (v).roleEnd b
local notation "classAt" => (v).classEnd b
local notation "bornAt" => (v).birthEnd b
local notation "move" => (v).roleTransfer
local notation "meta" => (v).primitiveEnd b
local notation "actors" => (v).actor.directory ((v).middle.stop b)
local notation "P" => a.stencilPhase u.shape floor u.count u.hub u.g u.Y
local notation "key" => (⟨(P).saved,0⟩ : Bank)
local notation "n" => (v).middle.rotorBits
local notation "r" => (v).middle.rootDepth

/-- The fixed coefficient dictionary of the whole trace supplies the role decoder at every date. -/
structure PrimitiveMenu where
  F : Type
  [field : Field F]
  gadget : PoweredGadget F
  stageBits : ℕ
  grain : ℕ
  op : DescentSixParty.RotorSpec

attribute [instance] PrimitiveMenu.field


structure FinalInputs where
  menu : PrimitiveMenu
  previousRoleBase : ℕ
  previousRoleStride : ℕ
  previousRoleBits : ℕ
  roleNodes : (v).primitive.chart.nodes=(move).transfer.nodes
  roleBlocks : (v).primitive.chart.blocks=(move).blocks
  classShape : (v).actorClass.rawHosts=(v).actor.hosts*(DescentDenseHostOrder.roster u.atlas.board r u.roots.Ht).card
  primaryRanks : (move).shapes=(v).setup.placement.shapes
  guardRoots : (v).birth.roots=2*(2^r*2^n)
  guardDepth : (v).birth.residual=r
  birthNodes : (v).primitive.chart.nodes=(v).birth.nodes
  birthBlocks : (v).primitive.chart.blocks=(v).birth.placement.blocks
  birthArgs : (v).birth.arguments=u.operand.slots
  censusBlocks : (v).primitive.chart.blocks=(M₁).blocks
  censusNodes : (v).primitive.chart.nodes=(M₁).nodes


  io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands
  signedCount : (F₀).capacity=a.c/2
  roleCount : (Q).jobs=(DescentDenseHostOrder.roster u.atlas.board r u.roots.Ht).card
  metaBlocks : (M₁).blocks=(v).receiver.blocks
  metaNodes : (M₁).nodes=u.operand.nodes

/-- The final inputs attached to an operand date. -/
abbrev DateInputs.FinalInputs (u : a.DateInputs floor w) := PhysicalReset.FinalInputs u

variable {u} (z : u.FinalInputs)
namespace FinalInputs
def earlier (j : Fin (F₀).blocks) := DescentFundedCensus.priorBank z.io j.val

def previousRoles (j : Fin (move).transfer.blocks) : Bank :=
  ⟨z.previousRoleBase+j.val*z.previousRoleStride,z.previousRoleBits⟩
def primary (j : Fin (move).shapes) :=u.menu.keep (j.cast z.primaryRanks)
def which (j : Fin (move).shapes) : Option ℕ:=u.menu.target (j.cast z.primaryRanks)
def oldMatrix (u : a.DateInputs floor w) : Expr:=
  OperandMenu.matrixPacket (z:=u.atlas) (roots:=u.roots) u.shape floor u.count u.hub u.g u.Y w
def classKey (i : Fin (v).actorClass.rawHosts) :=
  DescentResetActorClass.indexBook u.atlas.board (v).actor.hosts r u.roots.Ht (i.cast z.classShape)
def classes :=(v).actorClass.native movedAt z.classKey w
def ports : DescentFundedCensus.Ports r n :=
  let rc:=a.rootPhase u.shape floor u.count u.hub u.g u.Y u.roots w
  let width:=Nat.clog 2 ((v).actor.hosts*(v).actor.chunksPerHost)
  ⟨.lookup ((F₀).primary stop₀) .row,(F₀).secondary stop₀ (fun j=>.lookup (rc.tapped (j.cast (congrArg (2*·) z.signedCount))) .row),.lookup ⟨(P).output,width⟩ .row,
    fun side label=>rc.gatheredOperand u.book (side,.inr label)⟩

def presence (j : Fin (Q).jobs) : Expr :=
  .lookup ((v).actor.scene ((v).middle.stop b)) (.op .add (.lit (j.val*((v).actor.hosts*(v).actor.chunksPerHost))) .row)

def jobs :=fun j : Fin (Q).jobs=>DescentFundedCensus.compile («r»:=r) (Ht:=u.roots.Ht) u.atlas.board u.atlas.C u.atlas.packet
  u.atlas.groupDigits (Q).bits (F₀).capacity a.depthCut (F₀).degree (F₀).capacity u.roots.field (P).S.t z.ports
  (presence (a:=a) (floor:=floor) j) (ActorSetup.shapeAt u.atlas.board r u.roots.Ht (j.cast z.roleCount))

/-- Raw ports come from the three issued peer columns. The two direction maps and
the actor raster are the measured outputs of that date’s actor directory. -/
def predecessor (u : a.DateInputs floor w) : ResetVenue.Earlier :=
  let p:=(v).front.peer
  let raw:=p.rawPeers ((v).front.peers ((v).actorEnd b))
  let out:=DescentNextSignedWindow.Native.All.outputBase ((v).fieldsEnd b) (v).receiver.capacity
    (v).receiver.signedBits (v).receiver.lanes
  let rows:=(v).receiver.hosts*chunks (v).receiver.groups (v).receiver.lanes
  let signed:=fun x j=>⟨out+(x*(2*(v).receiver.capacity)+j)*DescentDyadicSpan.span rows,Nat.clog 2 rows⟩
  ⟨(v).actor.scene ((v).middle.stop b),
   ⟨(actors).count,(actors).inverse,(actors).ranks,fun i=>⟨raw+i.val*p.hosts,Nat.clog 2 p.hosts⟩⟩,
   signed,DescentDenseHostOrder.publicTag u.atlas.board r u.roots.Ht⟩

def paid (u : a.DateInputs floor w) : (M₁).Counts :=fun x=>.lookup
  (((V₀).sources (predecessor u) fund).paid x.val) .row
def spans : (M₁).Spans u.operand.slots :=fun x j i=>
  DescentResetMetadataInputs.spanLookup v u.operand b (x.cast z.metaBlocks) (j.cast z.metaNodes) i

def classWord (_u : a.DateInputs floor w) : Expr :=(v).actorClass.expr movedAt (actors).count (actors).inverse
def guards : (v).birth.Guards :=fun q d=>
  let rc:=a.rootPhase u.shape floor u.count u.hub u.g u.Y u.roots w
  DescentPrimitiveBirth.guards (rc.headerEnd u.book) (v).middle.rootHosts (v).middle.rootGroups
    (v).middle.rootLanes r n (v).middle.rootDegree (q.cast z.guardRoots)
    (d.cast (congrArg (·+1) z.guardDepth))
def roles : (v).primitive.Inputs :=
  ⟨fun x j=>.lookup ((move).bank roleAt (j.cast z.roleNodes) (x.cast z.roleBlocks)) .row,
   fun x j=>(v).birth.bornAt classAt (j.cast z.birthNodes) (x.cast z.birthBlocks)
     (classWord u) (paid u (x.cast z.censusBlocks))
     (fun i=>z.spans (x.cast z.censusBlocks) (j.cast z.censusNodes) (i.cast z.birthArgs)),
   fun x j=>(v).birth.relay classAt (j.cast z.birthNodes) (classWord u) (paid u (x.cast z.censusBlocks))⟩
local notation "first" => (F₀).program w stop₀ z.earlier key
local notation "t₁" => (F₀).ticks w stop₀ z.earlier key
local notation "second" => DescentFundedCensus.program z.jobs w fund
local notation "t₂" => DescentFundedCensus.ticks z.jobs fund
local notation "vphase" => (V₀).phase (predecessor u) fund w
local notation "roleMove" => (move).program roleAt z.previousRoles key (actors).count (actors).inverse z.which (oldMatrix u) w
local notation "tMove" => (move).ticks roleAt z.previousRoles key (actors).count (actors).inverse z.which (oldMatrix u) w
local notation "publishBirth" => (v).birth.program classAt z.guards (actors).count (actors).inverse w
local notation "birthCost" => (v).birth.clock classAt z.guards (actors).count (actors).inverse
local notation "checked" => (v).primitive.program z.menu.gadget z.menu.stageBits z.menu.grain z.menu.op bornAt z.roles w
local notation "t₄" => (v).primitive.clock z.menu.gadget z.menu.stageBits z.menu.grain z.menu.op bornAt z.roles
local notation "final" => (M₁).metadataProgram meta (M₀).paidBits (M₀).spanBits w (paid u) z.spans
local notation "t₅" => (M₁).metadataTime meta (M₀).paidBits (M₀).spanBits (paid u) z.spans

def tailCode : Procedure w :=(((((((first).seq second).seq (vphase).program).seq roleMove).seq z.classes.program).seq publishBirth).seq checked).seq final
def tailTime :=((((((t₁+t₂)+(vphase).ticks)+tMove)+z.classes.ticks)+birthCost)+t₄)+t₅

structure Room : Prop where
  earlier : ∀j,(z.earlier j).Fits w stop₀
  saved : (key).Fits w stop₀
  «fund» : fund<2^w
  jobs : DescentFundedCensus.Room z.jobs w fund
  successor : (V₀).RunRoom (predecessor u) fund 0 w
  «roleMove» : (move).Room roleAt z.previousRoles key (actors).count (actors).inverse (oldMatrix u) w
  birth : (v).birth.RootRoom classAt z.guards (actors).count (actors).inverse w
  roleFields : (v).primitive.Fits bornAt z.roles w
  count : ∀x,((paid u) x).Fits w meta
  spans : ∀x j i,(z.spans x j i).Fits w meta
  endFits : a.endAddress floor<2^w

/-- Memory immediately after the successor's actual roster, signed and paid banks have been issued. -/
def venueImage (mem : Memory w) : Memory w :=
  (vphase).image (DescentFundedCensus.memory z.jobs fund ((F₀).memory stop₀ z.earlier key mem))

def retainedImage (mem : Memory w) : Memory w :=
  (move).finalMem roleAt z.previousRoles key (actors).count (actors).inverse z.which (oldMatrix u) (z.venueImage mem)

def classImage (mem : Memory w) : Memory w := z.classes.image (z.retainedImage mem)

/-- Input to the primitive-role checker after role transfer, actor classification,
and publication of the birth registers. -/
def roleInput (mem : Memory w) : Memory w :=
  (v).birth.image classAt z.guards (actors).count (actors).inverse (z.classImage mem)

/-- Complete deterministic RAM image of the tail, including its published arities. -/
def finalImage (mem : Memory w) : Memory w :=
  let checkedMem := (v).primitive.finalMem z.menu.gadget z.menu.stageBits z.menu.grain z.menu.op bornAt z.roles (z.roleInput mem)
  (M₁).metadataImage meta (M₀).paidBits (M₀).spanBits (paid u) z.spans checkedMem

attribute [local irreducible] Procedure.Exec CheapCode

set_option maxHeartbeats 650000 in
theorem tail_result (ok : z.Room) (mem : Memory w) :
    z.tailCode.Exec mem (z.finalImage mem) z.tailTime ∧ CheapCode z.tailCode ∧
      (∀x,x<stop₀ ∨ a.endAddress floor≤x→z.finalImage mem x=mem x) ∧
      ∀x,x<roleAt→z.finalImage mem x=z.venueImage mem x :=by
  obtain ⟨a₁,c₁,h₁⟩:=(F₀).any stop₀ z.earlier key mem ok.earlier ok.saved ok.fund
  let m₁:=(F₀).memory stop₀ z.earlier key mem
  obtain ⟨a₂,c₂,h₂⟩:=DescentFundedCensus.any z.jobs ok.jobs m₁
  let m₂:=DescentFundedCensus.memory z.jobs fund m₁
  obtain ⟨a₃,h₃⟩:=(V₀).any (predecessor u) fund m₂ ok.successor
  have o₁:stop₀≤fund:=(F₀).room stop₀
  obtain ⟨o₂,o₃,o₄⟩:=(V₀).after fund
  have roleBefore:roleAt≤ movedAt:=by
    change roleAt≤(move).endAddress roleAt
    rw [(move).translate];exact Nat.le_add_right ..
  have classBefore:movedAt≤classAt:=by
    change movedAt≤(v).actorClass.endAddress movedAt
    rw [(v).actorClass.translate];exact Nat.le_add_right ..
  have birthBefore:classAt≤bornAt:=by
    change classAt≤(v).birth.endAddress classAt
    rw [(v).birth.translate];exact Nat.le_add_right ..
  have primitiveBefore:bornAt≤ meta:=by
    change bornAt≤(v).primitive.endAddress bornAt
    rw [(v).primitive.translate];exact Nat.le_add_right ..
  have o₅:meta≤a.endAddress floor:=by
    change meta≤(M₀).endAddress meta
    rw [(M₀).translate];exact Nat.le_add_right ..
  obtain ⟨runMove,cheapMove,moveFrame⟩:=(move).any roleAt z.previousRoles key (actors).count (actors).inverse
    z.which (oldMatrix u) (z.venueImage mem) ok.roleMove
  let moved:=(move).finalMem roleAt z.previousRoles key (actors).count (actors).inverse z.which (oldMatrix u) (z.venueImage mem)
  obtain ⟨runClass,cheapClass,classFrame⟩:=(v).actorClass.any movedAt z.classKey moved
    (birthBefore.trans_lt (primitiveBefore.trans_lt (o₅.trans_lt ok.endFits)))
  obtain ⟨runBirth,cheapBirth,birthFrame⟩:=(v).birth.any classAt z.guards (actors).count (actors).inverse
    (z.classes.image moved) ok.birth (primitiveBefore.trans_lt (o₅.trans_lt ok.endFits))
  obtain ⟨a₄,c₄,h₄⟩:=(v).primitive.any z.menu.gadget z.menu.stageBits z.menu.grain z.menu.op bornAt
    z.roles (z.roleInput mem) ok.roleFields (o₅.trans_lt ok.endFits)
  obtain ⟨a₅,h₅,c₅⟩:=(M₁).metadataAny meta (M₀).paidBits (M₀).spanBits (paid u) z.spans
    ((v).primitive.finalMem z.menu.gadget z.menu.stageBits z.menu.grain z.menu.op bornAt z.roles (z.roleInput mem)) ok.count ok.spans ok.endFits
  have run12 : ((first).seq second).Exec mem m₂ (t₁+t₂) :=
    @Procedure.Exec.then w _ _ _ _ _ _ _ @a₁ @a₂
  have run123 : (((first).seq second).seq (vphase).program).Exec mem (z.venueImage mem) ((t₁+t₂)+(vphase).ticks) :=
    @Procedure.Exec.then w _ _ _ _ _ _ _ @run12 @a₃
  have runMoveAll : ((((first).seq second).seq (vphase).program).seq roleMove).Exec mem moved (((t₁+t₂)+(vphase).ticks)+tMove) :=
    @Procedure.Exec.then w _ _ _ _ _ _ _ @run123 @runMove
  have runPacked : ((((first).seq second).seq (vphase).program).seq roleMove |>.seq z.classes.program).Exec mem (z.classImage mem) ((((t₁+t₂)+(vphase).ticks)+tMove)+z.classes.ticks) :=
    @Procedure.Exec.then w _ _ _ _ _ _ _ @runMoveAll @runClass
  have phaseCheap : CheapCode (vphase).program := @NativePhase.cheap w (vphase)
  have cheapPacked : CheapCode (((((first).seq second).seq (vphase).program).seq roleMove).seq z.classes.program) :=
    cheap_seq (cheap_seq (cheap_seq (cheap_seq c₁ c₂) phaseCheap) cheapMove) cheapClass
  refine ⟨?_,cheap_seq (cheap_seq (cheap_seq cheapPacked cheapBirth) c₄) c₅, ?_⟩
  · let pre := ((((first).seq second).seq (vphase).program).seq roleMove).seq z.classes.program
    let preTime := ((((t₁+t₂)+(vphase).ticks)+tMove)+z.classes.ticks)
    let checker := (v).primitive.finalMem z.menu.gadget z.menu.stageBits z.menu.grain z.menu.op bornAt z.roles (z.roleInput mem)
    have rb : (pre.seq publishBirth).Exec mem (z.roleInput mem) (preTime + birthCost) :=
      @Procedure.Exec.then w pre publishBirth mem (z.classImage mem) (z.roleInput mem) preTime birthCost @runPacked @runBirth
    have rc : ((pre.seq publishBirth).seq checked).Exec mem checker (preTime + birthCost + t₄) :=
      @Procedure.Exec.then w (pre.seq publishBirth) checked mem (z.roleInput mem) checker (preTime + birthCost) t₄ @rb @a₄
    exact @Procedure.Exec.then w ((pre.seq publishBirth).seq checked) final mem checker (z.finalImage mem) (preTime + birthCost + t₄) t₅ @rc @a₅
  have roleBeforeClass := roleBefore.trans classBefore
  have roleBeforeBirth := roleBeforeClass.trans birthBefore
  have roleBeforeMeta := roleBeforeBirth.trans primitiveBefore
  have birthEnd := primitiveBefore.trans o₅
  have classEnd := birthBefore.trans birthEnd
  have moveEnd := classBefore.trans classEnd
  have roleEnd := roleBefore.trans moveEnd
  have denseBefore : dense ≤ roleAt := o₃.trans o₄
  have fundBefore : fund ≤ roleAt := o₂.trans denseBefore
  have startBefore : stop₀ ≤ roleAt := o₁.trans fundBefore
  have tailFrame (x : ℕ) (hx : x<roleAt ∨ a.endAddress floor≤x) : z.finalImage mem x=z.venueImage mem x :=by
    exact (h₅ x (hx.imp (fun h => h.trans_le roleBeforeMeta) id)).trans
      ((h₄ x (hx.imp (fun h => h.trans_le roleBeforeBirth) (fun h => o₅.trans h))).trans
      ((birthFrame x (hx.imp (fun h => h.trans_le roleBeforeClass) (fun h => birthEnd.trans h))).trans
      ((classFrame x (hx.imp (fun h => h.trans_le roleBefore) (fun h => classEnd.trans h))).trans
      (moveFrame x (hx.imp id (fun h => moveEnd.trans h))))))
  refine ⟨?_,fun x hx=>tailFrame x (Or.inl hx)⟩
  intro x hx
  exact (tailFrame x (hx.imp_left (fun h => h.trans_le startBefore))).trans
    ((h₃ x (hx.imp (fun h => h.trans_le (o₁.trans o₂)) (fun h => roleEnd.trans h))).trans
    ((h₂ x (hx.imp (fun h => h.trans_le o₁) (fun h => (denseBefore.trans roleEnd).trans h))).trans
    (h₁ x (hx.imp_right (fun h => (fundBefore.trans roleEnd).trans h)))))


theorem tail_image (ok : z.Room) (mem : Memory w) : z.tailCode.Exec mem (z.finalImage mem) z.tailTime :=
  (z.tail_result ok mem).1

theorem tail_visible (ok : z.Room) (mem : Memory w) :
    ∃dst : Memory w,z.tailCode.Exec mem dst z.tailTime ∧ CheapCode z.tailCode ∧
      (∀x,x<stop₀ ∨ a.endAddress floor≤x→dst x=mem x) ∧
      ∀x,x<roleAt→dst x=z.venueImage mem x :=
  ⟨z.finalImage mem,z.tail_result ok mem⟩

theorem tail_any (ok : z.Room) (mem : Memory w) :
    ∃dst : Memory w,z.tailCode.Exec mem dst z.tailTime ∧ CheapCode z.tailCode ∧
      ∀x,x<stop₀ ∨ a.endAddress floor≤x→dst x=mem x :=by
  obtain ⟨dst,ran,cheap,frame,_⟩:=z.tail_visible ok mem
  exact ⟨dst,ran,cheap,frame⟩

end FinalInputs
/-- A single public reset instruction sequence, including the returned role and arity words. -/
def date : DateCode w :=.reset (u.throughOperands.seq z.tailCode) (u.throughOperandTicks+z.tailTime)

theorem date_operand_end (a : PhysicalReset) (floor : ℕ) :
    a.successor.finalEnd (a.rebased floor)≤a.endAddress floor :=by
  let v₀:=a.successor
  let pos:=a.rebased floor
  obtain ⟨fund₀,venue₀⟩:=v₀.complete_after pos
  have role₀:v₀.fullEnd pos≤v₀.roleEnd pos:=by
    change _≤v₀.roleTransfer.endAddress (v₀.fullEnd pos)
    rw [v₀.roleTransfer.translate];exact Nat.le_add_right ..
  have class₀:v₀.roleEnd pos≤v₀.classEnd pos:=by
    change _≤v₀.actorClass.endAddress (v₀.roleEnd pos)
    rw [v₀.actorClass.translate];exact Nat.le_add_right ..
  have birth₀:v₀.classEnd pos≤v₀.birthEnd pos:=by
    change _≤v₀.birth.endAddress (v₀.classEnd pos)
    rw [v₀.birth.translate];exact Nat.le_add_right ..
  have op₀:v₀.birthEnd pos≤v₀.primitiveEnd pos:=by
    change _≤v₀.primitive.endAddress (v₀.birthEnd pos)
    rw [v₀.primitive.translate];exact Nat.le_add_right ..
  have meta₀:v₀.primitiveEnd pos≤v₀.metadataEnd pos:=by
    change _≤v₀.metadata.endAddress (v₀.primitiveEnd pos)
    rw [v₀.metadata.translate];exact Nat.le_add_right ..
  exact fund₀.trans (venue₀.trans (role₀.trans (class₀.trans (birth₀.trans (op₀.trans meta₀)))))

theorem date_any (ready : u.Ready) (room : z.Room) (m : Memory w) :
    ∃dst : Memory w,(date z).Runs m dst ∧ (date z).cheap ∧ ∀i,i<floor ∨ a.endAddress floor≤ i→dst i=m i := by
  obtain ⟨mid,h,c,frame⟩:=u.run_to_operands ready m
  obtain ⟨dst,j,k,outer⟩:=z.tail_any room mid
  have h₀:floor≤ stop₀:=by obtain ⟨p₁,p₂,p₃,p₄,p₅,p₆,p₇,p₈,p₉⟩:=ready.ordered;omega
  have end_:=date_operand_end a floor
  exact ⟨dst,@Procedure.Exec.then w u.throughOperands z.tailCode m mid dst u.throughOperandTicks z.tailTime @h @j,@cheap_seq w u.throughOperands z.tailCode @c @k,fun i outside=>(outer i (outside.imp_left (·.trans_le h₀))).trans
    (frame i (outside.imp_right (end_.trans ·)))⟩

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
