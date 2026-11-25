import OAI.Hierarchy.DescentOriginalSignedPhase
import OAI.Hierarchy.DescentDatedSignedAny
import OAI.Hierarchy.DescentOrdinaryMountedInlet
import OAI.Hierarchy.DescentDatedOperandHeaderStep
import OAI.Hierarchy.DescentDatedOperandHeaderPair

namespace OAI
/-! The same signed parent fields remain readable through the entire operand header prefix. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentDatedOperandReadPipeline DescentPackedZip DescentPackedColony
open DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOrdinaryOriginMask
open DescentDatedSourcePathDirectory DescentHaloWalkRAM DescentRawCablePanel DescentSIMDLookup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1600000
set_option maxRecDepth 6000
variable {F Pin : Type} [Field F] (v:PhysicalOrdinary F Pin) (floor:ℕ)
variable (A:v.ArgumentEntry) (match_:A.Match v floor) (refs:v.SourceReferences) (orig:v.SourceMasks)
local notation "e₀" => v.material
local notation "fmt" => v.ticket.depotShape v.short
local notation "low₀" => v.signedEnd floor
local notation "vec" => v.vectorStart floor
local notation "route" => v.routedStart floor
local notation "ports₀" => v.originPortEnd floor
local notation "mouth" => v.originMouthEnd floor
local notation "oldHeader" => v.operandOldHeaderStart floor
local notation "high₀" => v.operandHeaderEnd floor

/-- Address/word room for the original eight consecutive writes that precede operand lookup. -/
structure OperandHeaderRoom (w:ℕ) : Prop where
  inlet : A.Room v floor w
  gather : refs.Room w vec
  masks : ∀u,(mask (orig u)).Fits w route
  group : v.bornBook.groups=v.vector.groups*v.vector.radix
  mouths : ∀a l,((v.mouthRef A match_ a l).expr v.bornBook.hosts).inputEnd≤ports₀
  panel : A.venue.panel.base+A.venue.panel.size≤ mouth
  rows : (e₀).oldHosts*chunks (e₀).oldGroups (e₀).oldLanes≤A.venue.panel.size
  lanes : (e₀).oldLanes*max (DepotRAM.totalBits fmt) (e₀).fieldBits≤w/2
  paths : DescentDatedSourcePathDirectory.Fits (nativeBanks (e₀).oldHosts (e₀).groups (e₀).lanes (fmt).degree (v.donorEnd floor))
    (e₀).oldHosts (breadth (fmt).degree) (v.operandPathStart floor) w
  ends : (v.operandRanks floor).endpoints.Fits w (v.operandRankStart floor)
  ranks : (v.operandRanks floor).localRank.Fits w (v.operandRankStart floor)
  ceiling : high₀<2^w

variable {w:ℕ} (room:v.OperandHeaderRoom floor A match_ refs orig w)
private theorem headerOrder : oldHeader≤high₀:=(Nat.le_add_right _ _).trans (Nat.le_add_right ..)
private theorem mouthOrder : mouth≤oldHeader:=by
  have one : mouth≤v.operandPathStart floor:=by rw [operandPathStart,DescentDatedOperandPages.affine];exact Nat.le_add_right ..
  have two : v.operandPathStart floor≤v.operandRankStart floor:=(Nat.le_add_right ..).trans (end_le ..)
  exact one.trans (two.trans (Nat.le_add_right ..))

private theorem earlyOrder : vec≤ mouth:=by
  have p : route≤ports₀:=by rw [v.originPort_span];exact Nat.le_add_right ..
  exact (v.vector_before floor).trans (p.trans (Nat.le_add_right ..))

include room in
private theorem vectorRoom : vec<2^w:=
  (v.earlyOrder floor).trans_lt ((v.mouthOrder floor).trans_lt ((v.headerOrder floor).trans_lt room.ceiling))

local notation "chip" => A.chip_fits v floor room.inlet match_
local notation "mount" => v.mountPhase floor (A.chipBank v floor) chip (v.vectorRoom floor A match_ refs orig room)
local notation "gather" => refs.phase w vec
local notation "both" => v.originAndMouth floor w A match_ v.operandShortBits orig
local notation "early" => v.operandEarlyPhase floor w A

def toOperandHeaders : NativePhase w:=
  ((((A.inlet v floor w).seq mount).seq gather).seq both).seq early

private theorem operandDictionaryStep (m:Memory w) (space:high₀<2^w) :
    Step oldHeader high₀ (v.operandHeaderPhase floor w) m:=by
  let one:=previousHeaderPhase (v.resolver.size+2) v.resolver.nodes v.resolver.lanes oldHeader w
  let two:=previousHeaderPhase v.bornBook.bits v.resolver.nodes v.resolver.lanes (v.operandMouthHeaderStart floor) w
  have lo : oldHeader≤v.operandMouthHeaderStart floor:=Nat.le_add_right ..
  have hi : v.operandMouthHeaderStart floor≤high₀:=Nat.le_add_right ..
  have first:=ScalarOperand.header_dictionary (v.resolver.size+2) v.resolver.nodes v.resolver.lanes oldHeader m (hi.trans_lt space)
  have second:=ScalarOperand.header_dictionary v.bornBook.bits v.resolver.nodes v.resolver.lanes
    (v.operandMouthHeaderStart floor) (one.image m) space
  have l : Step oldHeader (v.operandMouthHeaderStart floor) one m:=
    ⟨lo,first.1,ROM.frame _ _ oldHeader m⟩
  have r : Step (v.operandMouthHeaderStart floor) high₀ two (one.image m):=
    ⟨hi,second.1,ROM.frame _ _ _ _⟩
  exact l.thenStep r

theorem operand_header_frames (m:Memory w) :
    Step low₀ high₀ (v.toOperandHeaders floor A match_ refs orig room) m ∧
    (v.vectorStart floor≤v.operandHeaderEnd floor ∧ ∀a,a<v.vectorStart floor→
      (v.toOperandHeaders floor A match_ refs orig room).image m a=A.mountedTape v floor m a):=by
  let inlet:=A.inlet v floor w
  let start:=inlet.image m
  let mounted:=(mount).image start
  let first:=(gather).image mounted
  let shift:=v.originPrefix floor v.operandShortBits w orig
  let middle:=shift.image first
  let endMouth:=v.originPrefixMouth floor w A match_
  let dealt:=endMouth.image middle
  let before:=v.operandBeforeHeaders floor w A
  have one:=A.inlet_any v floor room.inlet m
  have lo : low₀≤v.refsStart floor:=Nat.le_add_right ..
  have order:=v.mount_order floor
  have l : Step low₀ (v.refsStart floor) inlet m:=⟨lo,one.1,fun t outside=>
    one.2 t (outside.imp_right (match_.atRefs.le.trans ·))⟩
  have mountRun:=v.mount_run floor (A.chipBank v floor) start chip (v.vectorRoom floor A match_ refs orig room)
  have b : Step (v.refsStart floor) vec mount start:=⟨order.1.trans order.2,mountRun.1,mountRun.2.2.1⟩
  have gathered:=refs.any vec mounted room.gather
  have g : Step vec route gather mounted:=⟨v.vector_before floor,gathered.1,gathered.2⟩
  have p : route≤ports₀:=by rw [v.originPort_span];exact Nat.le_add_right ..
  have q : ports₀≤ mouth:=Nat.le_add_right ..
  have endRoom : mouth<2^w:=(v.mouthOrder floor).trans_lt ((v.headerOrder floor).trans_lt room.ceiling)
  have origin:=v.originPrefix_run floor v.operandShortBits w orig first room.masks (q.trans_lt endRoom)
  have o : Step route ports₀ shift first:=⟨p,origin.1,origin.2⟩
  have old : (A.chipBank v floor).Fits w ports₀:=
    ⟨(chip).1,(chip).2.1,(chip).2.2.trans ((order.1.trans order.2).trans ((v.vector_before floor).trans p))⟩
  have mouths:=v.originPrefixMouth_any floor A match_ middle old room.group
    room.gather.lanes room.gather.radix room.mouths endRoom
  have f : Step ports₀ mouth endMouth middle:=⟨q,mouths.1,mouths.2⟩
  have last:=v.before_headers_any floor A dealt room.panel room.rows room.lanes room.paths room.ends room.ranks
    ((v.headerOrder floor).trans_lt room.ceiling)
  have dict:=v.operandDictionaryStep floor (before.image dealt) room.ceiling
  have tail:=((g.thenStep (o.thenStep f)).thenStep (last.thenStep dict))
  exact ⟨(((l.thenStep b).thenStep g).thenStep (o.thenStep f)).thenStep (last.thenStep dict),
    tail.order,fun a low=>tail.frame a (.inl low)⟩

theorem toOperandHeaders_step (m:Memory w) :
    Step low₀ high₀ (v.toOperandHeaders floor A match_ refs orig room) m:=by
  exact (v.operand_header_frames floor A match_ refs orig room m).1

/-- Preserve an actual candidate-field read at the common signed bank, across every later header write. -/
theorem retained_header_source (m:Memory w) (expr:Expr) {H G M b:ℕ} (values:Fin H→Fin G→Cell b)
    (fits:expr.Fits w low₀) (seen:Source expr values M m):
    expr.Fits w high₀ ∧ Source expr values M ((v.toOperandHeaders floor A match_ refs orig room).image m):=by
  have held:=v.toOperandHeaders_step floor A match_ refs orig room m
  exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ held.order fits,fun r=>
    (ProtocolRAM.eval_below expr _ m _ fits (fun j h=>held.frame j (.inl h))).trans (seen r)⟩
end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentSIMDLookup DescentRawCablePanel DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1600000
set_option maxRecDepth 6000
variable {F P : Type} [Field F] (v:PhysicalOrdinary F P)
local notation "phys" => v.withIssuedSigned
local notation "s₀" => (phys).signed
local notation "e₀" => (phys).material
variable (floor:ℕ) (input:DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (count parts adj:Bank) {w:ℕ} (m:Memory w)
local notation "head" => PriorHeader.phase v.area.H (s₀).groups (s₀).lanes (s₀).degree ((phys).donorEnd floor) adj w
local notation "dir" => PriorHeader.reverseRank v.area.H (s₀).groups (s₀).lanes (s₀).degree ((phys).donorEnd floor)
local notation "after" => (v.signedReturn floor input count parts adj w).image m
local notation "src" => (⟨count,input.roster,input.hubs⟩:DescentOrdinaryVenueReturn.Sources)
variable (A : v.withIssuedSigned.ArgumentEntry) (match_ : A.Match v.withIssuedSigned floor) (refs : v.withIssuedSigned.SourceReferences) (orig : v.withIssuedSigned.SourceMasks)
local notation "start" => (phys).materialStart floor
local notation "stop" => (phys).materialEnd floor

/-- Every original post-match donor word is still read at its original address
after the signed return, source gathering, and both operand dictionary writes. -/
theorem material_at_operand_headers (room:(phys).OperandHeaderRoom floor A match_ refs orig w)
    (cash:(phys).SignedRoom floor w) (mat:(phys).MaterialRoom start parts dir w)
    (venues:DescentOrdinaryVenueReturn.Room src stop v.area.H v.area.D v.venue.hosts v.venue.degree w)
    (marks:(phys).MarkRoom floor input w) :
    ∀a,a<(e₀).endAddress start →
      ((phys).toOperandHeaders floor A match_ refs orig room).image after a =
        ((phys).materialAt start parts ((phys).operandRanks floor).reverseRank w).image ((head).image m) a :=by
  have old:=v.signed_predecessor_frames floor input count parts adj m mat venues marks
  have sealed:=(phys).signed_any floor w v.issuedSignedChart cash ((v.signedPredecessor floor input count parts adj w).image m)
  have later:=(phys).toOperandHeaders_step floor A match_ refs orig room after
  intro a before
  have first:a<(phys).markEnd floor:=before.trans_le cash.material
  have «until»:a<(phys).signedEnd floor:=first.trans_le ((s₀).room _)
  exact (later.frame a (.inl «until»)).trans ((sealed.2 a (.inl first)).trans (old.2.1 a before))

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
