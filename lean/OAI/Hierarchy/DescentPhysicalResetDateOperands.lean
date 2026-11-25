import OAI.Hierarchy.DescentPhysicalOperandSelection
import OAI.Hierarchy.DescentDatedRetainedTicket
import OAI.Hierarchy.DescentTerminalExecUnique
import OAI.Hierarchy.DescentPhysicalOperandMenu
import OAI.Hierarchy.DescentPhysicalResetHeadFrame
import OAI.Hierarchy.DescentPhysicalResetActors
import OAI.Hierarchy.DescentPhysicalResetOriginalSeries
import OAI.Hierarchy.DescentStemProjectedRegister
import OAI.Hierarchy.DescentPhysicalResetSceneInputs
import OAI.Hierarchy.DescentPhysicalResetCandidateReturn
import OAI.Hierarchy.DescentResetCompactedCandidates
import OAI.Hierarchy.DescentContactOutputIssued
import OAI.Hierarchy.DescentPhysicalResetMixedSources
import OAI.Hierarchy.DescentPhysicalStemOperand
import OAI.Hierarchy.DescentResetTrunkOperand
import OAI.Hierarchy.DescentPublicDateMachine

namespace OAI
/-! One dated reset body from the previous packed graph to its ranked operand and node books. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.Chronology DescentFallbackPeriod DescentSIMDLookup DescentPackedColony
open DescentResetFieldAssembler ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable (a : PhysicalReset) (floor w : ℕ)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "A" => (v).receiver
local notation "s" => (v).sheets
local notation "rbase" => ((v).remap b).endAddress

structure SectorDirectory where
  stems : ℕ
  pageBits : ℕ
  count : (A).candidates=CandidateSheet.size stems (s).contacts (s).privates
  ports : Ports 4
  before : ℕ→ℕ→Bool
  sourceSlot : Fin (A).candidates→ℕ→ℕ

structure DateInputs where
  shape : a.StencilShape
  count : Bank
  hub : Bank
  src : Bank
  g : ℕ
  Y : ℕ
  sourceRows : ℕ
  oldDegree : ℕ
  roots : a.RootInputs
  atlas : a.Atlas
  bookFits : (a.rootPhase shape floor count hub g Y roots w).PreparedFits (atlasBook atlas shape floor count hub g Y roots w)
  actorFit : ActorFit atlas roots
  earlier : (v).OriginalOperands b
  sceneFits : (v).front.SceneRoom ((v).actorEnd b) ((v).issuedScene b earlier) w
  number : (s).OriginalInputs
  directory : a.SectorDirectory
  operandBlocks : (v).receiver.blocks=(v).setup.placement.blocks
  operandChannels : (v).receiver.fields=((7*(v).setup.retained.args)*(v).receiver.blocks)*(v).setup.retained.nodes
  menu : OperandMenu atlas roots
  degree : ℕ

variable {a floor w} (u : a.DateInputs floor w)
/-- All carried, new private, and new public operand selectors refer to the original
dated tape. A retained arrival uses its sibling's original ticket on the same tape. -/
def DateInputs.rawOperands : (v).OperandInputs :=
  u.menu.renderer floor u.shape u.count u.hub u.g u.Y u.operandBlocks u.operandChannels
    ((v).retainedHub b) ((v).retainedTicket b)

def DateInputs.operand : (v).OperandInputs :=
  {u.rawOperands with kept:=fun i=>(v).keptValue b (u.rawOperands.kept i)}

def DateInputs.book := atlasBook u.atlas u.shape floor u.count u.hub u.g u.Y u.roots w
def DateInputs.actor := atlasActors u.atlas u.shape floor u.count u.hub u.g u.Y u.roots w u.actorFit

local notation "root" => a.rootPhase u.shape floor u.count u.hub u.g u.Y u.roots w
local notation "actorBase" => (v).middle.stop b
local notation "head" => a.throughPublishedRoots u.shape floor u.count u.hub u.g u.Y u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits
local notation "ht" => a.throughPublishedTicks u.shape floor u.count u.hub u.g u.Y u.roots u.book u.sourceRows u.oldDegree w u.bookFits
local notation "actors" => (v).actor.actorBody u.actor actorBase w
local notation "atime" => (v).actor.actorTicks u.actor actorBase w
local notation "scene" => (v).front.trunkScene ((v).actorEnd b) ((v).issuedScene b u.earlier) u.sceneFits
local notation "S₀" => (v).sheetsStart b

namespace DateInputs
def bank :=u.menu.banks u.shape floor u.count u.hub u.g u.Y w
def laws :=u.menu.tables
local notation "front₀" => (v).front
local notation "peer₀" => (front₀).peer
local notation "cut₀" => (v).actorEnd b
local notation "old₀" => (v).issuedScene b u.earlier
local notation "donor₀" => (front₀).donorStart cut₀
local notation "mass₀" => (v).trunkEnd b
local notation "join₀" => (v).massEnd b

local notation "jointPhase" => (v).jointPhase b u.earlier w
local notation "massPhase" => (v).contactShape.issuedProgram donor₀ mass₀ (old₀).donor w
local notation "mticks" => (v).contactShape.issuedTicks donor₀ mass₀ (old₀).donor

local notation "pr₀" => (v).privateShape
local notation "oldPitch" => (front₀).contactLayout cut₀
local notation "pcode" => (pr₀).code ((v).jointEnd b) oldPitch u.earlier.pages w
local notation "pclock" => (pr₀).ticks ((v).jointEnd b) oldPitch u.earlier.pages

def jointRank (_ : a.DateInputs floor w) (j : ℕ) (i : Fin 5) : DescentResetDenseOperand.Operand :=
  Fin.lastCases ((v).actualTarget b j)
    (fun h=>.compact ((v).peerJoint b h)) i

def masked : DescentResetDenseOperand.MaskedDate :=
  {first:=(v).privateEnd b,jobs:=(s).jobs,lanes:=(s).lanes,hosts:=(s).hosts,groups:=(s).groups,
   sparseHosts:=(v).front.peer.hosts,field:=(s).metaBits,count:=((v).actor.directory actorBase).count,
   inverse:=((v).actor.directory actorBase).inverse,rank:=u.jointRank,raw:=(v).actualRaw b}
theorem masks_end : u.masked.endAddress=(s).metaEnd rbase:=rfl

def markRead (x offset : ℕ) : Expr :=
  .lookup (u.masked.output (x*((s).contacts+(s).privates)+offset)) .row

theorem measured_mark_fits (x j : ℕ) (job : x*((s).contacts+(s).privates)+j<(s).jobs)
    (roof : u.masked.endAddress<2^w) : (u.markRead x j).Fits w u.masked.endAddress :=
  ⟨u.masked.mixed.masks.output_fits _ job roof,trivial⟩

/-- All four disjoint families read the actual preceding physical publications. -/
def sectorHeader (x : ℕ) : CandidateSheet.Sector u.directory.stems (s).contacts (s).privates→Expr
  | .inl j=>(v).front.stemOperand ((v).actorEnd b) x j.val
  | .inr (.inl _)=>(v).front.trunkOperand ((v).actorEnd b) x
  | .inr (.inr (.inl j))=>u.markRead x j.val
  | .inr (.inr (.inr j))=>u.markRead x ((s).contacts+j.val)

def sectors : (v).Sectors where
  stems:=u.directory.stems
  contacts:=(s).contacts
  privates:=(s).privates
  pageBits:=u.directory.pageBits
  count:=u.directory.count
  ports:=(v).rankPorts b
  before:=u.directory.before
  sourceSlot:=u.directory.sourceSlot
  header x j:=u.sectorHeader x.val j
  original x j:=.lookup (DescentResetOriginalSlots.bank ((s).original rbase) (s).rows (s).candidates x.val
    ((CandidateSheet.index u.directory.stems (s).contacts (s).privates) j).val) .row

/-- The three mutable registers and the saved matrix determine every numbered stem. -/
def stemRegisters (x j : ℕ) : Fin 6→Expr :=
  let plan:=(s).stemSources
  let cap:=a.c/2
  if hx:x<(front₀).blocks ∧ x<2^plan.coord.fine then
    if hj:j<(front₀).signedQueries ∧ j<DescentResetStemPackedIssue.count (2^plan.coord.residual) cap then
      let lo:=((DescentResetStemPackedIssue.ordinal (2^plan.coord.residual) cap).symm ⟨j,hj.2⟩).2.1
      let old:=DescentResetStemPackedIssue.Mixed.Projected.signedRegister
        (D:=(peer₀).oldDegree) (f:=(front₀).stemField) (Q:=(front₀).signedQueries)
        ((front₀).parentEnd cut₀) ((front₀).parent cut₀).base (front₀).oldTicketCount
        (peer₀).oldHosts (front₀).newHosts (peer₀).groups (front₀).blocks
        (front₀).oldLanes (peer₀).lanes ⟨x,hx.1⟩ ⟨j,hj.1⟩
      let saved:=⟨(a.stencilPhase u.shape floor u.count u.hub u.g u.Y).saved,0⟩
      plan.stem ((s).metaEnd rbase) saved ⟨x,hx.2⟩ lo old ((v).peerAux b 3)
        ((front₀).stemOperand cut₀ x j)
    else fun _=>.lit 0
  else fun _=>.lit 0

/-- The early original-number programs reuse the same compact trunk, contact and private masks. -/
def numbered : (s).OriginalInputs :=
  { u.number with
    stem := fun x j => u.stemRegisters x.val j.val
    privateMeta := fun x j => u.markRead x.val ((s).contacts+j.val)
    sources := { u.number.sources with
      «meta» := fun x j => Fin.cases ((v).front.trunkOperand ((v).actorEnd b) x.val) (fun j => u.markRead x.val j.val) j } }


local notation "num" => u.numbered.code rbase w
local notation "exit₀" => (v).sheetsReturn u.sectors S₀ u.operand b u.degree u.bank u.laws w
local notation "exitTime" => (v).sheetsTime u.sectors S₀ u.operand b u.degree u.bank u.laws w

def throughOperands : Procedure w :=
  (((((head).seq actors).seq (scene).program).seq massPhase).seq (jointPhase).program).seq
    ((((pcode).seq (u.masked.code w)).seq num).seq exit₀)

def throughOperandTicks : ℕ :=
  ((((ht+atime)+(scene).ticks)+mticks)+(jointPhase).ticks)+(((pclock+u.masked.ticks)+u.numbered.time rbase)+exitTime)

def throughOperandDate : DateCode w := .reset u.throughOperands u.throughOperandTicks

/-- The two actual directory banks and every issued rank/mask lookup lie below the relay. -/
theorem genuine_mask_previous (joint : (v).JointRoom b u.earlier w) (roof : u.masked.endAddress<2^w) :
    u.masked.mixed.Previous w := by
  have below:= (v).receipt_order b
  have prior : (v).massEnd b≤(v).privateEnd b:=below.1.trans below.2
  have relay:=u.masked.ordered
  have fits:= (v).mixed_term_room b ((relay.1.trans relay.2).trans_lt roof)
  have up {q : Bank} (h : q.Fits w ((v).massEnd b)) : q.Fits w ((v).privateEnd b):=
    ⟨h.1,h.2.1,h.2.2.trans prior⟩
  apply u.masked.prior (u.masked.relay.book_fits _ _ (up joint.measured.count)
    (up joint.measured.inverse) (relay.2.trans_lt roof))
  · intro j _ i
    refine Fin.lastCases ?_ (fun k=>?_) i
    · simpa only [masked,jointRank,Fin.lastCases_last] using fits.1 j
    · simpa only [masked,jointRank,Fin.lastCases_castSucc,DescentResetDenseOperand.Operand.term] using
        ProtocolRAMGeneratedWrite.fits_mono _ below.2 ((v).peerJoint_fits b u.earlier joint
          ((below.2.trans (relay.1.trans relay.2)).trans_lt roof) k)
  · exact fun j _ i=>fits.2 j i

/-- Numeric fits and address intervals, fixed before the incoming memory is supplied. -/
structure Ready : Prop where
  prime : a.PrimeRoom floor u.src u.count u.sourceRows u.oldDegree w
  stencil : (a.stencilPhase u.shape floor u.count u.hub u.g u.Y).Room w
  rootEnd : (root).preparedEnd u.book=actorBase
  actor : (v).actor.Ready u.actor actorBase w
  trunk : (v).trunkEnd b<2^w
  donors : ((front₀).donor.markers donor₀ (v).contactShape.shapes (v).contactShape.markerBits).endAddress≤ mass₀
  mass : join₀<2^w
  projectionLanes : 0<(v).contactShape.batch
  projectionBlocks : 0<(v).contactShape.blocks
  joints : (v).JointRoom b u.earlier w
  packed : (v).jointEnd b<2^w
  pages : ∀ side field, (u.earlier.pages side field).Fits w ((v).jointEnd b)
  privates : (v).privateEnd b<2^w
  masked : u.masked.endAddress<2^w
  numbers : u.numbered.Room rbase w
  full : (v).finalEnd b<2^w
  matched : DescentResetCandidatePair.endAddress S₀ (A).blocks
    (CandidateSheet.size u.sectors.stems u.sectors.contacts u.sectors.privates) u.sectors.pageBits=(v).candidateEnd b
  header : ∀x j,(u.sectors.header x j).Fits w S₀
  original : ∀x j,(u.sectors.original x j).Fits w S₀
  rows : (A).hosts*chunks (A).groups (A).lanes≤2^u.sectors.pageBits
  width : (A).signedBits=(v).assemblerBits
  nodes : u.operand.nodes=(v).nodes
  slots : u.operand.slots=(v).argumentSlots
  rankPorts : (v).RankPortRoom b w
  ranks : ((v).rankBook ((v).linkedRankInputs u.sectors S₀) b).Previous w
  controls : (v).ControlRoom b u.bank w
  placed : (v).setup.Ready u.bank w ((v).operandFloor b)
  «fields» : (v).OperandEarly u.operand ((v).renderFromRanks ((v).linkedRankInputs u.sectors S₀) b) w b
  ordered : floor≤actorBase ∧ actorBase≤(v).actorEnd b ∧ (v).actorEnd b≤(v).trunkEnd b ∧
    (v).trunkEnd b≤(v).massEnd b ∧ (v).massEnd b≤(v).jointEnd b ∧ (v).jointEnd b≤(v).privateEnd b ∧ (v).privateEnd b≤u.masked.endAddress ∧ u.masked.endAddress≤S₀ ∧ S₀≤(v).finalEnd b

/-- Input to the paired candidate sheets after the actual actor, mass, join, private and numbering passes. -/
def sheetsEntry (ok : u.Ready) (actorMem : Memory w) :=
  let trunk:=(scene).image actorMem
  let mass:=(v).contactShape.issuedImage donor₀ mass₀ (old₀).donor trunk
  let joint:=(jointPhase).image mass
  let safe:=(v).private_inputs_fit b u.earlier ok.pages ok.privates
  let private_:=(v).privatePhase b u.earlier ok.projectionLanes ok.projectionBlocks safe ok.privates
  u.numbered.output rbase (u.masked.image (private_.image joint))

def sheetsResult (ok : u.Ready) (actorMem : Memory w) :=
  (v).sheetsMemory u.sectors S₀ u.operand b u.degree u.bank u.laws (u.sheetsEntry ok actorMem)

/-- Frames the actual attained actor census before the trunk and all later scans. -/
theorem run_to_sheets_from_actors (ok : u.Ready) (m m₂ : Memory w)
    (t₁₂ : ((head).seq actors).Exec m m₂ (ht+atime)) (c₁₂ : CheapCode ((head).seq actors)) :
    let dst:=u.sheetsResult ok m₂
    u.throughOperandDate.Runs m dst ∧ u.throughOperandDate.cheap ∧
      ∀z,z<(v).actorEnd b ∨ (v).finalEnd b≤z→dst z=m₂ z := by
  obtain ⟨t₃,h₃⟩:=(v).front.trunkScene_any ((v).actorEnd b) ((v).issuedScene b u.earlier) u.sceneFits m₂ ok.trunk
  let m₃:=(scene).image m₂
  obtain ⟨massRun,massCheap,massFrame⟩:=(v).contactShape.actual donor₀ mass₀
    (old₀).donor u.sceneFits.donor ok.donors ok.mass ok.projectionLanes ok.projectionBlocks m₃
  let massOut:=(v).contactShape.issuedImage donor₀ mass₀ (old₀).donor m₃
  obtain ⟨joinRun,joinFrame⟩:=(v).joint_any b u.earlier massOut ok.joints ok.packed
  let mid:=(jointPhase).image massOut
  have privateFits:=(v).private_inputs_fit b u.earlier ok.pages ok.privates
  let post:=(v).privatePhase b u.earlier ok.projectionLanes ok.projectionBlocks privateFits ok.privates
  obtain ⟨pRun,pKeep⟩:=(v).private_any b u.earlier mid ok.projectionLanes ok.projectionBlocks privateFits ok.privates
  obtain ⟨t₄,c₄,h₄⟩:=u.masked.any (post.image mid) (u.genuine_mask_previous ok.joints ok.masked) ok.masked
  obtain ⟨t₅,c₅,h₅⟩:=u.numbered.any rbase (u.masked.image (post.image mid)) ok.numbers
  obtain ⟨t₆,h₆,c₆⟩:=(v).sheets_any u.sectors S₀ u.operand b u.degree u.bank u.laws
    (u.numbered.output rbase (u.masked.image (post.image mid))) ok.matched ok.full ok.header ok.original
    ok.rows ok.width ok.nodes ok.slots ok.rankPorts ok.ranks ok.controls ok.placed ok.fields
  let prefixProgram := (head).seq actors
  let trunkProgram := prefixProgram.seq (scene).program
  let massProgram := trunkProgram.seq massPhase
  let leftProgram := massProgram.seq (jointPhase).program
  let maskProgram := (pcode).seq (u.masked.code w)
  let numberProgram := maskProgram.seq num
  let rightProgram := numberProgram.seq exit₀
  let maskedMem := u.masked.image (post.image mid)
  let numberedMem := u.numbered.output rbase maskedMem
  have trunkRun : trunkProgram.Exec m m₃ ((ht+atime)+(scene).ticks) :=
    @Procedure.Exec.then w prefixProgram (scene).program m m₂ m₃ (ht+atime) (scene).ticks @t₁₂ @t₃
  have throughMass : massProgram.Exec m massOut (((ht+atime)+(scene).ticks)+mticks) :=
    @Procedure.Exec.then w trunkProgram massPhase m m₃ massOut ((ht+atime)+(scene).ticks) mticks @trunkRun @massRun
  have leftRun : leftProgram.Exec m mid ((((ht+atime)+(scene).ticks)+mticks)+(jointPhase).ticks) :=
    @Procedure.Exec.then w massProgram (jointPhase).program m massOut mid (((ht+atime)+(scene).ticks)+mticks)
      (jointPhase).ticks @throughMass @joinRun
  have throughMask : maskProgram.Exec mid maskedMem (pclock+u.masked.ticks) :=
    @Procedure.Exec.then w pcode (u.masked.code w) mid (post.image mid) maskedMem pclock u.masked.ticks @pRun @t₄
  have throughNumber : numberProgram.Exec mid numberedMem ((pclock+u.masked.ticks)+u.numbered.time rbase) :=
    @Procedure.Exec.then w maskProgram num mid maskedMem numberedMem (pclock+u.masked.ticks) (u.numbered.time rbase) @throughMask @t₅
  have rightRun : rightProgram.Exec mid (u.sheetsResult ok m₂) (((pclock+u.masked.ticks)+u.numbered.time rbase)+exitTime) :=
    @Procedure.Exec.then w numberProgram exit₀ mid numberedMem (u.sheetsResult ok m₂)
      ((pclock+u.masked.ticks)+u.numbered.time rbase) exitTime @throughNumber @t₆
  refine ⟨@Procedure.Exec.then w leftProgram rightProgram m mid (u.sheetsResult ok m₂)
    ((((ht+atime)+(scene).ticks)+mticks)+(jointPhase).ticks)
    (((pclock+u.masked.ticks)+u.numbered.time rbase)+exitTime) @leftRun @rightRun,?_,?_⟩
  · exact @cheap_seq w leftProgram rightProgram
      (@cheap_seq w massProgram (jointPhase).program
        (@cheap_seq w trunkProgram massPhase
          (@cheap_seq w prefixProgram (scene).program @c₁₂ (@(scene).cheap)) @massCheap) (@(jointPhase).cheap))
      (@cheap_seq w numberProgram exit₀
        (@cheap_seq w maskProgram num (@cheap_seq w pcode (u.masked.code w) (@post.cheap) @c₄) @c₅) @c₆)
  obtain ⟨a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉⟩:=ok.ordered
  have mEnd:=u.masks_end
  intro z hz
  exact (h₆ z (by omega)).trans ((h₅ z (by change z<(s).metaEnd rbase ∨ S₀≤z;omega)).trans
    ((h₄ z (by change z<(v).privateEnd b ∨ u.masked.endAddress≤z;omega)).trans
    ((pKeep z (by omega)).trans
    ((joinFrame z (by omega)).trans
    ((massFrame z (by change z<(v).trunkEnd b ∨ (v).massEnd b≤z;omega)).trans
      (h₃ z (by change z < (v).actorEnd b ∨ (v).trunkEnd b ≤ z; omega)))))))

/-- Frames the actual attained actor census before the trunk and all later scans. -/
theorem run_to_operands_from_actors (ok : u.Ready) (m m₂ : Memory w)
    (t₁₂ : ((head).seq actors).Exec m m₂ (ht+atime)) (c₁₂ : CheapCode ((head).seq actors)) :
    ∃dst,u.throughOperandDate.Runs m dst ∧ u.throughOperandDate.cheap ∧
      ∀z,z<(v).actorEnd b ∨ (v).finalEnd b≤z→dst z=m₂ z := by
  exact ⟨u.sheetsResult ok m₂,u.run_to_sheets_from_actors ok m m₂ t₁₂ c₁₂⟩

/-- The prior actor snapshot is witnessed by its original native execution. -/
theorem sheets_result (ok : u.Ready) {m mid : Memory w} (ran : u.throughOperandDate.Runs m mid) :
    ∃m₂,((head).seq actors).Exec m m₂ (ht+atime) ∧ mid=u.sheetsResult ok m₂ := by
  obtain ⟨m₁,t₁,c₁,_⟩:=a.throughPublishedRoots_any_framed u.shape floor u.count u.hub u.g u.Y
    u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits m ok.prime ok.stencil
  obtain ⟨m₂,t₂,c₂,_⟩:=(v).actor.dated_any u.actor actorBase m₁ ok.actor
  have atActors : ((head).seq actors).Exec m m₂ (ht+atime) :=
    @Procedure.Exec.then w head actors m m₁ m₂ ht atime @t₁ @t₂
  have after:=u.run_to_sheets_from_actors ok m m₂ (@atActors) (@cheap_seq w head actors @c₁ @c₂)
  exact ⟨m₂,atActors,exec_unique u.throughOperands m mid (u.sheetsResult ok m₂) (@ran) (@after.1)⟩

/-- Every post-root pass preserves the published root and the measured stencil below it. -/
theorem run_to_operands_from_roots (ok : u.Ready) (m m₁ : Memory w)
    (t₁ : (head).Exec m m₁ ht) (c₁ : CheapCode head) :
    ∃dst,u.throughOperandDate.Runs m dst ∧ u.throughOperandDate.cheap ∧
      ∀z,z<actorBase ∨ (v).finalEnd b≤z→dst z=m₁ z := by
  obtain ⟨m₂,t₂,c₂,h₂⟩:=(v).actor.dated_any u.actor actorBase m₁ ok.actor
  obtain ⟨out,ran,cheap,keep⟩:=u.run_to_operands_from_actors ok m m₂ (@Procedure.Exec.then w head actors m m₁ m₂ ht atime @t₁ @t₂) (@cheap_seq w head actors @c₁ @c₂)
  obtain ⟨a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉⟩:=ok.ordered
  exact ⟨out,ran,cheap,fun i hi=>(keep i (by omega)).trans (h₂ i (by change i<actorBase ∨ (v).actorEnd b≤ i;omega))⟩

theorem run_to_operands (ok : u.Ready) (m : Memory w) :
    ∃dst,u.throughOperandDate.Runs m dst ∧ u.throughOperandDate.cheap ∧
      ∀z,z<floor ∨ (v).finalEnd b≤z→dst z=m z := by
  obtain ⟨m₁,t₁,c₁,h₁⟩:=a.throughPublishedRoots_any_framed u.shape floor u.count u.hub u.g u.Y
    u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits m ok.prime ok.stencil
  obtain ⟨out,ran,cheap,kept⟩:=u.run_to_operands_from_roots ok m m₁ (@t₁) (@c₁)
  have rootFrame : ∀ i, i < floor ∨ actorBase ≤ i → m₁ i = m i := by
    intro i hi
    exact h₁ i (hi.imp_right (fun h => ok.rootEnd.le.trans h))
  obtain ⟨a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉⟩:=ok.ordered
  exact ⟨out,ran,cheap,fun z hz=>(kept z (by omega)).trans (rootFrame z (by omega))⟩

end DateInputs
end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
