import OAI.Hierarchy.DescentPostedResetSevenArchive
import OAI.Hierarchy.DescentResetReachedNodeMetadata

namespace OAI
/-! # Operand headers, spans, census and primitive roles on one reached reset -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentDatedPriorOperand DescentPackedColony DescentPackedZip
open DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentPrimitivePalette RegisterTimeline
open DescentPacking.PackedMatch.Local.Stage
open DescentColonies DescentDatedNodeMetadata DescentOperandStateBanks DescentOperandCandidateLookup DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "A" => (v).receiver
local notation "s" => u.operand
local notation "start" => (v).sheetsStart b
local notation "plan" => (v).linkedRankInputs u.sectors start
local notation "rendered" => (v).renderFromRanks plan b
local notation "ports" => reset a floor u
local notation "head" => a.throughPublishedRoots u.shape floor u.count u.hub u.g u.Y u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits
local notation "ht" => a.throughPublishedTicks u.shape floor u.count u.hub u.g u.Y u.roots u.book u.sourceRows u.oldDegree w u.bookFits
local notation:max "acted" m:arg actorMem:arg => ((head).seq ((v).actor.actorBody u.actor ((v).middle.stop b) w)).Exec m actorMem
  (ht+(v).actor.actorTicks u.actor ((v).middle.stop b) w)



variable {F P:Type} [Field F] [Fintype P] {d:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F}
  {q ε:ℝ} {S:DescentCompiler.AtomSchedule} {k age grain degree wire hist p R seedGrain:ℕ}
  (r:Reached W G q ε S k age grain degree wire hist) (B:BitDescription W) (number:Local B)
  (places:RangeRoom (reset a floor u) r B) (shape:WorldShape p R B) (hp:0<p) (pin:P→ℕ)
  (op:RotorSpec) (label:NodeOrder.All B→Label G hist seedGrain op)
local notation "L" => (ports).rangeLayout
local notation "R₁" => (v).rangeLayout
local notation "c₀" => (ports).metadataChart
local notation "c₁" => (v).metadata.chart
local notation "slot" => slotAt ports r B number places
local notation "flags" => archiveFlag r B number ports places
local notation "ptr" => Reached.argumentPointer r B number shape hp pin (ports).argumentsPerNode
local notation:max "argc" y:arg => (DescentRetainedRangeDigits.occurrences (shape.sites (y:NodeOrder.All B).1) y.2).length
local notation:max "reg" m:arg => rangeRegister ports r B number places.capacity places.hosts places.groups places.radix places.positive m

variable (ok : u.Ready) (small : 2*a.successor.receiver.candidates<2^a.successor.receiver.queryBits)
    (axes : (reset a floor u).rangeLayout=a.successor.rangeLayout)
    (actorMem : Memory w) (choice : ∀i,OrdinalRead u ok small actorMem i)

def SevenHeaders : Prop :=
  ∀(x:Fin (L).blocks)(j:Fin (L).operands)(f:Fin 4) h g n y,slot x n h g=some y → j.val<argc y →
        ((choice ((v).operandOrdinal (s) (f.castLE (by decide:4≤7)) ((j.cast (congrArg Layout.operands axes)).cast ok.slots.symm)
          (x.cast (congrArg Layout.blocks axes)) ((n.cast (congrArg Layout.nodes axes)).cast ok.nodes.symm))).amount
          (h.cast (congrArg Layout.hosts axes)) (g.cast (congrArg Layout.groups axes))).val=(ptr y j.val).header f

def SevenSpans : Prop :=
  ∀(x:Fin (L).blocks)(j:Fin (L).operands)(f:Fin 3) h g n y,slot x n h g=some y → (j.val<argc y ∨ f=2) →
        ((choice ((v).operandOrdinal (s) (DescentRetainedRangeDigits.page f) ((j.cast (congrArg Layout.operands axes)).cast ok.slots.symm)
          (x.cast (congrArg Layout.blocks axes)) ((n.cast (congrArg Layout.nodes axes)).cast ok.nodes.symm))).amount
          (h.cast (congrArg Layout.hosts axes)) (g.cast (congrArg Layout.groups axes))).val=DescentRetainedRangeDigits.atSlot (shape.sites y.1) y.2 j.val f

def PrimitiveRolesAt (out : Memory w) : Prop :=
  ∀x:Fin (2^(ports).venue.k),Reads ((ports).archive.roles.bank x.val) (fun h g=>
      encode (printedBits G hist seedGrain op) (ports).nodes (fun n=>(slot x n h g).elim 0
        (fun y=>token G hist seedGrain op (label y)))) (ports).roleLanes out

variable (chart : (reset a floor u).metadataChart=a.successor.metadata.chart)
local notation "bank" => (v).metadata
local notation "rawX" x => (x : Fin (c₁).blocks).cast (congrArg Chart.blocks chart).symm
local notation "rawN" n => (n : Fin (c₁).nodes).cast (congrArg Chart.nodes chart).symm
local notation "rawH" h => (h : Fin (c₁).hosts).cast (congrArg Chart.hosts chart).symm
local notation "rawG" g => (g : Fin (c₁).groups).cast (congrArg Chart.groups chart).symm
local notation "at_" x:arg n:arg h:arg g:arg => slot (rawX x) (rawN n) (rawH h) (rawG g)

section
-- The constructor's equality lemmas compare two abstract dates. Keep their physical
-- layout opaque while Lean generates those lemmas.
attribute [local irreducible] reset

/-- Every source refers to an intermediate or output memory of the same dated program. -/
structure ResetArchiveCertificate (z : u.FinalInputs) (m mid out : Memory w) where
  actorMem : Memory w
  issued : acted m actorMem
  choice : ∀i, OrdinalRead u ok small actorMem i
  headers : SevenHeaders u r B number places shape hp pin ok small axes actorMem choice
  spanFields : SevenSpans u r B number places shape ok small axes actorMem choice
  sp : Fin (c₁).blocks→Fin (c₁).nodes→Fin u.operand.slots→Fin (c₁).hosts→Fin (c₁).groups→Cell (bank).spanBits
  hosts : (ports).operandHosts=S.hostSize age
  paid : ∀x, Source ((PhysicalReset.FinalInputs.paid u) x) (fun h g=>
      Census.count r.placement (Equiv.refl _) (r.vertex.trans (Fin.castLEEmb r.valid.host)) (bank).paidBits
        ((rawH h).cast hosts) ((rawG g).cast places.groups.symm)
        ((rawX x).cast (congrArg (2^·) places.radix.symm))) (c₁).lanes (z.venueImage mid)
  spans : ∀x n j,Source (z.spans x n j) (sp x n j) (c₁).lanes (z.venueImage mid)
  width : ∀x n j h g,(sp x n j h g).val=(at_ x n h g).elim 0
      (fun y=>DescentRetainedRangeDigits.atSlot (shape.sites y.1) y.2 j.val 2)
  roles : PrimitiveRolesAt u r B number places op label out

end

omit [Fintype P] in
theorem ResetArchiveCertificate.result (z : u.FinalInputs) (fits : z.Room) {m mid out : Memory w}
    (before : u.throughOperandDate.Runs m mid) (ran : (PhysicalReset.date z).Runs m out)
    (coeff : u.operand.coeff=(v).nodeBits)
    (blocks : (c₁).blocks≤2^(v).venue.next.k) (positive : 0<age)
    (bound : ∀y : NodeOrder.All B,argc y≤u.operand.slots)
    (mass : r.placement.wire*(r.placement.z*G.b)*r.placement.cap<2^(bank).paidBits)
    (src : ResetArchiveCertificate u r B number places shape hp pin op label ok small axes chart z m mid out) :
    ArchiveRead ports r B number places shape op label ptr flags out :=by
  obtain ⟨amount,count,bounded,live,counts,ranges,countAt,arityAt⟩:=
    reset_reached_metadata u r B number places shape chart z ok fits mid blocks src.hosts positive hp bound mass
      src.sp src.paid src.spans src.width
  exact reset_from_posted_seven u r B number places shape hp pin op label z ok fits before ran coeff small axes chart
    src.actorMem src.issued src.choice src.headers src.spanFields amount src.sp count bounded live counts ranges
    countAt arityAt src.roles

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
