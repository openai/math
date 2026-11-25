import OAI.Hierarchy.DescentRegisteredHeaderTables

namespace OAI
/-! Read back all four native pointer digits after the registered instruction. -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open DescentPackedColony DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
set_option hygiene false
namespace DatePorts
variable {F P : Type} [Field F] {G : PoweredGadget F} {S : DescentCompiler.AtomSchedule}
    {d k i z D z' D' wire hist : ℕ} {q ε u : ℝ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {prevWorld : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
    {choice : (T.result he).Choice} {n : Normalize ((T.result he).state choice)}
    {next : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (prior : DatePorts) (ticket : OrdinaryLink prevWorld he T choice n next)
    (op : RotorSpec) (gain tail p f drift degree payload seats root : ℕ)
    (ordinary : ℕ→Dated.Ordinary)
local notation "books" => OrdinaryBooks.atDate G S op gain k i p tail drift degree payload seats prior
local notation "base" => (books).onTicket ticket gain tail p f payload seats prior.venue.lanes prior.io.roster ordinary
local notation "floor" => (base).stageStart root

local notation "v" => ordinaryModel prior ticket op gain tail p f drift degree payload seats root ordinary

local notation "A" => (base).registeredEntry prior floor
local notation "match₀" => (base).registered_match prior floor (Nat.le_max_left prior.argumentsPerNode (S.retainedArgumentsAt G drift))
local notation "sh" => (base).registered_geometry prior floor
local notation "paidSources" => (v).reachedSources floor

variable (w : ℕ) (shelf header : ℕ) (pos : 0<k)
variable (room : OrdinaryCodeRoom prior ticket op gain tail p f drift degree payload seats root ordinary w)
local notation "steps" => (v).issuedSteps root prior (A) room.signed w (match₀) (sh) room.blocks room.paths
  room.slots room.chip room.endFit room.packed room.radix room.funded


local notation "digits" => (v).signedInput floor room.signed
local notation "date₀" => DonorDate.atDate G S gain k i p

variable (exec : OrdinaryExecutionRoom prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header room)
local notation "opOut" => (v).argumentsAfter floor room.result.operands
  (by rw [(v).after_end floor room.result.geometry]; exact room.result.limit)

open DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentPrimitivePalette
open DescentHistoryOrder DescentDatedPriorOperand DescentOperandStateBanks DescentRetainedRangeDigits
open DescentPackedOperand DescentOrdinaryFinal DescentLocalPrivateNames Computability.BorderVNP.Crossing
variable [Fintype P]
local notation "modelWorld" => n.result
local notation "out" => ordinaryPorts prior ticket op gain tail p f drift degree payload seats root ordinary
local notation "coordsB" => (registered_blocks_groups prior ticket op gain tail p f drift degree payload seats root ordinary).1
local notation "coordsG" => (registered_blocks_groups prior ticket op gain tail p f drift degree payload seats root ordinary).2
local notation "layoutEq" => ordinary_range_layout (v) floor coordsB coordsG
local notation "ports" => out
variable (B:BitDescription modelWorld) (number:Local B) (places:RangeRoom out next B)
    {R:ℕ} (shape:WorldShape p R B) (hp:0<p) (pin:P→ℕ)
local notation "args" y:arg => occurrences (shape.sites (y:NodeOrder.All B).1) y.2
local notation "rec₁" u:arg => (shape.sites u).recipe hp
local notation "sx" u:arg => ((Reached.NodeCells.coordinate next u).2.2.cast (congrArg (2^·) places.radix)).cast
  (congrArg Layout.blocks (show (ports).rangeLayout=(v).resolver from layoutEq))
local notation "sh" u:arg => (⟨(Reached.NodeCells.coordinate next u).1.val,places.hosts u⟩:Fin (ports).operandHosts).cast
  (congrArg Layout.hosts (show (ports).rangeLayout=(v).resolver from layoutEq))
local notation "sg" u:arg => ((Reached.NodeCells.coordinate next u).2.1.cast places.groups).cast
  (congrArg Layout.groups (show (ports).rangeLayout=(v).resolver from layoutEq))
local notation "onsite" u:arg => (number u).toEmbedding.trans (Fin.castLEEmb (places.capacity u))
variable («meta»:(v).MetaWords) (old:Books (v).resolver) (jobs:Fin (v).resolver.jobs→DescentDatedPriorOperand.Source (v).resolver)
  (argFit:∀u n,(rec₁ u).arity n≤(v).resolver.operands)
local notation "mouth" u:arg => (v).finalChart.mouths (rec₁ u) (onsite u) (argFit u)
local notation "fragment" u:arg n:arg j:arg => (v).issuedFragment jobs (sx u) (sh u) (sg u) ((mouth u) ⟨n,j⟩)
local notation "expected" => Reached.argumentPointer next B number shape hp pin (v).resolver.operands


variable (dates:ℕ→DateCode w) (m:Memory w)
local notation "sourceMem" => DateCode.history dates m i
local notation "work" => ordinaryMetadata prior ticket op gain tail p f drift degree payload seats root ordinary
  w shelf header pos room exec sourceMem
local notation "meter" => (date₀).counter payload (((date₀).schedule payload seats (v).bitsPerField).rotationEnd prior.io.roster floor) header

include argFit in
omit [Fintype P] in
theorem registered_header_return
    (posted:dates i=ordinaryDate prior ticket op gain tail p f drift degree payload seats root ordinary
      w shelf header pos room)
    (preserved:(meter).endAddr≤(v).finalChart.out ((v).metaEnd floor)) (earlier:header<(meter).endAddr)
    (dated:i<S.length) (previous:prior.argumentsPerNode≤S.retainedArgumentsAt G drift)
    (bitsFit:(v).finalChart.field*(v).resolver.nodes*(v).resolver.lanes≤w)
    (tables:PhysicalOrdinary.HeaderTables (v) floor work)
    (arity:HeaderArity prior ticket op gain tail p f drift degree payload seats root ordinary
      w shelf header pos room exec B number places shape hp dates m)
    (sites:Reached.PointerSites next (v) B number shape hp pin tables.jobs) :
    HeaderRows out next B number places shape expected (DateCode.history dates m (i+1)):=by
  obtain ⟨metadataWords,stored,full,vacant⟩:=arity
  have source:=printed_header_sites prior ticket op gain tail p f drift degree payload seats root ordinary
    B number places shape hp pin tables.jobs argFit sites
  exact registered_header_rows prior ticket op gain tail p f drift degree payload seats root ordinary
    w shelf header pos room exec B number places shape hp pin metadataWords tables.old tables.jobs argFit dates m
    posted preserved earlier dated previous stored tables.rows tables.keys bitsFit full vacant
    (fun u=>(source u).1) (fun u=>(source u).2.1) (fun u=>(source u).2.2)

omit [Fintype P] in
/-- This entry accepts the two measured input strips before the final writer. The
cursor equality selects the archived copy of the numbered result at the next date. -/
theorem header_return_at_cursor
    {nextPorts:DatePorts} (posted:dates i=ordinaryDate prior ticket op gain tail p f drift degree payload seats root ordinary
      w shelf header pos room) (point:nextPorts=out)
    (preserved:(meter).endAddr≤(v).finalChart.out ((v).metaEnd floor)) (earlier:header<(meter).endAddr)
    (dated:i<S.length) (previous:prior.argumentsPerNode≤S.retainedArgumentsAt G drift)
    (bitsFit:(v).finalChart.field*(v).resolver.nodes*(v).resolver.lanes≤w)
    {jobs_:Fin (v).resolver.jobs→DescentDatedPriorOperand.Source (v).resolver} {old_:Books (v).resolver}
    (keys:∀j,Reads (Banks.wordBank (v).resolver ((v).normalizedEnd floor) j)
      (fun h g=>word ((jobs_ j).compiled h g)) (v).resolver.lanes work)
    (rows:∀x pg,Reads (previousBank (v).resolver ((v).vectorOutput floor) x pg) (old_ x pg) (v).resolver.lanes work)
    (B₁:BitDescription n.result) (number₁:Local B₁) (where₁:RangeRoom nextPorts next B₁)
    {K:ℕ} (shape₁:WorldShape p K B₁) (hp₁:0<p) (pin₁:P→ℕ)
    (arityFit:∀u nodeIndex,((shape₁.sites u).recipe hp₁).arity nodeIndex≤(v).resolver.operands)
    (arity:HeaderArity prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header
      pos room exec B₁ number₁ (point ▸ where₁) shape₁ hp₁ dates m)
    (sites:Reached.PointerSites next (v) B₁ number₁ shape₁ hp₁ pin₁ jobs_) :
    HeaderRows nextPorts next B₁ number₁ where₁ shape₁
      (Reached.argumentPointer next B₁ number₁ shape₁ hp₁ pin₁ nextPorts.argumentsPerNode)
      (DateCode.history dates m (i+1)):=by
  subst nextPorts
  let tables:PhysicalOrdinary.HeaderTables (v) floor work :=
    PhysicalOrdinary.HeaderTables.from_reads (v) floor work keys rows
  exact registered_header_return prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header
    pos room exec B₁ number₁ where₁ shape₁ hp₁ pin₁ arityFit dates m posted preserved earlier dated previous
    bitsFit tables arity sites

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
