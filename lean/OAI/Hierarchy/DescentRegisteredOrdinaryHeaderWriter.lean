import OAI.Hierarchy.DescentDatedOrdinaryRegisteredOperand
import OAI.Hierarchy.DescentArchivePointerRows
import OAI.Hierarchy.DescentOrdinaryArchiveHeaders
import OAI.Hierarchy.DescentOrdinaryRegisteredHeaderRoom
import OAI.Hierarchy.DescentRegisteredHeaderFrames

namespace OAI
/-! The registered ordinary tape returns the four original pointer «metadataWords» at its actual next cursor. -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open DescentPackedColony DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxHeartbeats 650000
open scoped Fin.CommRing
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
  (argFit:∀(u:(modelWorld).graph.Site) nodeIndex,(rec₁ u).arity nodeIndex≤(v).resolver.operands)
local notation "mouth" u:arg => (v).finalChart.mouths (rec₁ u) (onsite u) (argFit u)
local notation "fragment" u:arg nodeIndex:arg j:arg => (v).issuedFragment jobs (sx u) (sh u) (sg u) ((mouth u) ⟨nodeIndex,j⟩)
local notation "expected" => Reached.argumentPointer next B number shape hp pin (v).resolver.operands


/-- The three cases refer directly to the resolver's earlier fragment and the chosen old archive. -/
def HeaderSites : Prop :=
    ∀u,(∃hidden:(rec₁ u).UsedWord↪Key,(v).SourceKeys jobs (sx u) (sh u) (sg u) (rec₁ u) (onsite u) (argFit u) hidden) ∧
    (∀nodeIndex (j:Fin ((rec₁ u).arity nodeIndex)) (e:DescentKernelHistory.Incident (modelWorld).graph u) z
      (enough:(z+1)*p≤(modelWorld).graph.width e.val), (rec₁ u).operand nodeIndex j=.inl ⟨.inl e,z,enough⟩ →
      Pointer.ofKey 0 (resolve (fragment u nodeIndex j))=Reached.firstCable next hp u e z enough) ∧
    ∀nodeIndex (j:Fin ((rec₁ u).arity nodeIndex)) (e:DescentKernelHistory.Attached (modelWorld).graph u) z
      (enough:(z+1)*p≤bits e.val), (rec₁ u).operand nodeIndex j=.inl ⟨.inr e,z,enough⟩ →
      resolve (fragment u nodeIndex j)=Key.pin (pin e.val) z

variable (dates:ℕ→DateCode w) (m:Memory w)
local notation "sourceMem" => DateCode.history dates m i
local notation "work" => ordinaryMetadata prior ticket op gain tail p f drift degree payload seats root ordinary
  w shelf header pos room exec sourceMem
/-- The earlier native metadata bank gives the true arity at every occupied node, and zero at unused slots. -/
def HeaderArity : Prop :=
  ∃metadataWords:(v).MetaWords,(∀field x,Reads ((v).nodeChart.bank ((v).nodeBankBase floor) field x) (metadataWords field x)
    (v).resolver.lanes work) ∧
    (∀u nodeIndex,digit (v).finalChart.arityBits ((onsite u) nodeIndex).val (metadataWords 1 (sx u) (sh u) (sg u)).val=(rec₁ u).arity nodeIndex) ∧
    ∀u t,(∀nodeIndex,(onsite u) nodeIndex≠t)→digit (v).finalChart.arityBits t.val (metadataWords 1 (sx u) (sh u) (sg u)).val=0

local notation "meter" => (date₀).counter payload (((date₀).schedule payload seats (v).bitsPerField).rotationEnd prior.io.roster floor) header

omit [Fintype P] in
theorem registered_header_rows
    (posted:dates i=ordinaryDate prior ticket op gain tail p f drift degree payload seats root ordinary
      w shelf header pos room)
    (preserved:(meter).endAddr≤(v).finalChart.out ((v).metaEnd floor)) (earlier:header<(meter).endAddr)
    (dated:i<S.length) (previous:prior.argumentsPerNode≤S.retainedArgumentsAt G drift)
    (newRead:∀field x,Reads ((v).nodeChart.bank ((v).nodeBankBase floor) field x) («meta» field x) (v).resolver.lanes work)
    (spanRead:∀x pageIndex,Reads (previousBank (v).resolver ((v).vectorOutput floor) x pageIndex) (old x pageIndex) (v).resolver.lanes work)
    (keyRead:∀j,Reads (Banks.wordBank (v).resolver ((v).normalizedEnd floor) j)
      (fun h g=>word ((jobs j).compiled h g)) (v).resolver.lanes work)
    (bitsFit:(v).finalChart.field*(v).resolver.nodes*(v).resolver.lanes≤w)
    (count:∀u nodeIndex,digit (v).finalChart.arityBits ((onsite u) nodeIndex).val («meta» 1 (sx u) (sh u) (sg u)).val=(rec₁ u).arity nodeIndex)
    (empty:∀u t,(∀nodeIndex,(onsite u) nodeIndex≠t) →
      digit (v).finalChart.arityBits t.val («meta» 1 (sx u) (sh u) (sg u)).val=0)
    (names:∀u,∃hidden:(rec₁ u).UsedWord↪Key,(v).SourceKeys jobs (sx u) (sh u) (sg u) (rec₁ u) (onsite u) (argFit u) hidden)
    (cable:∀u nodeIndex (j:Fin ((rec₁ u).arity nodeIndex)) (e:DescentKernelHistory.Incident (modelWorld).graph u) z
      (enough:(z+1)*p≤(modelWorld).graph.width e.val), (rec₁ u).operand nodeIndex j=.inl ⟨.inl e,z,enough⟩ →
      Pointer.ofKey 0 (resolve (fragment u nodeIndex j))=Reached.firstCable next hp u e z enough)
    (exterior:∀u nodeIndex (j:Fin ((rec₁ u).arity nodeIndex)) (e:DescentKernelHistory.Attached (modelWorld).graph u) z
      (enough:(z+1)*p≤bits e.val), (rec₁ u).operand nodeIndex j=.inl ⟨.inr e,z,enough⟩ →
      resolve (fragment u nodeIndex j)=Key.pin (pin e.val) z)
    : HeaderRows out next B number places shape expected (DateCode.history dates m (i+1)):=by
  obtain ⟨capacity,rectangle⟩:=ordinary_header_capacities prior ticket op gain tail p f drift degree payload seats root ordinary dated previous
  exact ordinary_argument_headers (v) root shelf header prior.io prior.archive.count digits ((v).reachedSources floor)
    steps room.result date₀ pos exec dates m i posted coordsB coordsG preserved earlier next B number places shape hp pin
    «meta» old jobs argFit newRead spanRead keyRead bitsFit count empty names cable exterior capacity rectangle

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
