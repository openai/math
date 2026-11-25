import OAI.Hierarchy.DescentReturnedMetadataFromSpans
import OAI.Hierarchy.DescentArchiveArityPadding

namespace OAI
/-! # Both returned node rows and the arity digit on each genuine or vacant node -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxHeartbeats 900000
set_option maxRecDepth 6000
open scoped Classical Fin.CommRing
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
local notation "B" => (v).reachedSources floor

variable (w : ℕ) (shelf header : ℕ) (pos : 0<k)
variable (room : OrdinaryCodeRoom prior ticket op gain tail p f drift degree payload seats root ordinary w)
local notation "steps" => (v).issuedSteps root prior (A) room.signed w (match₀) (sh) room.blocks room.paths
  room.slots room.chip room.endFit room.packed room.radix room.funded


local notation "digits" => (v).signedInput floor room.signed
local notation "date₀" => DonorDate.atDate G S gain k i p
local notation "depot" => (v).donorEnd floor
local notation "sources" => (⟨prior.archive.count,prior.io.roster,prior.io.hubs⟩:DescentOrdinaryVenueReturn.Sources)
local notation "pg" => (⟨0,Nat.mul_pos (by decide : 0<7) room.slots⟩:Fin (7*(v).vector.operands))


variable (exec:OrdinaryExecutionRoom prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header room)

open DescentPackedZip DescentPackedColony DescentColonies
open scoped Classical Fin.CommRing
local notation "current" m => (v).beforeReturn root shelf header prior.io prior.archive.count digits steps date₀ pos exec m
local notation "funded" m => (((v).venue.phase B ((v).rasterEnd floor) w).image (current m))

local notation "record" m => ordinaryMetadata prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room exec m
local notation "chart" => (v).nodeChart
local notation "start" => (v).metaStart floor
local notation "pb" => (v).metadata.paidBits
local notation "sb" => (v).resolver.size+2
local notation "counts" => (fun x:Fin (chart).blocks=>(v).venue.metadataPaid B x.val)
local notation "spans" => (v).spanVectors floor


open DescentCompiler DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentRetainedRangeDigits
variable [Fintype P] {R : ℕ} (desc : BitDescription n.result) (ord : Local desc)
local notation "ports" => DatePorts.ordinary v floor
variable (places : RangeRoom ports next desc) (shape : WorldShape p R desc)
local notation "atNode" => slotAt ports next desc ord places
local notation "lengthAt" x:arg j:arg h:arg g:arg =>
  (atNode x j h g).elim 0 (fun y=>(occurrences (shape.sites y.1) y.2).length)
local notation "flag" => RegisterTimeline.archiveFlag next desc ord ports places

local notation "own" u => (ord u).toEmbedding.trans (Fin.castLEEmb (places.capacity u))
local notation "blockOf" u => (next.placement.block u).cast (congrArg (2^·) places.radix)
local notation "hostOf" u => (⟨(next.vertex (next.placement.pos u).2).val,places.hosts u⟩:Fin (ports).operandHosts)
local notation "groupOf" u => (next.placement.pos u).1.cast places.groups

omit [Fintype P] in
theorem returned_metadata_cells (m : Memory w) (wide : Fintype.card next.V≤(v).venue.hosts)
    (crop : (v).resolver.hosts≤(v).venue.hosts)
    (issued : returnedVenue prior ticket op gain tail p f drift degree payload seats root ordinary
      w shelf header pos room exec m)
    (words : Fin (chart).blocks→Fin (v).resolver.operands→Fin (chart).hosts→Fin (chart).groups→Cell ((sb)*(chart).nodes))
    (printed : ∀x j,Reads (spans x j) (words x j) (chart).lanes (record m))
    (bounded : ∀x n h g,lengthAt x n h g ≤ (v).resolver.operands)
    (hp : 0<p)
    (active : ∀x n j h g y,atNode x n h g=some y →
      (DescentOrdinaryAtomFieldRAM.ScalarOperand.take (a:=sb) n (words x j h g)).val=
        atSlot (shape.sites y.1) y.2 j.val 2)
    (vacant : ∀x n j h g,atNode x n h g=none →
      DescentOrdinaryAtomFieldRAM.ScalarOperand.take (a:=sb) n (words x j h g)=0)
    (mass : next.placement.wire*(next.placement.z*G.b)*next.placement.cap<2^(S.censusBits p))
    (size : ∀u n,((shape.sites u).recipe hp).arity n<2^(ports).operandBits) :
    ∃fieldWords : (v).MetaWords,
      (∀fieldIndex x,Reads ((chart).bank ((v).nodeBankBase floor) fieldIndex x) (fieldWords fieldIndex x) (v).resolver.lanes (record m)) ∧
      (∀u n,DescentSIMDLookup.digit (v).finalChart.arityBits ((own u) n).val
        (fieldWords 1 (blockOf u) (hostOf u) (groupOf u)).val=((shape.sites u).recipe hp).arity n) ∧
      ∀u n,(∀s,(own u) s≠n)→DescentSIMDLookup.digit (v).finalChart.arityBits n.val
        (fieldWords 1 (blockOf u) (hostOf u) (groupOf u)).val=0 :=by
  let fieldWords : (v).MetaWords := fun fieldIndex x h g=>encode (ports).operandBits (ports).nodes (fun n=>
    (if fieldIndex=0 then flag x n h g else lengthAt x n h g : Cell (ports).operandBits))
  have returned:=returned_metadata_from_spans prior ticket op gain tail p f drift degree payload seats root ordinary
    w shelf header pos room exec desc ord places shape m wide crop issued words printed bounded hp active vacant mass
  have digitsAt (u:n.result.graph.Site) :=
    Reached.NodeCells.original_arity_digits next desc ord shape hp u (hostOf u) rfl (places.capacity u)
      (fieldWords 1 (blockOf u) (hostOf u) (groupOf u))
  have row (u:n.result.graph.Site) :
      fieldWords 1 (blockOf u) (hostOf u) (groupOf u)=encode (ports).operandBits (ports).nodes
        (fun j=>(Reached.NodeCells.atPhysical next desc ord (next.placement.block u) j (hostOf u)
          (next.placement.pos u).1).elim 0 (fun y=>((occurrences (shape.sites y.1) y.2).length:Cell (ports).operandBits))) :=by
    dsimp only [fieldWords]
    congr 1
  refine ⟨fieldWords,?_,fun u=>(digitsAt u (row u) (size u)).1,fun u=>(digitsAt u (row u) (size u)).2⟩
  intro fieldIndex x
  have fieldCases : fieldIndex=0 ∨ fieldIndex=1 := by fin_cases fieldIndex <;> decide
  rcases fieldCases with rfl | rfl
  · simp only [fieldWords, Fin.isValue, ↓reduceIte]
    exact returned.1 x
  · simp only [fieldWords, Fin.isValue, Fin.reduceEq, ↓reduceIte]
    exact returned.2 x

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
