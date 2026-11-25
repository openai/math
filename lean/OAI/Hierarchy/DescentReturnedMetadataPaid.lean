import OAI.Hierarchy.DescentRegisteredReturnedVenue
import OAI.Hierarchy.DescentNativeMetadataPaid
import OAI.Hierarchy.DescentDatedOrdinaryRegisteredOperand

namespace OAI
/-! The physical count used by the ordinary node checkpoint after the venue has returned. -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
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

theorem returned_metadata_paid (m : Memory w) (wide : Fintype.card next.V≤(v).venue.hosts)
    (crop : (v).resolver.hosts≤(v).venue.hosts)
    (issued : returnedVenue prior ticket op gain tail p f drift degree payload seats root ordinary
      w shelf header pos room exec m) (x : Block k) :
    Source ((v).venue.metadataPaid B x.val)
      (fun (h:Fin (v).resolver.hosts) g=>Census.count next.placement (Equiv.refl _)
        (next.vertex.trans (Fin.castLEEmb wide)) (v).metadata.paidBits (h.castLE crop) g x)
      (v).resolver.lanes (funded m):=
  StageVenueTail.Date.metadata_paid_source next (v).venue B wide rfl rfl crop x
    ((v).rasterEnd floor) (funded m) room.result.venue (issued wide).2.2

local notation "record" m => ordinaryMetadata prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room exec m
local notation "chart" => (v).nodeChart
local notation "start" => (v).metaStart floor
local notation "pb" => (v).metadata.paidBits
local notation "sb" => (v).resolver.size+2
local notation "counts" => (fun x:Fin (chart).blocks=>(v).venue.metadataPaid B x.val)
local notation "spans" => (v).spanVectors floor

/-- The previous span words and the funded bank in the actual return determine both metadata pages. -/
theorem returned_metadata_rows (m : Memory w) (wide : Fintype.card next.V≤(v).venue.hosts)
    (crop : (v).resolver.hosts≤(v).venue.hosts)
    (issued : returnedVenue prior ticket op gain tail p f drift degree payload seats root ordinary
      w shelf header pos room exec m)
    (words : Fin (chart).blocks→Fin (v).resolver.operands→Fin (chart).hosts→Fin (chart).groups→Cell ((sb)*(chart).nodes))
    (printed : ∀x j,Reads (spans x j) (words x j) (chart).lanes (record m))
    (arity : Fin (chart).blocks→Fin (chart).nodes→Fin (chart).hosts→Fin (chart).groups→ℕ)
    (bounded : ∀x n h g,arity x n h g≤(v).resolver.operands)
    (live : ∀x n j h g,DescentOrdinaryAtomFieldRAM.ScalarOperand.take (a:=sb) n (words x j h g)≠0 ↔ j.val<arity x n h g)
    (field : Fin 2) (x : Fin (chart).blocks) :
    Reads ((chart).bank ((v).nodeBankBase floor) field x)
      (fun h g=>encode (chart).bits (chart).nodes (fun n=>if field=0 then
        (if n.val<(Census.count next.placement (Equiv.refl _) (next.vertex.trans (Fin.castLEEmb wide))
          pb (h.castLE crop) g x).val then 1 else 0) else (arity x n h g:Cell (chart).bits)))
      (chart).lanes (record m):=by
  have top : (v).metaEnd floor≤(v).operandEnd floor:=by
    rw [PhysicalOrdinary.operandEnd,(v).operandBook.affine]
    exact Nat.le_add_right ..
  have boundary:=(v).nodeEnd floor room.result.chart room.result.digit
  have admissible:=boundary.le.trans_lt (top.trans_lt room.result.limit)
  have native:=(chart).ordinaryAny start pb sb counts spans (funded m) room.result.paid room.result.spans admissible
  have capacity (x j) : (chart).rows≤(spans x j).size:=
    (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have before (x j) : Reads (spans x j) (words x j) (chart).lanes (funded m):=by
    intro index
    have below:=(Nat.add_lt_add_left ((row _ _ _ index).isLt.trans_le (capacity x j)) _).trans_le
      (room.result.spans x j).2.2
    exact (native.2.1 _ (.inl below)).symm.trans (printed x j index)
  exact (chart).ordinaryPair start pb sb counts spans (funded m) _ words arity bounded live
    room.result.paid room.result.spans
    (returned_metadata_paid prior ticket op gain tail p f drift degree payload seats root ordinary
      w shelf header pos room exec m wide crop issued) capacity before admissible field x

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
