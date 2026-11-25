import OAI.Hierarchy.DescentOrdinarySignedActorHeaders
import OAI.Hierarchy.DescentOrdinarySourceArchive
import OAI.Hierarchy.DescentDatePortArchiveWidths
import OAI.Hierarchy.DescentRegisteredArgumentInletRoom

namespace OAI
/-! Previous argument words and one-based primitive tokens at the registered ordinary signed cut. -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
namespace DatePorts
open DescentDatedPriorOperand DescentOperandStateBanks

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
local notation "src₀" => (v).reachedSources floor

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
local notation "rot" => ((date₀).schedule (v).payload (v).seats (v).bitsPerField).rotationEnd prior.io.roster floor
local notation "meter" => (date₀).counter (v).payload rot header
local notation "readAt" => (v).rasterEnd floor
local notation "args" => (v).venue.operands src₀ readAt
local notation "ready" => (v).metaStart floor
local notation "measure" => (⟨(v).prior.placement.wire,(v).prior.placement.z,(v).prior.placement.hist⟩:Dated.Measures)


local notation "donor" m => ordinaryDonorMemory prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room exec m
local notation "wired" m => ordinarySignedMemory prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room exec m
local notation "before" m => (v).peerEntry root shelf header prior.io prior.archive.count digits steps date₀ pos exec m
local notation "peered" m => (v).afterPeer root shelf header prior.io prior.archive.count digits steps date₀ pos exec m
local notation "paid" => (v).materialEnd floor
local notation "nextPeer" => (v).peerTail floor
local notation "mark_" => (v).markEnd floor
local notation "after" => (v).signedEnd floor
local notation "now" m => (steps).arguments.image (wired m)


open DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentPrimitivePalette


open DescentPackedColony DescentColonies

open PhysicalOrdinary.ArgumentEntry
local notation "pop₀" => (A).population (v) floor
local notation "bits₀" => printedBits G (S.firstWidth G.b p) (S.grainAt G.b p 0) op
local notation "labels₀" => Label G (S.firstWidth G.b p) (S.grainAt G.b p 0) op

/-- Supply the old seven words and the full primitive word from a single earlier archive.
The last equality also specifies every inactive and out-of-range primitive digit. -/
theorem ordinary_signed_pages {K : ℕ} (B : BitDescription W) (number : Local B)
    (places : RangeRoom prior prevWorld B) (shape : WorldShape p K B)
    (label : NodeOrder.All B→labels₀) (pointer : NodeOrder.All B→ℕ→Pointer)
    (flags : Fin (2^prior.venue.k)→Fin prior.nodes→Fin prior.operandHosts→Fin prior.venue.groups→ℕ)
    (m : Memory w) (source : ArchiveRead prior prevWorld B number places shape op label pointer flags (wired m))
    (registered : prior.ArchiveFits k root) (space : root<2^w) (capacity : prior.RoleRows)
    (archive : ArchiveWidths G S op prior k tail p drift degree payload i)
    (rolePositive : 0<prior.roleLanes) :
    ∃(old : Pages (A).previous.operands→Fin (A).previous.blocks→Fin (A).previous.hosts→Fin (A).previous.groups→
        Cell (DescentOrdinaryPriorRetile.digits (A).previous))
      (roles : Fin (A).previous.blocks→Fin (A).previous.hosts→Fin (A).clip.venue.groups→
        Cell ((pop₀).roleBits*(pop₀).nodes)),
      0<(A).previous.lanes ∧ 0<(A).rolePitch ∧
      (∀x j,(previousBank (A).previous (A).previousBase x j).Fits w ((v).signedEnd floor)) ∧
      (∀x j,Reads (previousBank (A).previous (A).previousBase x j) (old j x) (A).previous.lanes (wired m)) ∧
      (∀x,((A).role x).base+((A).role x).size≤(v).signedEnd floor) ∧
      (∀x,(A).previous.hosts*chunks (A).clip.venue.groups (A).rolePitch≤((A).role x).size) ∧
      (∀x,Reads ((A).role x) (roles x) (A).rolePitch (wired m)) ∧
      ∀x h g,(roles x h g).val=(DescentSIMDLookup.encode bits₀ prior.nodes (fun j=>
        (slotAt prior prevWorld B number places (x.cast (congrArg (2^·) places.radix)) j h (g.cast places.groups)).elim 0
          (fun y=>token G (S.firstWidth G.b p) (S.grainAt G.b p 0) op (label y)))).val:=by
  have wide : 2≤prior.operandBits:=by
    rw [archive.digits]
    exact (le_max_left _ _ : 2≤DescentOperandWidth.s G S k tail drift degree).trans (le_max_left ..)
  have pages:=source.ordinary_input_pages (congrArg (2^·) places.radix) wide
  obtain ⟨old,read⟩:=pages.1
  let tokenRows x h g:=DescentSIMDLookup.encode bits₀ prior.nodes (fun j=>
    (slotAt prior prevWorld B number places ((x : Fin (2^k)).cast (congrArg (2^·) places.radix)) j h g).elim 0
      (fun y=>token G (S.firstWidth G.b p) (S.grainAt G.b p 0) op (label y)))
  have low : root≤floor:=by
    change root≤(v).profileRepack.endAddress root
    rw [(v).profileRepack.translate]
    exact Nat.le_add_right ..
  have below : root≤(v).signedEnd floor:=by rw [(v).signed_extent,(v).donor_shift];omega
  let blank : DescentResetRetainedSetup.Layout:=⟨0,0,0,0,0,0,0,0,0,0,0,0,0,0,0⟩
  have oldFit:=prior.prior_fits (2^k) root w (registered.data blank).2 space
  refine ⟨old,fun x=>rowsAt rfl places.groups rfl (tokenRows x),places.positive,rolePositive,?_,read,?_,?_,?_,?_⟩
  · intro x j
    have held:=oldFit x j
    exact ⟨held.1,held.2.1,held.2.2.trans below⟩
  · intro x
    exact ((prior.archive.roles.fits w root x.val (x.isLt.trans_le registered.blocks) registered.roles space).2.2).trans below
  · intro x
    change prior.operandHosts*chunks (S.groupCount i) prior.roleLanes≤2^prior.archive.roles.bits
    rw [places.groups]
    exact capacity
  · intro x
    exact reads_at rfl places.groups rfl rfl (pages.2 x)
  · intro x h g
    rfl

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
