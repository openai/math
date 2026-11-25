import OAI.Hierarchy.DescentRegisteredOrdinaryExecution
import OAI.Hierarchy.DescentRegisteredOrdinaryVenueRoom

namespace OAI
/-! # Carry the measured ordinary venue and actual host count through the registered date -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
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
local notation "rot" => ((date₀).schedule (v).payload (v).seats (v).bitsPerField).rotationEnd prior.io.roster floor
local notation "meter" => (date₀).counter (v).payload rot header
local notation "readAt" => (v).rasterEnd floor
local notation "args" => (v).venue.operands B readAt
local notation "ready" => (v).metaStart floor
local notation "measure" => (⟨(v).prior.placement.wire,(v).prior.placement.z,(v).prior.placement.hist⟩:Dated.Measures)

/-- The signed scan begins at the retained donor panel of the original numbered cut. -/
def ordinaryDonorMemory (m:Memory w):Memory w:=
  let archive:=((v).archivePhase root shelf w).image m
  let matched:=(((date₀).schedule (v).payload (v).seats (v).bitsPerField).nativePhase G pos prior.io measure w floor exec.matcher).image archive
  ((date₀).afterMatcher (v).payload (v).seats prior.io (v).bitsPerField floor w).image matched

/-- All input rows of the paid raster are read on this particular output of the signed scan. -/
def ordinarySignedMemory (m:Memory w):Memory w:=
  let a:=ordinaryDonorMemory prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room exec m
  let b:=((v).beforeSignedMaterial floor (steps).parts (steps).adjacency w).image a
  let peers:=(DescentOrdinaryVenueReturn.phase sources ((v).materialEnd floor) k (v).area.H (v).area.D (v).venue.hosts (v).venue.degree w).image b
  ((v).signed.phase digits ((v).markEnd floor) w).image (((v).mark floor prior.io w).image peers)

local notation:max "wiresAt" m:arg => ordinarySignedMemory prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room exec m
local notation:max "rasterIn" m:arg => (steps).arguments.image (wiresAt m)
local notation "funded" => (v).fundedRaster floor ((v).fundedFromEntry floor A room.paths) prior.io w room.funded

set_option maxRecDepth 4096 in
theorem ordinary_before_return (m:Memory w):
    (v).beforeReturn root shelf header prior.io prior.archive.count digits steps date₀ pos exec m=(funded).image (rasterIn m):=rfl

set_option maxRecDepth 4096 in
theorem ordinary_output_held (m:Memory w) (old:prior.held prevWorld root m)
    (hostSize:prior.venue.hosts=(v).area.H)
    (wireSpace:∀(x:DescentColonies.Block k)(j:Fin (2*prevWorld.placement.cap)),
      (prior.io.wire x.val j.val).base+(v).area.H*chunks (S.groupCount i) prior.venue.lanes≤root)
    (countLow:prior.archive.count.base<root) (oldDegree:(v).area.D=D)
    (newDegree:(v).venue.degree=D') (wide:Fintype.card next.V≤(v).venue.hosts)
    (cap:next.placement.cap=(v).venue.cap)
    (cash:rot≤ (meter).base ∧ (meter).base< (meter).endAddr ∧ (meter).endAddr≤depot)
    (issued:stageVenue next wide args (v).venue.lanes (v).venue.paidBits ready (next.venueRoster wide)
      (((v).venue.phase B readAt w).image ((funded).image (rasterIn m)))):
    (ordinaryPorts prior ticket op gain tail p f drift degree payload seats root ordinary).held next ((v).fullEnd root)
      (ordinaryOutput prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room exec m):=by
  have shift : root≤floor:=by
    change root≤(base).profileRepack.endAddress root
    rw [(base).profileRepack.translate];omega
  have chosen : floor≤rot:=by
    have h:=((date₀).schedule (v).payload (v).seats (v).bitsPerField).rotation_add prior.io.roster 0 floor
    simp only [Nat.add_zero] at h
    rw [h];exact Nat.le_add_right ..
  have start:=shift.trans chosen
  have paid:=cash.2.2
  have nextLow:depot≤(v).rasterEnd floor:=by
    obtain ⟨material,peer,sign⟩:=(v).signed_stage_paid floor
    have wires:(v).signedEnd floor≤(v).refsStart floor:=Nat.le_add_right ..
    have refs:(v).refsStart floor≤(v).birthStart floor:=Nat.le_add_right ..
    have born:(v).birthStart floor≤(v).vectorStart floor:=by
      rw [PhysicalOrdinary.vectorStart,(v).bornBook.affine];exact Nat.le_add_right ..
    have resolved:(v).normalizedEnd floor≤(v).endAddress floor:=by
      rw [PhysicalOrdinary.endAddress,(v).resolver.affine];exact Nat.le_add_right ..
    have fundedAt:(v).endAddress floor≤(v).rasterEnd floor:=by
      rw [PhysicalOrdinary.rasterEnd,StageVenueTail.OrdinaryRaster.translated];exact Nat.le_add_right ..
    exact material.trans (peer.trans (sign.trans (wires.trans (refs.trans (born.trans
      (((v).vector_before floor).trans (((v).routed_le floor).trans (resolved.trans fundedAt))))))))
  have countAfter:depot≤(PriorResetArchive.ordinary (v) floor).count.base:=by
    apply ((v).signed_stage_paid floor).1.trans
    change (v).materialEnd floor≤DescentOrdinaryPeerChart.top (DescentOrdinaryPeerRows.fixed _ _ _) _ _
    simp only [DescentOrdinaryPeerChart.top,DescentOrdinaryPeerChart.out,DescentOrdinaryPeerRows.fixed]
    omega
  have pins:=(v).reachedLower floor
  exact (v).date_ordinary_held root shelf header prior.io prior.archive.count digits B steps room.result
    date₀ pos exec m prior old hostSize rfl rfl wireSpace countLow start
    (start.trans (cash.1.trans (cash.2.1.le.trans paid))) oldDegree newDegree rfl rfl wide rfl
    cap (paid.trans nextLow) (paid.trans pins.1) (paid.trans pins.2) (paid.trans countAfter)
    (exec.counter.before.trans_lt cash.2.1) issued

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
