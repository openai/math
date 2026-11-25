import OAI.Hierarchy.DescentRegisterInstructionRun
import OAI.Hierarchy.DescentRegisteredOrdinaryExecution
import OAI.Hierarchy.DescentActualDonorBounds

namespace OAI
/-! # Protected execution of the registered ordinary date on arbitrary memory -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
set_option quotPrecheck false
noncomputable section
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

include exec in
theorem ordinary_protected :
    RegisterTimeline.Protected (ordinaryDate prior ticket op gain tail p f drift degree payload seats root ordinary
      w shelf header pos room) root header:=by
  let native:=ordinary_output prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header
    pos room exec
  let m₀:Memory w:=fun _=>0
  refine ⟨?_,(native m₀).2⟩
  intro m
  refine ⟨_,(native m).1,?_⟩
  intro j earlier other
  apply (v).date_low root shelf header prior.io prior.archive.count digits (B) steps room.result date₀ pos exec m j earlier other
  let a:=(date₀).schedule payload seats (S.censusBits p)
  let rot:=a.rotationEnd prior.io.roster floor
  have baseLo : root≤floor:=by
    change root≤(v).profileRepack.endAddress root
    rw [(v).profileRepack.translate]
    exact Nat.le_add_right ..
  have rotLo : floor≤rot:=by
    have h:=a.rotation_add prior.io.roster 0 floor
    simp only [Nat.add_zero] at h
    change floor≤a.rotationEnd _ _
    rw [h]
    exact Nat.le_add_right ..
  have meter : rot≤(date₀).meterBase payload rot:=by
    unfold DonorDate.meterBase DonorSpace.meterBase
      DonorSpace.source DonorSpace.dynamicStart
    dsimp only
    omega
  have donor : floor≤(v).donorEnd floor:=by rw [(v).donor_shift]; exact Nat.le_add_right ..
  exact ⟨baseLo.trans rotLo,meter,baseLo.trans donor⟩

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
