import OAI.Hierarchy.DescentRegisteredOrdinaryStep
import OAI.Hierarchy.DescentOrdinaryDateBillExact
import OAI.Hierarchy.DescentIssuedOrdinaryInvoice
import OAI.Hierarchy.DescentRegisteredReturnInvoice
import OAI.Hierarchy.DescentOrdinaryReturnBill

namespace OAI
/-! # Literal breakdown of the dated word tariff executed by the public register -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
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
set_option quotPrecheck false
set_option hygiene false
local notation "books" => OrdinaryBooks.atDate G S op gain k i p tail drift degree payload seats prior
local notation "base" => (books).onTicket ticket gain tail p f payload seats prior.venue.lanes prior.io.roster ordinary
local notation "floor" => (base).stageStart root

local notation "v" => ordinaryModel prior ticket op gain tail p f drift degree payload seats root ordinary

local notation "A" => (base).registeredEntry prior floor
local notation "match₀" => (base).registered_match prior floor (Nat.le_max_left prior.argumentsPerNode (S.retainedArgumentsAt G drift))
local notation "sh" => (base).registered_geometry prior floor
local notation "B" => (v).reachedSources floor

variable (w : ℕ) (shelf header : ℕ) (pos : 0 < k)
variable (room : OrdinaryCodeRoom prior ticket op gain tail p f drift degree payload seats root ordinary w)
local notation "steps" => (v).issuedSteps root prior (A) room.signed w (match₀) (sh) room.blocks room.paths
  room.slots room.chip room.endFit room.packed room.radix room.funded


theorem ordinary_date_invoice :
    let d:=DonorDate.atDate G S gain k i p
    let a:=d.schedule payload seats (S.censusBits p)
    let base₀:=a.rotationEnd prior.io.roster floor
    let data₀ : Dated.Measures:=⟨prevWorld.placement.wire,prevWorld.placement.z,prevWorld.placement.hist⟩
    let m:=d.counter payload base₀ header
    (ordinaryDate prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room).tariff=
      ((v).archivePhase root shelf w).wordInvoice+
        DateBill.bitTariff (a.program G pos prior.io data₀ w floor) (a.ticks G pos prior.io data₀ w floor)+
        (d.afterMatcher payload seats prior.io (S.censusBits p) floor w).wordInvoice+
        ((v).finish floor prior.io prior.archive.count ((v).signedInput floor room.signed) (B) steps room.result).wordInvoice+
        DateBill.bitTariff (m.program w) m.ticks :=by
  intro d a base₀ data₀ m
  exact d.loaded_tariff G pos payload seats (S.censusBits p) floor header w prior.io data₀
    ((v).archivePhase root shelf w) ((v).finish floor prior.io prior.archive.count ((v).signedInput floor room.signed)
      (B) steps room.result)

local notation "oldVenue" => (⟨prior.archive.count,prior.io.roster,prior.io.hubs⟩:DescentOrdinaryVenueReturn.Sources)

/-- Each summand is either the original registered subprogram or the sum of a pair of its non-adjacent subprograms. -/
theorem ordinary_date_charges :
    let d:=DonorDate.atDate G S gain k i p
    let a:=d.schedule payload seats (S.censusBits p)
    let rot:=a.rotationEnd prior.io.roster floor
    let data₀ : Dated.Measures:=⟨prevWorld.placement.wire,prevWorld.placement.z,prevWorld.placement.hist⟩
    let m:=d.counter payload rot header
    (ordinaryDate prior ticket op gain tail p f drift degree payload seats root ordinary w shelf header pos room).tariff=
      ((v).archivePhase root shelf w).wordInvoice+
      DateBill.bitTariff (a.program G pos prior.io data₀ w floor) (a.ticks G pos prior.io data₀ w floor)+
      ((d.afterMatcher payload seats prior.io (S.censusBits p) floor w).wordInvoice+
        DateBill.bitTariff (m.program w) m.ticks)+
      ((v).issuedPrefix floor w (A).venue.panel (A).venue.adjacency oldVenue prior.io room.signed).wordInvoice+
      (steps).arguments.wordInvoice+(steps).paid.wordInvoice+(v).tailAmount floor w (B) room.result+
      (steps).primitive.wordInvoice :=by
  intro d a rot data₀ m
  have panel : (steps).parts=(A).venue.panel := rfl
  have adjacent : (steps).adjacency=(A).venue.adjacency := rfl
  have tail := show (v).tailAmount floor w (B) room.result =
      ((v).returnPhase floor (B) w room.result).wordInvoice+((v).counter floor w).wordInvoice from rfl
  rw [ordinary_date_invoice]
  simp only [Chronology.PhysicalOrdinary.finish,Chronology.PhysicalOrdinary.beforeCount,
    Chronology.PhysicalOrdinary.issuedPrefix,Chronology.PhysicalOrdinary.signedPhase,
    NativePhase.wordInvoice_seq,panel,adjacent,tail]
  dsimp only [d,a,rot,data₀,m]
  ac_rfl

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
