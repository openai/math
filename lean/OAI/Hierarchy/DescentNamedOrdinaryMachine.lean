import OAI.Hierarchy.DescentPublicOrdinaryMachine
import OAI.Hierarchy.DescentNamedOrdinaryBarePlan

namespace OAI
/-! # A single ordinary instruction stream on every issued cut at this age -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentOrdinaryVenueIngress ProtocolRAM
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

private theorem archive_profile_code {F P : Type} [Field F] (model : PhysicalOrdinary F P)
    (origin shelf w : ℕ) :
    PrintedStep.ofPhase (model.archivePhase origin shelf w) =
      DatePorts.profileCode model.area model.old model.profileRepack origin shelf w := rfl

variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
set_option hygiene false
set_option quotPrecheck false
local notation "wire" => S.epochPower^S.priceExponent
local notation "s" => S.firstWidth G.b p
local notation "price" => (1/((s:ℝ)*(wire:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => price*(wire:ℝ)
local notation "Ht" => GroupStage.depthBound (atRound S.rounds) n f g
variable {he : 0 ≤ fee} {hu : 0 ≤ u} {radix : S.radix=2^k}
variable {run : Epochs G hu he (h:=h) (C:=C) («Ht»:=Ht) (t:=S.rounds) S.height
      (initial X S.copies s (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he run).Choice} (br : Branch X G S radix R run c)
local notation "P" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width)))
local notation "bits" => (fun _ : P=>s*1)
variable {W : MarkedWorld F 0 P bits} {i z D z' D' : ℕ} {rate : ℝ}
    {prior : Reached W G price fee S k i z D wire s} {T : StageInput W G rate fee}
    {nonneg : 0 ≤ fee} {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G price fee S k (i+1) z' D' wire s}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path br.origin.source prior) (tail : Path next br.target)
    (cut : (Path.ordinary before ticket).append tail=br.path)
local notation "A" => prior.placement
local notation "calendar" => capCalendar G.b S.rounds g S.height



variable (op:RotorSpec) (frozen drift degree payload seats root:ℕ) (ports:DatePorts)
    (ordinary:ℕ→Ordinary)
local notation "books" => OrdinaryBooks.atDate G S op g k i p frozen drift degree payload seats ports
local notation "base" => (books).onTicket ticket g frozen p f payload seats ports.venue.lanes ports.io.roster ordinary
local notation "v" => DatePorts.ordinaryModel ports ticket op g frozen p f drift degree payload seats root ordinary
local notation "d₀" => DonorDate.atDate G S g k i p
local notation "start" => PhysicalOrdinary.StaticCore.profileStart G S g k i p payload seats root

local notation "core" => PhysicalOrdinary.StaticCore.atAge G S g k i p payload seats root ports.io.roster
local notation "paid" => (StageVenueTail.Date.atOrdinary G S g k frozen p f payload ordinary i ports.venue.lanes).paidBits


local notation "clip" => OrdinaryBooks.purchaseClip G books core ports paid
local notation "purchased" => OrdinaryBooks.purchased G books core ports paid
local notation "entry" => (base).registeredEntry ports ((base).stageStart root)

local notation "argData" => PhysicalOrdinary.bareData G S i payload seats start (S.censusBits p)
  ports core purchased clip
local notation "cap₀" => Nat.le_max_left ports.argumentsPerNode (S.retainedArgumentsAt G drift)
local notation "m₀" => (base).registered_match ports ((base).stageStart root) cap₀
local notation "actual" => (v).bareArguments ((base).stageStart root) entry m₀

local notation "sh" => (base).registered_geometry ports ((base).stageStart root)
local notation "regs" => VenueProgram.Registered.atAge G S op g k i p frozen f drift degree payload seats root ports ordinary
local notation "floor" => (v).stageStart root
variable (w shelf header : ℕ) (pos : 0<k)
variable (room : DatePorts.OrdinaryCodeRoom ports ticket op g frozen p f drift degree payload seats root ordinary w)
local notation "fits" => DatePorts.MachineFits ports G S op g k i p frozen f drift degree payload seats root ordinary
local notation "actualRegs" => (v).returnRegisters floor entry room.paths

attribute [local irreducible] DonorDate.codeLoadedAfter VenueProgram.Registered.body
  PhysicalOrdinary.bareData OrdinaryBooks.purchased OrdinaryBooks.purchaseClip

set_option maxHeartbeats 750000 in
include before tail cut in
theorem registered_machine :
    ∃ h:fits,
      ports.ordinaryDate ticket op g frozen p f drift degree payload seats root ordinary w shelf header pos room=
      ports.commonOrdinary G S op g k i p frozen f drift degree payload seats root ordinary w shelf header pos h :=by
  have common:=(registered_purchased_books X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary)
  have coreEq:=registered_static_core X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary
  have regsEq : actualRegs=regs:=registered_return_inputs X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary
    purchased clip common.1 common.2 room.paths (regs).paths
  obtain ⟨valid,equal⟩:=registered_bare_at X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary
  have real : (actualRegs).BodyFits actual:=(base).registered_body_fits root ports cap₀ room.signed room.blocks room.paths room.slots
  have good : (regs).BodyFits ((argData).plan valid):=regsEq ▸ equal ▸ real
  let h:fits:=⟨valid,good⟩
  refine ⟨h,?_⟩
  have body:=(base).registered_body root ports w cap₀ room.signed room.blocks room.paths room.slots rfl
  have codeEq:=body.trans (VenueProgram.Registered.body_congr G actualRegs actual start ports w
    regsEq equal real good)
  have area : (v).area=(regs).core.area:=congrArg PhysicalOrdinary.StaticCore.area coreEq
  have meas:=congrArg PhysicalOrdinary.StaticCore.measures coreEq
  let d:=DonorDate.atDate G S g k i p
  let c:=(v).signedInput floor room.signed
  let native:=(v).issuedResult root ports entry room.signed w m₀ sh room.blocks room.paths room.slots
  let realLoad:=(v).archivePhase root shelf w
  have issued :
      ports.ordinaryDate ticket op g frozen p f drift degree payload seats root ordinary w shelf header pos room =
      d.codeLoadedAfter G pos payload seats (S.censusBits p) start header w ports.io ((v).staticCore floor).measures
          realLoad.program realLoad.ticks native.printed.program native.printed.ticks :=
    (v).date_result_code root ports.io ports.archive.count entry room.signed m₀ room.paths
      ((v).nativeTicketExpr floor room.signed entry m₀ sh room.blocks)
      ((v).nativeTicketPreparation floor w room.signed entry m₀ sh room.blocks ⟨0,Nat.mul_pos (by decide) room.slots⟩)
      ((v).reachedSources floor) room.chip sh room.endFit room.packed room.radix room.funded shelf header room.result d pos
  rw [issued]
  have loader : PrintedStep.ofPhase realLoad=
      DatePorts.profileCode (regs).core.area ports.io.roster
        ⟨seats,DescentPackedEpochShelves.grain (payload/2) G.C,
          (regs).core.area.lanesAt*(regs).core.area.shapeAt.pairs,DescentTerminalEpochBits.width G.C⟩ root shelf w:=by
    have pitch : (v).profileRepack =
        ⟨seats, DescentPackedEpochShelves.grain (payload/2) G.C,
          (regs).core.area.lanesAt*(regs).core.area.shapeAt.pairs, DescentTerminalEpochBits.width G.C⟩ := rfl
    have old : (v).old = ports.io.roster := rfl
    apply (archive_profile_code (v) root shelf w).trans
    rw [pitch, old, area]
  have lp := congrArg PrintedStep.program loader
  have lt := congrArg PrintedStep.ticks loader
  dsimp only [DatePorts.commonOrdinary]
  rw [show native=(regs).body G ((argData).plan valid) start ports w good from codeEq,
      meas, show realLoad.program=_ from lp, show realLoad.ticks=_ from lt]
  rfl

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
