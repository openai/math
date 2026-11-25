import OAI.Hierarchy.DescentRegisteredReturnProgram
import OAI.Hierarchy.DescentNamedPurchasedOrdinaryBooks

namespace OAI
/-! # Public funded and returned native instructions at the actual ordinary cut -/
namespace Hierarchy.DescentSixParty.Chronology.VenueProgram.Registered
open DescentCompiler DescentPacking.PackedMatch.Local.Stage
noncomputable section
/-- The returned register description is available before selecting any graph, including
its exact socket arity at the predetermined original public degree. -/
def atAge {F:Type} [Field F] (G:PoweredGadget F) (S:AtomSchedule) (op:RotorSpec)
    (gain k i p tail f drift degree payload seats root:ℕ) (ports:DatePorts) (ordinary:ℕ→Dated.Ordinary):Registered:=
  let books:=OrdinaryBooks.atDate G S op gain k i p tail drift degree payload seats ports
  let c:=PhysicalOrdinary.StaticCore.atAge G S gain k i p payload seats root ports.io.roster
  let d:=StageVenueTail.Date.atOrdinary G S gain k tail p f payload ordinary i ports.venue.lanes
  let clip:=OrdinaryBooks.purchaseClip G books c ports d.paidBits
  let bought:=OrdinaryBooks.purchased G books c ports d.paidBits
  ⟨c,bought,{d with paidLanes:=clip.postPitch,aliveLanes:=clip.postPitch},clip,rfl⟩
end
end Hierarchy.DescentSixParty.Chronology.VenueProgram.Registered

namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentOrdinaryVenueIngress StageVenueTail
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

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

local notation "floor" => (v).stageStart root
local notation "entry" => (base).registeredEntry ports start
local notation "core" => PhysicalOrdinary.StaticCore.atAge G S g k i p payload seats root ports.io.roster
local notation "rawDate" => Date.atOrdinary G S g k frozen p f payload ordinary i ports.venue.lanes

local notation "clip₀" => OrdinaryBooks.purchaseClip G books core ports (rawDate).paidBits
local notation "selectedBooks" => OrdinaryBooks.purchased G books core ports (rawDate).paidBits

include before tail cut in
/-- A named cut's original return program depends on the physical allocator's books
and clip. The selected stage and its region of signed ports are already fixed by the
original age, including the final fill of the public lane. -/
theorem registered_return_inputs (selected:OrdinaryBooks) (clip:Clip)
    (gotBooks:(v).books=selected) (gotClip:(entry).clip=clip)
    (paths:(entry).clip.venue.paths=OrdinaryRaster.paths (v).area)
    (truePaths:clip.venue.paths=OrdinaryRaster.paths (core).area):
    (v).returnRegisters floor entry paths=
      ⟨core,selected,{rawDate with paidLanes:=clip.postPitch,aliveLanes:=clip.postPitch},clip,truePaths⟩:=by
  apply VenueProgram.Registered.ext
  · exact registered_static_core X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary
  · exact gotBooks
  · change {rawDate with paidLanes:=(entry).clip.postPitch,aliveLanes:=(entry).clip.postPitch}=
      {rawDate with paidLanes:=clip.postPitch,aliveLanes:=clip.postPitch}
    rw [gotClip]
  · exact gotClip

include before tail cut in
theorem registered_return_codes (selected:OrdinaryBooks) (clip:Clip)
    (gotBooks:(v).books=selected) (gotClip:(entry).clip=clip)
    (paths:(entry).clip.venue.paths=OrdinaryRaster.paths (v).area)
    (truePaths:clip.venue.paths=OrdinaryRaster.paths (core).area)
    (w:ℕ) (fund:(v).FundedRoom floor ((v).fundedFromEntry floor entry paths) ports.io w)
    (result:(v).ResultRoom floor ((v).reachedSources floor) w):
    let assigned:VenueProgram.Registered:=
      ⟨core,selected,{rawDate with paidLanes:=clip.postPitch,aliveLanes:=clip.postPitch},clip,truePaths⟩
    PrintedStep.ofPhase ((v).fundedRaster floor ((v).fundedFromEntry floor entry paths) ports.io w fund)=
      assigned.fundedCode ports.io w ∧
    PrintedStep.ofPhase ((v).returnPhase floor ((v).reachedSources floor) w result)=assigned.returnCode w:=by
  intro assigned
  have erased:=registered_return_inputs X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary
    selected clip gotBooks gotClip paths truePaths
  have printed:=(v).returned_registers floor entry ports.io w paths rfl fund result
  exact ⟨printed.1.trans (congrArg (fun x:VenueProgram.Registered=>x.fundedCode ports.io w) erased),
    printed.2.trans (congrArg (fun x:VenueProgram.Registered=>x.returnCode w) erased)⟩

include before tail cut in
theorem registered_program_paths (paths:(entry).clip.venue.paths=OrdinaryRaster.paths (v).area):
    (clip₀).venue.paths=OrdinaryRaster.paths (core).area:=by
  have accepted:=registered_purchased_books X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary
  have fixed:=registered_static_core X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary
  exact ((congrArg (fun a:Clip=>a.venue.paths) accepted.2).symm.trans paths).trans
    (congrArg (fun c:PhysicalOrdinary.StaticCore=>OrdinaryRaster.paths c.area) fixed)

include before tail cut in
theorem registered_programs_at (paths:(entry).clip.venue.paths=OrdinaryRaster.paths (v).area)
    (w:ℕ) (fund:(v).FundedRoom floor ((v).fundedFromEntry floor entry paths) ports.io w)
    (result:(v).ResultRoom floor ((v).reachedSources floor) w):
    let published:=registered_program_paths X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary paths
    let assigned:VenueProgram.Registered:=
      ⟨core,selectedBooks,{rawDate with paidLanes:=(clip₀).postPitch,aliveLanes:=(clip₀).postPitch},clip₀,published⟩
    PrintedStep.ofPhase ((v).fundedRaster floor ((v).fundedFromEntry floor entry paths) ports.io w fund)=
      assigned.fundedCode ports.io w ∧
    PrintedStep.ofPhase ((v).returnPhase floor ((v).reachedSources floor) w result)=assigned.returnCode w:=by
  intro published assigned
  obtain ⟨bought,used⟩:=registered_purchased_books X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary
  exact registered_return_codes X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary
    selectedBooks clip₀ bought used paths published w fund result

include before tail cut in
theorem ordinary_programs_at (paths:(entry).clip.venue.paths=OrdinaryRaster.paths (v).area)
    (w:ℕ) (fund:(v).FundedRoom floor ((v).fundedFromEntry floor entry paths) ports.io w)
    (result:(v).ResultRoom floor ((v).reachedSources floor) w):
    let assigned:=VenueProgram.Registered.atAge G S op g k i p frozen f drift degree payload seats root ports ordinary
    PrintedStep.ofPhase ((v).fundedRaster floor ((v).fundedFromEntry floor entry paths) ports.io w fund)=
      assigned.fundedCode ports.io w ∧
    PrintedStep.ofPhase ((v).returnPhase floor ((v).reachedSources floor) w result)=assigned.returnCode w:=
  registered_programs_at X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary paths w fund result

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
