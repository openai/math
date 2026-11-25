import OAI.Hierarchy.DescentNamedRegisteredArgumentCost
import OAI.Hierarchy.DescentRegisteredOrdinarySize

namespace OAI
/-! # The entire ordinary allocation on an original named cut is public -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryBooks
open DescentDatedAddressBook DescentOrdinaryVenueIngress DescentSIMDLookup
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) (b : OrdinaryBooks)
    (core : PhysicalOrdinary.StaticCore) (ports : DatePorts) (paidBits : ℕ)

def purchaseClip : Clip :=
  PhysicalOrdinary.fundedClipAt core.area core.format core.donor.amount paidBits
    (b.argumentCost G core ports paidBits)

def purchased : OrdinaryBooks :=
  let c:=purchaseClip G b core ports paidBits
  let cells:=b.clipped core.area c
  let role:=DescentPrimitivePalette.printedBits G b.palette.seedWidth b.palette.grainLimit b.palette.rotor
  cells.paid core c (ports.argumentLayout (2^core.area.k)) G.b ports.roleLanes role core.area.profile

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryBooks

namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
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

local notation "core" => PhysicalOrdinary.StaticCore.atAge G S g k i p payload seats root ports.io.roster
local notation "paid" => (StageVenueTail.Date.atOrdinary G S g k frozen p f payload ordinary i ports.venue.lanes).paidBits


local notation "clip" => OrdinaryBooks.purchaseClip G books core ports paid
local notation "purchased" => OrdinaryBooks.purchased G books core ports paid
local notation "entry" => (base).registeredEntry ports ((base).stageStart root)

include before tail cut in
theorem registered_purchased_books :
    (v).books=purchased ∧ (entry).clip=clip := by
  let floor:=(base).stageStart root
  have fixed : (base).staticCore floor=core :=
    registered_static_core X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary
  have area : (base).area=(core).area :=congrArg PhysicalOrdinary.StaticCore.area fixed
  have donor : (base).ticket.donorDate=(core).donor :=congrArg PhysicalOrdinary.StaticCore.donor fixed
  have format : (base).ticket.depotShape (base).short=(core).format :=
    congrArg PhysicalOrdinary.StaticCore.format fixed
  have dig:= (issued_return_fields X G S br ticket before tail cut (books) frozen payload seats
    ports.venue.lanes ports.io.roster ordinary).1
  have nominal : (base).ticket.depotShape (base).short=(base).ticket.donorDate.format :=by rw [dig]; rfl
  have fcore : (base).ticket.donorDate.format=(core).format:=nominal.symm.trans format
  have cost_eq:=registered_argument_cost_eq X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary
  have c : (base).fundedClip ((base).argumentUnitFrom ports floor)=clip :=by
    rw [(base).fundedClip_named _ dig rfl,cost_eq,area,fcore]
    unfold OrdinaryBooks.purchaseClip
    rw [donor]
    rfl
  have epoch : (base).profile=(core).area.profile :=by rw [←area]; rfl
  refine ⟨?_,c⟩
  change ((base).registeredFrom ports floor).books=_
  rw [(base).registered_paid_books ports floor]
  unfold OrdinaryBooks.purchased
  change ((books).clipped (base).area ((base).fundedClip ((base).argumentUnitFrom ports floor))).paid
      ((base).staticCore floor) ((base).fundedClip ((base).argumentUnitFrom ports floor))
      (ports.argumentLayout (2^(base).area.k)) G.b ports.roleLanes _ (base).profile=_
  rw [c,fixed,area,epoch]
  rfl

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
