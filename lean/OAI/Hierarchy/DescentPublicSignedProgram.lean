import OAI.Hierarchy.DescentMaterialProgramEquality
import OAI.Hierarchy.DescentOrdinaryVenueCalendarRead
import OAI.Hierarchy.DescentNamedSignedDate

namespace OAI
/-! # Construct the entire signed program from the two dates and their prior word banks -/
namespace Hierarchy.DescentDatedAddressBook.SignedProgram
open DescentSixParty DescentCompiler DescentSixParty.Chronology DescentSIMDLookup DescentHostDegree
open DescentPacking.PackedMatch.Local.Stage DescentRawCablePanel
noncomputable section

def ofData (a : Dated.Ordinary) (d : DonorDate) (s : SignedExtent)
    (nextH nextD payload start : ℕ) : SignedProgram :=
  let e:=StageVenueTail.OrdinaryReturn.materialFor a d s payload
  let slots:=2^packExponent 20 d.rankDegree+2
  let setup : DepotRAM.Material.Setup:=
    ⟨DescentTerminalEpochBits.width d.colors,d.branch,d.exponent,gainExponent 20 d.rankDegree,slots,
      (2^(d.exponent+1)-1)*slots,s.fieldBits⟩
  let m : DescentOrdinaryMarkProject.Shape:=
    ⟨s.reach,2^d.exponent,d.cap,d.degree,a.H,s.hosts,s.groups,s.blocks,a.lanesAt,s.lanes⟩
  ⟨s,⟨e,d.format,setup⟩,m,a.H,a.D,nextH,nextD,start⟩

def atAge {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule)
    (gain k i p b payload unit seats floor : ℕ) (old : ProtocolRAM.Bank) : SignedProgram :=
  let H:=NativePitch.incomingHosts S (i+1)
  let a:=Dated.forAge S G.b gain k i (Nat.clog 2 (S.hostSize i)) b payload unit (DescentTerminalEpochBits.width G.C) seats
  let d:=DonorDate.atDate G S gain k i p
  let stage:=SignedStage.atDate G S gain k i H
  ofData a d (stage.format payload) H stage.newDegree payload (d.endAddress payload (a.rotationEnd old floor))

end
end Hierarchy.DescentDatedAddressBook.SignedProgram

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentCompiler
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

theorem signed_program_data (floor : ℕ)
    (short : v.short=max (v.k+3) (Nat.clog 2 (v.prior.placement.degree+1)))
    (profile : v.profile=DescentTerminalEpochBits.width v.gadget.C) :
    v.signedProgram floor=SignedProgram.ofData v.area v.ticket.donorDate v.signed v.venue.hosts v.venue.degree
      v.payload (v.donorEnd floor) := by
  unfold signedProgram materialProgram material materialFormat materialPitch
  rw [short,profile]
  rfl

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
set_option hygiene false
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


include ticket before tail cut in
theorem public_signed_program (old : ProtocolRAM.Bank) (floor b payload unit seats : ℕ) :
    let profile:=DescentTerminalEpochBits.width G.C
    let ℓ:=Nat.clog 2 (S.hostSize i)
    let a:=ticket.ordinaryArea ℓ b payload unit profile seats
    let H':=NativePitch.incomingHosts S (i+1)
    let actual : SignedStage:=⟨k,prior.placement.degree,prior.placement.cap,next.placement.degree,next.placement.cap,
      hostRows (S.hostSize i),H',S.groupCount (i+1),G.b,G.C,G.k⟩
    let short:=max (k+3) (Nat.clog 2 (prior.placement.degree+1))
    let start:=ticket.endAddress old floor ℓ b short payload unit profile seats
    SignedProgram.ofData a ticket.donorDate (actual.format payload) H' next.placement.degree payload start=
      SignedProgram.atAge G S g k i p b payload unit seats floor old := by
  intro profile ℓ a H' actual short start
  have core:=ordinary_return_core X G S br ticket before tail cut old floor b payload unit seats
  have stage:actual=SignedStage.atDate G S g k i H':=signed_stage_eq X G S br ticket before tail cut H'
  have degree:=congrArg SignedStage.newDegree stage
  change next.placement.degree=(SignedStage.atDate G S g k i H').newDegree at degree
  unfold SignedProgram.atAge
  change SignedProgram.ofData a ticket.donorDate (actual.format payload) H' next.placement.degree payload start=_
  rw [show a=_ from core.1,core.2.1,stage,degree,show start=_ from core.2.2]

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
