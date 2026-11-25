import OAI.Hierarchy.DescentSelectedReturnPrefix
import OAI.Hierarchy.DescentPublicSignedProgram
import OAI.Hierarchy.DescentOrdinaryTicketChart

namespace OAI
/-! # The identical public prefix and its word charge on the actual named trajectory -/
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



variable (books : OrdinaryBooks) (frozen payload seats hostLanes : ℕ) (old : ProtocolRAM.Bank)
    (ordinary : ℕ→Ordinary)
local notation "v" => books.onTicket ticket g frozen p f payload seats hostLanes old ordinary
local notation "pub" => DonorDate.atDate G S g k i p
local notation "short₀" => max (k+3) (Nat.clog 2 (prior.placement.degree+1))

include before tail cut in
theorem issued_return_fields :
    (v).short=short₀ ∧ (v).unit=ticket.donorDate.amount ∧
    (v).venue.degree=next.placement.degree ∧ (v).withIssuedSigned=v :=by
  have chart:=donor_date_eq X G S br ticket before tail cut
  have d:=congrArg DonorDate.degree chart
  have e : (v).short=short₀:=by
    change max (k+3) (Nat.clog 2 ((pub).degree+1))=_
    rw [←d];rfl
  have unit_eq : (v).unit=ticket.donorDate.amount:=congrArg DonorDate.amount chart.symm
  have degree:=congrArg StageVenueTail.Date.degree
    (venue_date_eq X G S br ticket before tail cut frozen payload hostLanes ordinary)
  have shape : (v).signedLayout.format payload=(v).signed:=signed_at X G S br ticket before tail cut payload
  refine ⟨e,unit_eq,degree.symm,?_⟩
  change {v with signed:=(v).signedLayout.format payload}=v
  rw [shape]

include before tail cut in
theorem issued_return_program (floor : ℕ) :
    (v).signedProgram floor=SignedProgram.atAge G S g k i p (S.censusBits p) payload (pub).amount seats floor old :=by
  have data:=issued_return_fields X G S br ticket before tail cut books frozen payload seats hostLanes old ordinary
  have shape:=signed_at X G S br ticket before tail cut payload
  rw [(v).signed_program_data floor data.1 rfl]
  let ℓ:=Nat.clog 2 (S.hostSize i)
  let field:=DescentTerminalEpochBits.width G.C
  let a:=ticket.ordinaryArea ℓ (S.censusBits p) payload (pub).amount field seats
  let H':=NativePitch.incomingHosts S (i+1)
  let actual:SignedStage:=⟨k,prior.placement.degree,prior.placement.cap,next.placement.degree,next.placement.cap,
    hostRows (S.hostSize i),H',S.groupCount (i+1),G.b,G.C,G.k⟩
  have bound : (v).donorEnd floor=ticket.endAddress old floor ℓ (S.censusBits p) short₀ payload (pub).amount field seats:=by
    change ticket.endAddress old floor ℓ (S.censusBits p) (v).short payload (pub).amount field seats=_
    rw [data.1]
  change SignedProgram.ofData a ticket.donorDate (v).signed H' (v).venue.degree payload ((v).donorEnd floor)=_
  rw [show (v).signed=actual.format payload from shape.symm,data.2.2.1,bound]
  exact public_signed_program X G S br ticket before tail cut old floor (S.censusBits p) payload (pub).amount seats

include before tail cut in
theorem named_return_bill {t reset J M tailSize : ℕ}
    (cal : S=stageNumbers G t J f g reset M tailSize)
    (kfit : k=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g))
    (live : 0<S.hostSize i) (floor w ratio : ℕ) (parts adj : ProtocolRAM.Bank)
    (oldSources : DescentOrdinaryVenueReturn.Sources) (input : Operands)
    (room : (v).MarkRoom floor input w)
    (oldRoom : 2*scale J (donorRates G t f g reset).amount≤payload)
    (newRoom : 2*scale J (signedRates G t f g reset).amount≤payload)
    (bus : w≤ratio*payload) :
    ((v).signedReturnPrefix floor w parts adj oldSources input).wordInvoice≤
      ratio*scale J (returnRate G t f g reset)*MaterialProgram.purchased (S.hostSize i) (S.groupCount i) payload := by
  have issuedFields:=issued_return_fields X G S br ticket before tail cut books frozen payload seats hostLanes old ordinary
  have mark : (v).withIssuedSigned.MarkRoom floor input w:=issuedFields.2.2.2.symm ▸ room
  exact (v).signed_return_bill cal kfit issuedFields.1 rfl rfl rfl issuedFields.2.2.1 issuedFields.2.1
    (signed_source_capacity X G S br ticket before tail cut) live floor w ratio parts adj oldSources input
    mark oldRoom newRoom bus

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
