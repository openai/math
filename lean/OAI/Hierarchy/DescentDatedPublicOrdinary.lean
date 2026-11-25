import OAI.Hierarchy.DescentDatedOrdinaryRasterExtent
import OAI.Hierarchy.DescentDatedMaterialExtent
import OAI.Hierarchy.DescentOrdinaryVenueExtent
import OAI.Hierarchy.DescentNamedDonorCode
import OAI.Hierarchy.DescentIssuedDonorSpan
import OAI.Hierarchy.DescentDatedOrdinaryOutput
import OAI.Hierarchy.DescentDatedPriorOperand
import OAI.Hierarchy.DescentDatedOrdinaryCountRoof

namespace OAI
/-! # Public addresses for the original seed-named ordinary date, independent of the chosen cuts -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated
open DescentSixParty.Chronology ProtocolRAM
noncomputable section
/-- All of the data consumed here are program parameters, including the *addresses* of older
archives. The prior roster's contents, matches, selected rotor and counter values are arbitrary. -/
def ordinaryStop (v : Ordinary) (depot : DonorDate) (V : DescentOperandVectorArena.Layout)
    (R : DescentDatedPriorOperand.Layout) (old : Bank) (payload base : ℕ) :=
  R.endAddress (V.endAddress (depot.endAddress payload (v.rotationEnd old base)))
end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated

namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
local notation "wire" => S.epochPower^S.priceExponent
local notation "s" => S.firstWidth G.b p
local notation "price" => (1/((s:ℝ)*(wire:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => price*(wire:ℝ)
local notation "Ht" => GroupStage.depthBound (atRound S.rounds) n f g
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
    {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
      (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix=2^k}
variable {run : Epochs G hu he (h:=h) (C:=C) («Ht»:=GroupStage.depthBound (atRound S.rounds) n f g)
      (t:=S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he run).Choice}
    (br : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R run c)
local notation "P" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width)))
local notation "bits" => (fun _ : P=>s*1)
variable {W : MarkedWorld F 0 (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width))) (fun _ => S.firstWidth G.b p*1)} {i z D z' D' : ℕ} {rate : ℝ}
    {prior : Reached W G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k i z D (S.epochPower^S.priceExponent) (S.firstWidth G.b p)} {T : StageInput W G rate (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)}
    {nonneg : 0 ≤ (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)} {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k (i+1) z' D' (S.epochPower^S.priceExponent) (S.firstWidth G.b p)}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path br.origin.source prior) (tail : Path next br.target)
    (cut : (Path.ordinary before ticket).append tail=br.path)
local notation "A" => prior.placement
local notation "calendar" => capCalendar G.b S.rounds g S.height


include ticket before tail cut in
theorem ordinary_stop (old : ProtocolRAM.Bank) (vector : DescentOperandVectorArena.Layout)
    (resolver : DescentDatedPriorOperand.Layout) (b payload unit seats base : ℕ) :
    let ℓ:=Nat.clog 2 (S.hostSize i)
    let short:=max (k+3) (Nat.clog 2 ((A).degree+1))
    let prof:=DescentTerminalEpochBits.width G.C
    let pub:=forAge S G.b g k i ℓ b payload unit prof seats
    resolver.endAddress (ticket.outputEnd old vector base ℓ b short payload unit prof seats)=
      ordinaryStop pub (DonorDate.atDate G S g k i p) vector resolver old payload base := by
  intro ℓ short prof pub
  have geom:=ordinary_geometry X G S br ticket before tail cut ℓ b payload unit prof seats
  have name:=donor_date_eq X G S br ticket before tail cut
  unfold ordinaryStop OrdinaryLink.outputEnd OrdinaryLink.endAddress
  rw [←name]
  change resolver.endAddress (vector.endAddress (ticket.wholeDonorEnd short prof (2^ℓ) payload
      ((ticket.ordinaryArea ℓ b payload unit prof seats).rotationEnd old base)))=_
  rw [show ticket.ordinaryArea ℓ b payload unit prof seats=pub from geom]
  exact congrArg (fun x => resolver.endAddress (vector.endAddress x))
    (ticket.public_donor_end payload (pub.rotationEnd old base))

include ticket before tail cut in
/-- The signed output, repacking for the following stage and the surviving-count word
share one absolute end over every original choice at this scheduled ordinary date. -/
theorem ordinary_full_stop (old : ProtocolRAM.Bank) (vector : DescentOperandVectorArena.Layout)
    (resolver : DescentDatedPriorOperand.Layout) (profile : DescentDatedAddressBook.ProfileRepack)
    (material : DescentDatedAddressBook.MaterialExtent)
    (signed : DescentDatedAddressBook.SignedExtent) (venue : StageVenueTail.Date)
    («meta» : DescentDatedAddressBook.MetadataReturn) (book : DescentOrdinaryFinal.Chart)
    (refs:DescentOrdinaryRefsROM.Chart)(born:DescentOrdinaryBorn.Chart)
    (palette:DescentOrdinaryPrimitiveCheckpoint.Layout)(ingressWords rasterLanes routeWords:ℕ)
    (b payload unit seats base : ℕ) :
    let ℓ:=Nat.clog 2 (S.hostSize i)
    let short:=max (k+3) (Nat.clog 2 ((A).degree+1))
    let prof:=DescentTerminalEpochBits.width G.C
    let actual:=ticket.ordinaryArea ℓ b payload unit prof seats
    let pub:=forAge S G.b g k i ℓ b payload unit prof seats
    let lo:=profile.endAddress base
    let afterDonor:=fun (a:Ordinary) n=>
      let begins:=DescentDatedAddressBook.PriorHeader.endAddress a.H signed.groups signed.lanes signed.degree n
      let peers:=DescentOrdinaryVenueReturn.roof (material.endAddress begins) a.H a.D venue.hosts venue.degree
      let marks:DescentOrdinaryMarkProject.Shape:=
        ⟨signed.reach,2^a.k,a.cap,a.D,a.H,signed.hosts,signed.groups,signed.blocks,a.lanesAt,signed.lanes⟩
      let start:=signed.roof (marks.endAddress peers)+ingressWords+refs.extent
      let stored:=resolver.endAddress (vector.endAddress (born.endAddress start)+routeWords)
      let inputs:=venue.endAddress (StageVenueTail.OrdinaryRaster.roof a venue rasterLanes stored)
      palette.roof (DescentOrdinaryPaletteBirth.roof born (book.endAddress («meta».ordinaryEnd inputs)))
    DescentOrdinaryCountScan.endAddress (actual.shapeAt.outputBits*actual.lanesAt)
      (afterDonor actual (ticket.endAddress old lo ℓ b short payload unit prof seats)) actual.batch=
    DescentOrdinaryCountScan.endAddress (pub.shapeAt.outputBits*pub.lanesAt)
      (afterDonor pub ((DonorDate.atDate G S g k i p).endAddress payload (pub.rotationEnd old lo))) pub.batch:=by
  intro ℓ short prof actual pub lo afterDonor
  have geom:actual=pub:=ordinary_geometry X G S br ticket before tail cut ℓ b payload unit prof seats
  have named:=donor_date_eq X G S br ticket before tail cut
  have original:ticket.endAddress old lo ℓ b short payload unit prof seats=
      (DonorDate.atDate G S g k i p).endAddress payload (pub.rotationEnd old lo):=by
    unfold OrdinaryLink.endAddress
    rw [←named]
    change ticket.wholeDonorEnd short prof (2^ℓ) payload (actual.rotationEnd old lo)=_
    rw [geom]
    exact ticket.public_donor_end payload (pub.rotationEnd old lo)
  rw [geom,original]

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
