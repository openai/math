import OAI.Hierarchy.DescentDatedOrdinaryVenueModel
import OAI.Hierarchy.DescentNamedOrdinaryVenue
import OAI.Hierarchy.DescentDatedPublicOrdinary

namespace OAI
/-! # Addresses and programs for ordinary return depend only on their original date -/
namespace Hierarchy.DescentSixParty.StageVenueTail
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage.Dated DescentSIMDLookup ProtocolRAM
noncomputable section
set_option quotPrecheck false

/-- The complete inputs to the public address calculation, starting at the donor's last store. -/
structure OrdinaryReturn where
  area:Ordinary
  material:MaterialExtent
  signed:SignedExtent
  venue:Date
  work:ℕ
  ingressWords:ℕ
  reference:DescentOrdinaryRefsROM.Chart
  born:DescentOrdinaryBorn.Chart
  vector:DescentOperandVectorArena.Layout
  routeWords:ℕ
  resolver:DescentDatedPriorOperand.Layout

namespace OrdinaryReturn
def materialFor (a:Ordinary)(d:Chronology.DonorDate)(s:SignedExtent)(payload:ℕ):MaterialExtent:=
  ⟨a.H,a.G,lanes payload d.amount,s.hosts,s.groups,s.lanes,d.format.blocks,s.reach,d.format.cap,
    DescentRawCablePanel.DepotRAM.totalBits d.format+DescentRawCablePanel.DepotRAM.chartBits d.format,s.fieldBits⟩

def place (ports:OrdinaryReturn)(a:Ordinary)(d:Chronology.DonorDate)(s:SignedExtent)(v:Date)(payload:ℕ):OrdinaryReturn:=
  {ports with area:=a,material:=materialFor a d s payload,signed:=s,venue:=v}

variable (c:OrdinaryReturn)(donor:ℕ)

def materialEnd:=c.material.endAddress (PriorHeader.endAddress c.area.H c.signed.groups c.signed.lanes c.signed.degree donor)
def peers:=DescentOrdinaryVenueReturn.roof (c.materialEnd donor) c.area.H c.area.D c.venue.hosts c.venue.degree
def marks:DescentOrdinaryMarkProject.Shape:=
  ⟨c.signed.reach,2^c.area.k,c.area.cap,c.area.D,c.area.H,c.signed.hosts,c.signed.groups,c.signed.blocks,c.area.lanesAt,c.signed.lanes⟩
def markEnd:=c.marks.endAddress (c.peers donor)
def resultEnd:=c.resolver.endAddress (c.vector.endAddress (c.born.endAddress
    (c.signed.roof (c.markEnd donor)+c.ingressWords+c.reference.extent))+c.routeWords)
def stop:=OrdinaryRaster.sweep c.area c.venue c.work (c.resultEnd donor)
def rasterEnd:=OrdinaryRaster.roof c.area c.venue c.work (c.resultEnd donor)

def wire (x j:ℕ):Bank:=
  if hx:x<c.signed.blocks then
    if hj:j<2*c.signed.cap then c.signed.page (c.markEnd donor) ⟨x,hx⟩ ⟨j,hj⟩ else ⟨0,0⟩
  else ⟨0,0⟩

def sources:Sources:=
  ⟨DescentOrdinaryPeerRows.peers (c.materialEnd donor) c.area.H c.area.D c.venue.hosts c.venue.degree,
   DescentOrdinaryVenueReturn.hubs (c.materialEnd donor) c.area.H c.area.D c.venue.hosts c.venue.degree,
   DescentOrdinaryRasterReturn.actorBank (OrdinaryRaster.dims c.area c.venue c.work) (c.stop donor),
   DescentOrdinaryRasterReturn.paidBank (OrdinaryRaster.dims c.area c.venue c.work) (c.stop donor),
   c.wire donor⟩
end OrdinaryReturn
end
end Hierarchy.DescentSixParty.StageVenueTail

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open StageVenueTail DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage.Dated
noncomputable section
set_option quotPrecheck false
variable {F P:Type} [Field F](v:PhysicalOrdinary F P)

def returnChart:OrdinaryReturn:=
  ⟨v.area,v.material,v.signed,v.venue,v.rasterLanes,v.ingressWords,v.reference,v.bornBook,v.vector,v.routeWords,v.resolver⟩

theorem source_chart (floor:ℕ):v.reachedSources floor=v.returnChart.sources (v.donorEnd floor):=rfl
theorem raster_chart (floor:ℕ):v.rasterEnd floor=v.returnChart.rasterEnd (v.donorEnd floor):=rfl

theorem material_fields (short:v.short=max (v.k+3) (Nat.clog 2 (v.prior.placement.degree+1)))
    (profile:v.profile=DescentTerminalEpochBits.width v.gadget.C):
    v.material=OrdinaryReturn.materialFor v.area v.ticket.donorDate v.signed v.payload:=by
  unfold material OrdinaryReturn.materialFor
  rw [short,profile]; rfl

/-- Only public dates and the numeric output shapes of the preceding source programs
    enter the memory layout. No value of a matched row or live wire is inspected. -/
theorem chart_fields (a:Ordinary)(donor:DonorDate)(s:DescentDatedAddressBook.SignedExtent)(d:Date)
    (short:v.short=max (v.k+3) (Nat.clog 2 (v.prior.placement.degree+1)))
    (profile:v.profile=DescentTerminalEpochBits.width v.gadget.C)
    (area:v.area=a)(date:v.ticket.donorDate=donor)(signed:v.signed=s)(venue:v.venue=d):
    v.returnChart=⟨a,OrdinaryReturn.materialFor a donor s v.payload,s,d,v.rasterLanes,v.ingressWords,
      v.reference,v.bornBook,v.vector,v.routeWords,v.resolver⟩:=by
  unfold returnChart
  rw [v.material_fields short profile,area,date,signed,venue]

/-- The same chronological donor address and printed numeric date determine every
    reached output pointer, every returned instruction, and all target operand pointers. -/
theorem return_at (floor donor w:ℕ)(date:OrdinaryReturn)(same:v.returnChart=date)(start:v.donorEnd floor=donor):
    v.reachedSources floor=date.sources donor ∧ v.rasterEnd floor=date.rasterEnd donor ∧
    v.venue.operands (v.reachedSources floor) (v.rasterEnd floor)=date.venue.operands (date.sources donor) (date.rasterEnd donor) ∧
    v.venue.phase (v.reachedSources floor) (v.rasterEnd floor) w=date.venue.phase (date.sources donor) (date.rasterEnd donor) w:=by
  have banks:v.reachedSources floor=date.sources donor:=by rw [source_chart,same,start]
  have position:v.rasterEnd floor=date.rasterEnd donor:=by rw [raster_chart,same,start]
  have venue:v.venue=date.venue:=congrArg OrdinaryReturn.venue same
  exact ⟨banks,position,by rw [banks,position,venue],by rw [banks,position,venue]⟩

theorem same_ordinary_return {F' P':Type} [Field F'](other:PhysicalOrdinary F' P')
    (first second w:ℕ)(date:v.returnChart=other.returnChart)(donor:v.donorEnd first=other.donorEnd second):
    v.reachedSources first=other.reachedSources second ∧
    v.venue.operands (v.reachedSources first) (v.rasterEnd first)=
      other.venue.operands (other.reachedSources second) (other.rasterEnd second) ∧
    v.venue.phase (v.reachedSources first) (v.rasterEnd first) w=
      other.venue.phase (other.reachedSources second) (other.rasterEnd second) w:=by
  obtain ⟨source,_,ports,code⟩:=v.return_at first _ w _ date donor
  exact ⟨source,ports,code⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
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
theorem ordinary_return_core (old:ProtocolRAM.Bank)(base b payload unit seats:ℕ):
    let ℓ:=Nat.clog 2 (S.hostSize i)
    let short:=max (k+3) (Nat.clog 2 (prior.placement.degree+1))
    let profile:=DescentTerminalEpochBits.width G.C
    let a:=ticket.ordinaryArea ℓ b payload unit profile seats
    let pub:=forAge S G.b g k i ℓ b payload unit profile seats
    let d:=DonorDate.atDate G S g k i p
    a=pub ∧ ticket.donorDate=d ∧
    ticket.endAddress old base ℓ b short payload unit profile seats=d.endAddress payload (pub.rotationEnd old base):=by
  intro ℓ short profile a pub d
  have area:a=pub:=ordinary_geometry X G S br ticket before tail cut ℓ b payload unit profile seats
  have donor:ticket.donorDate=d:=donor_date_eq X G S br ticket before tail cut
  refine ⟨area,donor,?_⟩
  unfold OrdinaryLink.endAddress
  change ticket.wholeDonorEnd short profile (2^ℓ) payload (a.rotationEnd old base)=_
  rw [area,←donor]
  exact ticket.public_donor_end payload (pub.rotationEnd old base)

include ticket before tail cut in
theorem public_venue_return (old:ProtocolRAM.Bank)(ports:StageVenueTail.OrdinaryReturn)
    (frozen b payload unit seats floor sourceLanes w:ℕ)(ordinary:ℕ→Ordinary):
    let H:=NativePitch.incomingHosts S (i+1)
    let q:SignedStage:=⟨k,prior.placement.degree,prior.placement.cap,next.placement.degree,next.placement.cap,
      hostRows (S.hostSize i),H,S.groupCount (i+1),G.b,G.C,G.k⟩
    let ℓ:=Nat.clog 2 (S.hostSize i)
    let short:=max (k+3) (Nat.clog 2 (prior.placement.degree+1))
    let profile:=DescentTerminalEpochBits.width G.C
    let real:=ticket.ordinaryArea ℓ b payload unit profile seats
    let a:=forAge S G.b g k i ℓ b payload unit profile seats
    let d:=DonorDate.atDate G S g k i p
    let actual:=ports.place real ticket.donorDate (q.format payload)
      (StageVenueTail.Date.ofSigned q (S.censusBits p) sourceLanes payload (NativePitch.incoming S k frozen p f payload ordinary (i+1))) payload
    let agreed:=ports.place a d (SignedStage.signedAt G S g k i payload)
      (StageVenueTail.Date.atOrdinary G S g k frozen p f payload ordinary i sourceLanes) payload
    let recorded:=ticket.endAddress old floor ℓ b short payload unit profile seats
    let header:=d.endAddress payload (a.rotationEnd old floor)
    actual.sources recorded=agreed.sources header ∧
      actual.venue.operands (actual.sources recorded) (actual.rasterEnd recorded)=
        agreed.venue.operands (agreed.sources header) (agreed.rasterEnd header) ∧
      actual.venue.phase (actual.sources recorded) (actual.rasterEnd recorded) w=
        agreed.venue.phase (agreed.sources header) (agreed.rasterEnd header) w:=by
  intro H q ℓ short profile real a d actual agreed recorded header
  obtain ⟨area,donor,position⟩:=ordinary_return_core X G S br ticket before tail cut old floor b payload unit seats
  have ss:q.format payload=SignedStage.signedAt G S g k i payload:=
    signed_format_eq X G S br ticket before tail cut H payload
  have dd:=venue_date_eq X G S br ticket before tail cut frozen payload sourceLanes ordinary
  have same:actual=agreed:=by
    change ports.place real ticket.donorDate (q.format payload) _ payload=ports.place a d _ _ payload
    have area' : real=a := area
    have donor' : ticket.donorDate=d := donor
    have date' : StageVenueTail.Date.ofSigned q (S.censusBits p) sourceLanes payload
        (NativePitch.incoming S k frozen p f payload ordinary (i+1)) =
        StageVenueTail.Date.atOrdinary G S g k frozen p f payload ordinary i sourceLanes := dd
    rw [area',donor',ss,date']
  have starting:recorded=header:=position
  rw [same,starting]
  exact ⟨rfl,rfl,rfl⟩

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
