import OAI.Hierarchy.DescentRegisteredPrimitiveCheckpoint
import OAI.Hierarchy.DescentPrimitiveDateLocalBounds
import OAI.Hierarchy.DescentDatedPrimitiveWidthCeilings
import OAI.Hierarchy.DescentRegisteredOrdinaryGeometry

namespace OAI
/-! # Address room for the authentic ordinary primitive compiler on every registered cut -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCompiler DescentCompiler.TerminalScale DescentOrdinaryPrimitiveCheckpoint DescentDatedAddressBook
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F]
structure RegistryPrimitiveShape (G : PoweredGadget F) (S : AtomSchedule) (g k i p : ℕ) (op : RotorSpec)
    (frozen drift degree h seats : ℕ) (prior : DatePorts) (floor : ℕ) (v : PhysicalOrdinary F P) : Prop where
  hosts : (v.registeredFrom prior floor).paletteShape.hosts=hostRows (S.hostSize i)
  groups : (v.registeredFrom prior floor).paletteShape.groups=S.groupCount (i+1)
  blocks : (v.registeredFrom prior floor).paletteShape.blocks=2^k
  ports : (v.registeredFrom prior floor).paletteShape.ports=((DonorDate.atDate G S g k i p).degree+1)^4
  capacity : (v.registeredFrom prior floor).paletteShape.capacity=(DonorDate.atDate G S g k i p).cap
  old : (v.registeredFrom prior floor).paletteShape.oldNodes=prior.nodes
  lows : (v.registeredFrom prior floor).paletteShape.lows=(OrdinaryBooks.atDate G S op g k i p frozen drift degree h seats prior).vector.lows
  born : let W:=v.registeredFrom prior floor
         W.bornBook.hosts=W.paletteShape.hosts ∧ W.bornBook.groups=W.paletteShape.oldGroups ∧
           W.bornBook.blocks=W.paletteShape.blocks ∧ W.bornBook.cap=W.paletteShape.capacity
  chip : let W:=v.registeredFrom prior floor
         (2*W.bornBook.chipBits)*W.bornBook.lanes≤h/2
  peak : primitivePeak (v.registeredFrom prior floor)≤h/2
  pitches : let l:=(v.registeredFrom prior floor).paletteShape
            l.priorLanes≤h ∧ l.birthLanes≤h ∧ l.originLanes≤h ∧ l.workLanes≤h ∧ l.nextLanes≤h
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
local notation "feeMultiplier" => price*(wire:ℝ)
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


open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage
variable (op : RotorSpec) (frozen drift degree payload seats hostLanes : ℕ) (ports : DatePorts)
variable (old : ProtocolRAM.Bank) (ordinary : ℕ→Ordinary)
local notation "books" => OrdinaryBooks.atDate G S op g k i p frozen drift degree payload seats ports
local notation "v" => (books).onTicket ticket g frozen p f payload seats hostLanes old ordinary

open DescentDatedOperandReadPipeline
variable (stageFloor : ℕ)
local notation "entry" => (v).datedEntry ports stageFloor
local notation "other" => purchase ((v).withFundedArguments 0 entry).ticketReadGeometry

local notation "date₀" => DonorDate.atDate G S g k i p

include before tail cut in
theorem registered_primitive_geometry (age : i<S.length) :
    PhysicalOrdinary.RegistryPrimitiveShape G S g k i p op frozen drift degree payload seats ports stageFloor v:=by
  have groups : S.groupCount i=S.groupCount (i+1)*2^k:=by
    simpa only [Fintype.card_fin,Fintype.card_prod] using Fintype.card_congr (S.groupDigits age radix)
  have trueDegree : prior.placement.degree=(date₀).degree:=congrArg DonorDate.degree (donor_date_eq X G S br ticket before tail cut)
  let W:=(v).registeredFrom ports stageFloor
  let clip:=(v).fundedClip ((v).argumentUnitFrom ports stageFloor)
  have configured : W.palette=DescentOrdinaryPalette.Configuration.atOrdinary G S op p payload prior.placement.degree k
      (date₀).cap ports.nodes S.retainedNodes ports.roleLanes:=by rw [trueDegree];rfl
  have keys:=(v).funded_primitive_widths entry other
  have oldKey:=(v).funded_primitive_prior entry other rfl
  have ceilings:=W.primitive_width_ceilings p payload ports.roleLanes configured keys.2.1 oldKey keys.1 keys.2.2
  have working : clip.working≤payload:=clip.working_fields.1.trans (Nat.div_le_self ..)
  have later : clip.postPitch≤payload:=(Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)).trans working
  refine ⟨rfl,rfl,rfl,?_,rfl,rfl,rfl,⟨rfl,groups,rfl,rfl⟩,keys.2.1,ceilings.1,
    working,working,later,ceilings.2⟩
  change (prior.placement.degree+1)^4=_
  rw [trueDegree]

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentCompiler DescentCompiler.TerminalScale Filter
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {ι : ℕ→Type*} {Pins : ∀h,ι h→Type}
    (G : PoweredGadget F) (op : RotorSpec) (t f g reset τ B drift degreeMax : ℕ)
    (sites age p degree seats floor : ∀h,ι h→ℕ) (ports : ∀h,ι h→DatePorts)
    (v : ∀h (i:ι h),PhysicalOrdinary F (Pins h i))
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "S_" h:arg i:arg => stageNumbers G t (J_ h) f g reset (sites h i) (tail τ (J_ h))
local notation "k_" h:arg =>groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "Y_" h:arg i:arg =>(v h i).registeredFrom (ports h i) (floor h i)

/-- The five native pitches and nine lookup widths determine the absolute primitive archive. -/
theorem registered_primitive_rate (den : 0<B) (geo : OrdinaryGeometry G t f g reset τ B sites age p)
    (shape : ∀h i,RegistryPrimitiveShape G (S_ h i) g (k_ h) (age h i) (p h i) op (tail τ (J_ h))
      drift (degree h i) h (seats h i) (ports h i) (floor h i) (v h i))
    (inputs : ∀ᶠ h:ℕ in atTop,∀i,p h i≤h ∧ degree h i≤degreeMax ∧
      (ports h i).nodes≤(S_ h i).retainedNodes ∧ (S_ h i).firstWidth G.b (p h i)≤h)
    :
    PrimitiveScalarRoom (fun h i=>Y_ h i) ∧ Bounded (fun h i=>(Y_ h i).primitiveRoof 0):=by
  let frequency:=OrdinaryBooks.primitiveLocalRate G t f g reset
  have local_:=OrdinaryBooks.primitive_date_local G op t f g reset τ B drift degreeMax den
  have low : SmallAt (fun h=>J_ h) (fun h i=>(Y_ h i).paletteShape.lows):=by
    refine ⟨frequency,?_⟩
    filter_upwards [inputs,local_] with h fits bounds
    intro i
    obtain ⟨pFit,deg,nodes,seed⟩:=fits i
    have b:=bounds (sites h i) (age h i) (p h i) (degree h i) (seats h i) (ports h i) pFit deg nodes seed
    exact (shape h i).lows.le.trans b.2.2.2.2.2.2
  have nodes : SmallAt (fun h=>J_ h) (fun h i=>(Y_ h i).paletteShape.oldNodes):=by
    refine ⟨frequency,?_⟩
    filter_upwards [inputs,local_] with h fits bounds
    intro i
    obtain ⟨pFit,deg,current,seed⟩:=fits i
    have b:=bounds (sites h i) (age h i) (p h i) (degree h i) (seats h i) (ports h i) pFit deg current seed
    exact (shape h i).old.le.trans b.2.2.2.2.1
  have height : ∀ᶠ h:ℕ in atTop,J_ h≤h:=Eventually.of_forall fun h=>(Nat.div_le_self ..).trans (Nat.log_le_self 2 h)
  have lanes (c : ∀h,ι h→ℕ) (each : ∀h i,c h i≤h) : Bounded c :=
    ⟨1,Eventually.of_forall fun h i=>by
      simpa only [Nat.one_mul] using (each h i).trans (Nat.lt_two_pow_self.le)⟩
  have HH:=geo.axis.oldHost.padded.of_le (fun h i=>(shape h i).hosts.le)
  have GG:=geo.axis.newGroup.of_le (fun h i=>(shape h i).groups.le)
  have BB:=geo.blocks.of_le (fun h i=>(shape h i).blocks.le)
  have CC:=geo.cap.of_le (fun h i=>(shape h i).capacity.le)
  have room : PrimitiveScalarRoom (fun h i=>Y_ h i):=
    ⟨HH,GG,low.bounded height,BB,((geo.degree.add (Bounded.const 1)).pow 4).of_le
      (fun h i=>(shape h i).ports.le),CC,nodes.bounded height,
      lanes _ (fun h i=>(shape h i).pitches.1),lanes _ (fun h i=>(shape h i).pitches.2.1),
      lanes _ (fun h i=>(shape h i).pitches.2.2.1),lanes _ (fun h i=>(shape h i).pitches.2.2.2.1),
      lanes _ (fun h i=>(shape h i).pitches.2.2.2.2),HH.of_le (fun h i=>(shape h i).born.1.le),
      (GG.mul BB).of_le (fun h i=>(shape h i).born.2.1.le),BB.of_le (fun h i=>(shape h i).born.2.2.1.le),
      CC.of_le (fun h i=>(shape h i).born.2.2.2.le),1,Eventually.of_forall fun h i=>by
        simpa only [Nat.one_mul] using ((shape h i).peak.trans (Nat.div_le_self ..))⟩
  exact ⟨room,primitive_rate _ room⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
