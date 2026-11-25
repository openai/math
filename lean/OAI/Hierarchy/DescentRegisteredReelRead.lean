import OAI.Hierarchy.DescentRegisteredReelAddresses
import OAI.Hierarchy.DescentOrdinaryCalendarObservations
import OAI.Hierarchy.DescentRegisteredOrdinaryMeterRoom
import OAI.Hierarchy.DescentRegisteredOrdinaryProtection
import OAI.Hierarchy.DescentNamedSignedDate

namespace OAI
/-! # Registered count and matrix observations from the selected original matcher report -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open DescentSIMDLookup ProtocolRAM
open scoped Classical Fin.CommRing
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
variable {W : MarkedWorld F 0 (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width))) (fun _ => S.firstWidth G.b p*1)} {i z D z' D' : ℕ} {rate : ℝ}
    {prior : Reached W G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k i z D (S.epochPower^S.priceExponent) (S.firstWidth G.b p)} {T : StageInput W G rate (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)}
    {nonneg : 0 ≤ (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)} {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k (i+1) z' D' (S.epochPower^S.priceExponent) (S.firstWidth G.b p)}
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

local notation "entry" => (base).registeredEntry ports ((base).stageStart root)

local notation "floor₁" => (v).stageStart root
local notation "level₁" => Nat.clog 2 (S.hostSize i)
local notation "bits₁" => S.censusBits p
local notation "prof" => DescentTerminalEpochBits.width G.C


local notation "rotation" => ((d₀).schedule payload seats bits₁).rotationEnd ports.io.roster floor₁


open DescentColonies DescentGroupPeerOrder DescentSIMDLookup
open DescentTerminalEpochDecoder DescentTerminalEpochChart DescentPackedProfileWide DescentStageEdgeReceipt DescentKernelHistory.BitDescription
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentDatedAddressBook
variable (w shelf header : ℕ) (pos : 0< k)
variable (ok : DatePorts.OrdinaryCodeRoom ports ticket op g frozen p f drift degree payload seats root ordinary w)
variable (exec : DatePorts.OrdinaryExecutionRoom ports ticket op g frozen p f drift degree payload seats
  root ordinary w shelf header ok)
local notation "installed" => DatePorts.ordinaryDate ports ticket op g frozen p f drift degree payload seats
  root ordinary w shelf header pos ok
local notation "signedFields" => (v).signedInput floor₁ ok.signed
local notation "entry_" => (base).registeredEntry ports floor₁
local notation "match_" => (base).registered_match ports floor₁ (Nat.le_max_left ports.argumentsPerNode (S.retainedArgumentsAt G drift))
local notation "shape_" => (base).registered_geometry ports floor₁
local notation "steps_" => (v).issuedSteps root ports entry_ ok.signed w match_ shape_ ok.blocks ok.paths
  ok.slots ok.chip ok.endFit ok.packed ok.radix ok.funded
local notation "saved_" => (v).area.flagEnd ports.io.roster floor₁+2^k
local notation "μ₀" => DescentColonies.multiplier prior.placement.fieldBits (scannedRows nonneg prior.placement.stage).μ

include before tail cut exec in
theorem registered_reel_read {Pin:Type} (dates:ℕ→DateCode w) (m:Memory w)
    (issued : dates i=installed) (beforeHeader : header< root)
    (wide:Fintype.card prior.V≤2^(v).level) (pick:(prior.placement.stage.result nonneg).Choice)
    (e:Source Pin) (zeta:Pin→Bool) (ext:DescentTerminalEpochBits.width e.C≤(v).area.shapeAt.digit)
    (seen:(v).reachedReport ports.io floor₁ wide
      (((v).archivePhase root shelf w).image (DateCode.history dates m i)) pick e zeta ext) :
    DateCode.history dates m (i+1) ((v).countAddr root)=(selectionCount G ticket.selection:Word w) ∧
    DateCode.history dates m (i+1) saved_=((DescentExterior.matrixCode μ₀).val:Word w):=by
  obtain ⟨shape,endAt⟩:=ordinary_reel_layout X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary
  have rank:=((br.origin.names_on_path before).1)
  let name:=GroupStage.plane (v).hostNumbers wide
  have sameNames:name.trans Fin.valEmbedding=prior.vertex.trans Fin.valEmbedding:=by ext x;rfl
  have named : prior.placement.SiteNamed (groupRank ((Equiv.refl (Fin (S.groupCount i))).toEmbedding.trans Fin.valEmbedding)
      (name.trans Fin.valEmbedding)):=by rw [sameNames];exact rank
  have baseLo: root≤ floor₁:=by change root≤(v).profileRepack.endAddress root;rw [(v).profileRepack.translate];exact Nat.le_add_right ..
  have donorLo: floor₁≤(v).donorEnd floor₁:=by rw [(v).donor_shift];exact Nat.le_add_right ..
  have written:=(v).before_span floor₁ ports.io ports.archive.count signedFields ((v).reachedSources floor₁) steps_ ok.result exec.late
  have countLo:(v).primitiveEnd floor₁≤(v).countAddr root:=by
    change (v).primitiveEnd floor₁ ≤ (v).primitiveEnd floor₁ + 2^(v).countBits + (v).area.batch
    exact (Nat.le_add_right _ (2^(v).countBits)).trans (Nat.le_add_right _ _)
  have old_:= (v).area.rotation_add ports.io.roster 0 floor₁
  simp only [Nat.add_zero,Ordinary.rotationEnd] at old_
  have lowerSaved: floor₁≤ saved_:=by omega
  let planned:=(d₀).schedule payload seats bits₁
  have up:0< planned.unit:=(show 1≤ max 1 (max planned.b (DescentSignedCableCodec.width planned.D planned.cap)) from le_max_left ..).trans exec.matcher.inputWidth
  have live:0< lanes payload (d₀).amount:=(occupancy payload (d₀).amount up exec.matcher.laneWidth).1
  have cap:0<(d₀).cap:=by
    have hc:=congrArg Ordinary.cap shape
    change prior.placement.cap=(d₀).cap at hc
    rw [←hc]
    exact lt_of_lt_of_le (by decide : 0<256) (signed_source_capacity X G S br ticket before tail cut)
  exact (v).calendar_observations ports.io root shelf header ports.archive.count signedFields ((v).reachedSources floor₁)
    steps_ ok.result (d₀) pos exec wide e zeta pick ext dates m issued _ rfl seen named shape.symm rfl endAt
    g p rfl live cap (ne_of_gt (beforeHeader.trans_le (baseLo.trans (donorLo.trans (written.1.trans countLo)))))
    (ne_of_gt (beforeHeader.trans_le (baseLo.trans lowerSaved)))

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
