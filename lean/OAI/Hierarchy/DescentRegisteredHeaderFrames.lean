import OAI.Hierarchy.DescentRegisteredOrdinaryMeterRoom
import OAI.Hierarchy.DescentOrdinaryArchiveHeaders

namespace OAI
/-! The original accepted charge and ballot header precede every ordinary pointer field. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentPacking.PackedMatch.Local.Stage
noncomputable section
variable {F P:Type} [Field F] (v:PhysicalOrdinary F P)

theorem donor_before_header_output (floor:ℕ) :
    v.donorEnd floor≤v.finalChart.out (v.metaEnd floor) :=by
  have shape:=v.arguments_extent floor
  change v.normalizedEnd floor=v.vector.endAddress (v.donorEnd floor)+v.argumentExtra at shape
  rw [DescentOperandVectorArena.affine] at shape
  have raw : v.donorEnd floor≤v.endAddress floor:=by
    change _≤v.resolver.endAddress (v.normalizedEnd floor)
    rw [v.resolver.affine]
    omega
  have raster:v.endAddress floor≤v.rasterEnd floor:=by
    rw [rasterEnd,StageVenueTail.OrdinaryRaster.translated]
    exact Nat.le_add_right ..
  have venue:=v.venue.order (v.rasterEnd floor)
  have rooms:v.rasterEnd floor≤v.metaStart floor:=
    venue.1.trans (venue.2.1.trans (venue.2.2.1.trans venue.2.2.2))
  have node:v.metaStart floor≤v.metaEnd floor:=by rw [metaEnd,v.metadata.ordinary_translate];omega
  have pages:v.metaEnd floor≤v.finalChart.out (v.metaEnd floor):=
    (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  exact raw.trans (raster.trans (rooms.trans (node.trans pages)))

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open DescentSIMDLookup ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false

variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
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

local notation "entry" => (base).registeredEntry ports ((base).stageStart root)

local notation "floor₁" => (v).stageStart root
local notation "level₁" => Nat.clog 2 (S.hostSize i)
local notation "bits₁" => S.censusBits p
local notation "prof" => DescentTerminalEpochBits.width G.C


local notation "rotation" => ((d₀).schedule payload seats bits₁).rotationEnd ports.io.roster floor₁

include before tail cut in
theorem ordinary_header_frames (header:ℕ) (low:header<root) :
    let m:=(d₀).counter payload rotation header
    m.endAddr≤(v).finalChart.out ((v).metaEnd floor₁) ∧ header< m.endAddr :=by
  have meter:=ordinary_meter_roof X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary header
  have stage:root≤floor₁:=by
    change root≤(v).profileRepack.endAddress root
    rw [(v).profileRepack.translate]
    exact Nat.le_add_right ..
  have offset:=((d₀).schedule payload seats bits₁).rotation_add ports.io.roster 0 floor₁
  rw [Nat.add_zero] at offset
  have belowRotation:floor₁≤rotation:=by rw [offset];exact Nat.le_add_right ..
  exact ⟨meter.2.2.trans ((v).donor_before_header_output floor₁),
    low.trans_le (stage.trans (belowRotation.trans (meter.1.trans meter.2.1.le)))⟩

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
