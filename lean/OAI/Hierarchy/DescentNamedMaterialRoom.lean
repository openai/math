import OAI.Hierarchy.DescentRegisteredDonorExtent
import OAI.Hierarchy.DescentIssuedMaterialExtentRoom
import OAI.Hierarchy.DescentDatedMaterialRoom
import OAI.Hierarchy.DescentDatedSignedAny

namespace OAI
/-! # The selected original donor supplies the full material bank on the fixed date -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open DescentSIMDLookup ProtocolRAM
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
variable {he : 0 ≤ ((((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower))} {hu : 0 ≤ (((1/(((S.firstWidth G.b p):ℝ)*((S.epochPower^S.priceExponent):ℝ)):ℝ))*((S.epochPower^S.priceExponent):ℝ))} {radix : S.radix=2^k}
variable {run : Epochs G hu he (h:=h) (C:=C) («Ht»:=(GroupStage.depthBound (atRound S.rounds) n f g)) (t:=S.rounds) S.height
      (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he run).Choice} (br : Branch X G S radix R run c)
local notation "P" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width)))
local notation "bits" => (fun _ : P=>s*1)
variable {W : MarkedWorld F 0 ((Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width)))) ((fun _ : ((Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width))))=>(S.firstWidth G.b p)*1))} {i z D z' D' : ℕ} {rate : ℝ}
    {prior : Reached W G ((1/(((S.firstWidth G.b p):ℝ)*((S.epochPower^S.priceExponent):ℝ)):ℝ)) ((((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)) S k i z D (S.epochPower^S.priceExponent) (S.firstWidth G.b p)} {T : StageInput W G rate ((((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower))}
    {nonneg : 0 ≤ ((((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower))} {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G ((1/(((S.firstWidth G.b p):ℝ)*((S.epochPower^S.priceExponent):ℝ)):ℝ)) ((((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)) S k (i+1) z' D' (S.epochPower^S.priceExponent) (S.firstWidth G.b p)}
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


local notation "H" => (v).area.H
local notation "M" => (v).signed.lanes
local notation "groups" => (v).signed.groups
local notation "degree₀" => (v).signed.degree
local notation "P₀" => DescentHaloWalkRAM.breadth degree₀
local notation "bank₀" => (entry).venue.panel
local notation "low" => (v).donorEnd floor₁
local notation "middle" => (v).materialStart floor₁
local notation "bank₁" => PriorHeader.reverseRank H groups M degree₀ low

include before tail cut in
theorem selected_material_room {w:ℕ} (word:payload≤w) («wire»:(v).SignedRoom floor₁ w):
    (v).MaterialRoom middle bank₀ bank₁ w:=by
  have early:=registered_donor_extent X G S br ticket before tail cut op frozen drift degree payload seats root ports ordinary
  have floorLe:low≤ middle:=PriorHeader.lower ..
  have bankEnd:=early.1.trans floorLe
  have rowCount:(v).material.sourceRows≤(bank₀).size:=early.2
  have named:=(issued_return_fields X G S br ticket before tail cut books frozen payload seats ports.venue.lanes ports.io.roster ordinary).2.2.2
  have names:(v).signedLayout.format (v).payload=(v).signed:=congrArg (fun a=>PhysicalOrdinary.signed a) named
  have cap:=signed_source_capacity X G S br ticket before tail cut
  have widths:=(v).material_widths names cap
  have src:(bank₀).Fits w middle:=⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (bankEnd.trans_lt «wire».header),bankEnd⟩
  have inverse:(bank₁).Fits w middle:=PriorHeader.at_bank H groups M degree₀ low (P₀+16) (P₀+20) (by omega) «wire».header
  have count:H*P₀≤(bank₁).size:=(PriorHeader.limits H groups M degree₀).2.2.1
  have paid:(v).material.oldLanes*max (v).material.jointBits (v).material.fieldBits≤w/2:=by
    rcases le_total (v).material.fieldBits (v).material.jointBits with le|le
    · rw [max_eq_left le,Nat.mul_comm];exact widths.1.trans (Nat.div_le_div_right word)
    · rw [max_eq_right le,Nat.mul_comm];exact widths.2.1.trans (Nat.div_le_div_right word)
  refine ⟨?_,src,rowCount,inverse,count,paid,«wire».material.trans_lt ?_⟩
  · change (v).signed.reach=DescentHaloWalkRAM.breadth ((v).ticket.depotShape (v).short).degree
    rw [←names];rfl
  · exact (Nat.le_add_right ..).trans_lt «wire».combined

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
