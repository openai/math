import OAI.Hierarchy.DescentDatedMeter
import OAI.Hierarchy.DescentNamedDonorCode

namespace OAI
/-! # The actual private-counter program at the public date of the named history -/
namespace Hierarchy.DescentSixParty.Chronology.DonorDate
open DescentPacking.PackedMatch.Local.Stage.Dated DescentSIMDLookup
def counter (d : DonorDate) (payload base header : ℕ) : Meter :=
  ⟨d.hosts,d.groups,d.exponent,d.degree,d.cap,d.branch,d.colors,d.padding,d.grain,
    lanes payload d.amount,d.meterBase payload base,header⟩
end Hierarchy.DescentSixParty.Chronology.DonorDate
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentHostDegree DescentRawCablePanel DescentSIMDLookup DescentPacking.PackedMatch.Local
open ProtocolRAM Computability.VPVNP.BurstRAM DescentPackedZip DescentPackedColony
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q ε u : ℝ} {k i z D wire hist w : ℕ}
variable {W : MarkedWorld F d P bits} {prior : Reached W G q ε S k i z D wire hist}
variable {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
variable {n : Normalize ((T.result he).state c)} {z' D' : ℕ} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
variable (ticket : OrdinaryLink prior he T c n target)
local notation "A" => prior.placement
local notation "H" => DescentCompiler.TerminalScale.hostRows (S.hostSize i)
local notation "J" => S.groupCount i
local notation "r" => 2^k
local notation "cm" => 2*(A).cap
local notation "K₀" => 2^(k+1)
local notation "dim" => (A).degree
local notation "short" => max (k+3) (Nat.clog 2 (dim+1))
local notation "profile" => DescentTerminalEpochBits.width G.C
local notation "fmt" => ticket.depotShape short
local notation "s" => shape r dim cm profile
local notation "amount" => ticket.installedDonorWidth short profile
variable (h base : ℕ)
local notation "M" => lanes h amount
local notation "rows" => H*chunks J M

open DescentPacking.PackedMatch.Local.Stage.Dated
theorem issued_meter_code (old : PriorBanks r dim (A).cap K₀) {header factor p : ℕ}
    (oldLow : header≤base) (live : 0<amount) (wide : 2*amount≤h) (size : h≤w)
    (ratio : w≤factor*h) (extent : ticket.wholeDonorEnd short profile H h base≤2^w)
    (grain : T.z=S.grainAt G.b p i) :
    let visit:=ticket.issuedVisit h base old oldLow live wide size ratio extent grain
    let current:=ticket.donorDate.counter h base header
    MeterPort.program ticket visit.port header w=current.program w ∧
      MeterPort.ticks ticket visit.port header=current.ticks ∧ MeterPort.hardware ticket visit.port=current.hardware := by
  intro visit current
  have id : Meter.ofTicket (T:=T) visit.port header=current := by
    change Meter.mk _ _ _ _ _ _ _ _ T.z _ _ _ = Meter.mk _ _ _ _ _ _ _ _ (A).z _ _ _
    rw [ticket.quantum]
    rfl
  rw [←id]
  exact Meter.ticket_code ticket visit.port header w

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink
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


local notation "H" => DescentCompiler.TerminalScale.hostRows (S.hostSize i)
local notation "short" => max (k+3) (Nat.clog 2 ((A).degree+1))
local notation "prof" => DescentTerminalEpochBits.width G.C
local notation "amount" => ticket.installedDonorWidth short prof
variable (payload base : ℕ)
theorem ordinary_meter (old : OrdinaryLink.PriorBanks (2^k) (A).degree (A).cap (2^(k+1))) {header w factor : ℕ}
    (past : header≤base) (pos : 0<amount) (wide : 2*amount≤payload) (size : payload≤w)
    (ratio : w≤factor*payload) (room : ticket.wholeDonorEnd short prof H payload base≤2^w) :
    let grain:=ticket.grain_on_cut before tail cut br.issuedGrains
    let visit:=ticket.issuedVisit payload base old past pos wide size ratio room grain
    let fixed:=(DonorDate.atDate G S g k i p).counter payload base header
    MeterPort.program ticket visit.port header w=fixed.program w ∧
      MeterPort.ticks ticket visit.port header=fixed.ticks ∧ MeterPort.hardware ticket visit.port=fixed.hardware := by
  intro grain visit fixed
  dsimp only [fixed]
  rw [←donor_date_eq X G S br ticket before tail cut]
  exact ticket.issued_meter_code payload base old past pos wide size ratio room grain

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
