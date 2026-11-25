import OAI.Hierarchy.DescentNamedMatchedRooms
import OAI.Hierarchy.DescentDatedMatcherOutputRoom
import OAI.Hierarchy.DescentIssuedDonorReadRoom
import OAI.Hierarchy.DescentIssuedPublicDonorRoom
import OAI.Hierarchy.DescentIssuedPublicCounterRoom

namespace OAI
/-! # Every physical matcher output is readable by the actual donor and private counter -/
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
variable {W : MarkedWorld F 0 (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width))) (fun _ => S.firstWidth G.b p*1)} {i z D z' D' : ℕ}
variable {prior : Reached W G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k i z D (S.epochPower^S.priceExponent) (S.firstWidth G.b p)}
local notation "A" => prior.placement
variable {nonneg : 0≤(((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)} {choice : (prior.placement.stage.result nonneg).Choice}
    {norm : Normalize ((prior.placement.stage.result nonneg).state choice)}
    {next : Reached norm.result G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k (i+1) z' D' (S.epochPower^S.priceExponent) (S.firstWidth G.b p)}
    (ticket : OrdinaryLink prior nonneg prior.placement.stage choice norm next)
    (before : Path br.origin.source prior) (tail : Path next br.target)
    (cut : (Path.ordinary before ticket).append tail=br.path)
local notation "H" => DescentCompiler.TerminalScale.hostRows (S.hostSize i)
local notation "short" => max (k+3) (Nat.clog 2 ((A).degree+1))
local notation "prof" => DescentTerminalEpochBits.width G.C
local notation "amount" => ticket.installedDonorWidth short prof

open DescentPacking.PackedMatch.Local.Stage
local notation "d" => DonorDate.atDate G S g k i p

set_option maxHeartbeats 800000 in
include ticket before tail cut in
theorem matched_read_room (payload seats board : ℕ) (input : Operands) (floor w : ℕ)
    (cpu : 0<w) (safe : ((d).schedule payload seats board).Space input w floor)
    (hostWord : H<2^w) (degreeWord : (A).degree<2^w)
    (extent : ticket.wholeDonorEnd short prof H payload (((d).schedule payload seats board).rotationEnd input.roster floor)≤2^w) :
    let a:=(d).schedule payload seats board
    let real:=ticket.matchedBanks payload seats (a.prepareAt input.roster floor) (input.ports (A).degree)
      (fun x j=>input.wire x.val j.val) input.hubs
    ticket.ReadRoom payload (a.rotationEnd input.roster floor) real w :=by
  have date:=donor_date_eq X G S br ticket before tail cut
  rw [←date] at safe extent ⊢
  let a:=ticket.donorDate.schedule payload seats board
  let rot:=a.rotationEnd input.roster floor
  let rom:=a.prepareAt input.roster floor
  let real:=ticket.matchedBanks payload seats rom (input.ports (A).degree) (fun x j=>input.wire x.val j.val) input.hubs
  change ticket.ReadRoom payload rot real w
  obtain ⟨expr,flag,peers,top,born,topRows,birthRows⟩:=ticket.donorDate.matcher_output_room payload seats board input w floor safe
  have phases:=a.subphase_order input floor
  have start:=a.phase_before_winners input.roster floor
  have last : a.flagEnd input.roster floor≤rot:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have reach : floor≤rot:=phases.1.trans (start.trans (phases.2.1.trans (phases.2.2.1.trans (phases.2.2.2.trans last))))
  have cable : ∀j,((ticket.issuedAddressed payload rot real).cable j).Fits w rot:=by
    intro j
    exact Chooser.bank_before (safe.wires (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2).1 reach
  exact (ticket.issued_read_room payload rot real cpu safe.embed extent expr flag cable input.actors peers
    (safe.hubs.2.2.trans reach) hostWord degreeWord top born topRows birthRows).1

include ticket before tail cut in
theorem matched_rooms_from_space (payload seats board : ℕ) (input : Operands) (floor w header factor : ℕ)
    (cpu : 0<w) (safe : ((d).schedule payload seats board).Space input w floor)
    (hostWord : H<2^w) (degreeWord : (A).degree<2^w)
    (past : header≤((d).schedule payload seats board).rotationEnd input.roster floor)
    (live : 0<amount) (wide : 2*amount≤payload) (ratio : w≤factor*payload)
    (extent : ticket.wholeDonorEnd short prof H payload (((d).schedule payload seats board).rotationEnd input.roster floor)≤2^w) :
    let a:=(d).schedule payload seats board
    let base:=a.rotationEnd input.roster floor
    (d).PhaseRoom payload base w ((d).matcherOutput payload seats input (a.prepareAt input.roster floor)) ∧
      ((d).counter payload base header).Room w :=by
  exact matched_rooms X G S br ticket before tail cut payload seats _ _ input past live wide safe.embed ratio extent
    (matched_read_room X G S br ticket before tail cut payload seats board input floor w cpu safe hostWord degreeWord extent)

include ticket before tail cut in
/-- The originally allocated matcher has one host, an offset bank for each
host and a directory cell for every peer. These force both word bounds. -/
theorem matcher_rooms (payload seats board : ℕ) (input : Operands) (floor w header factor : ℕ)
    (safe : ((d).schedule payload seats board).Space input w floor)
    (past : header≤((d).schedule payload seats board).rotationEnd input.roster floor)
    (ratio : w≤factor*payload)
    (extent : ticket.wholeDonorEnd short prof H payload (((d).schedule payload seats board).rotationEnd input.roster floor)≤2^w) :
    let a:=(d).schedule payload seats board
    let base:=a.rotationEnd input.roster floor
    (d).PhaseRoom payload base w ((d).matcherOutput payload seats input (a.prepareAt input.roster floor)) ∧
      ((d).counter payload base header).Room w :=by
  have date:=donor_date_eq X G S br ticket before tail cut
  have issued:=safe
  rw [←date] at issued
  have Hpos : 0<H:=issued.hosts
  have hw : H<2^w:=issued.accessible.offRoom.trans_lt issued.accessible.offsets.2.1
  have dw : (A).degree<2^w:=
    (show (A).degree≤H*(A).degree by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (A).degree Hpos).trans_lt
      (issued.accessible.rosterRoom.trans_lt issued.accessible.roster.2.1)
  have cpu : 0<w:=by by_contra! zero;rw [show w=0 by omega] at hw;simp at hw;omega
  have pos : 0<ticket.donorDate.amount:=by
    unfold DonorDate.amount
    exact (Nat.zero_lt_succ _).trans_le ((le_max_right ..).trans (le_max_right ..))
  exact matched_rooms_from_space X G S br ticket before tail cut payload seats board input floor w header factor
    cpu safe hw dw past pos issued.laneWidth ratio extent

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

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
variable {W : MarkedWorld F 0 (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width))) (fun _ => S.firstWidth G.b p*1)} {i z D z' D' : ℕ}
variable {prior : Reached W G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k i z D (S.epochPower^S.priceExponent) (S.firstWidth G.b p)}
local notation "A" => prior.placement
variable {rate : ℝ} {T : StageInput W G rate (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)} {nonneg : 0≤(((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)}
    {ballot : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state ballot)}
    {next : Reached norm.result G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) S k (i+1) z' D' (S.epochPower^S.priceExponent) (S.firstWidth G.b p)}
    (ticket : OrdinaryLink prior nonneg T ballot norm next)
    (before : Path br.origin.source prior) (tail : Path next br.target)
    (cut : (Path.ordinary before ticket).append tail=br.path)
local notation "H" => DescentCompiler.TerminalScale.hostRows (S.hostSize i)
local notation "short" => max (k+3) (Nat.clog 2 ((A).degree+1))
local notation "prof" => DescentTerminalEpochBits.width G.C
local notation "amount" => ticket.installedDonorWidth short prof

local notation "d" => DonorDate.atDate G S g k i p

include ticket before tail cut in
theorem issued_matcher_rooms (payload seats board : ℕ) (input : Operands) (floor w header factor : ℕ)
    (safe : ((d).schedule payload seats board).Space input w floor)
    (past : header≤((d).schedule payload seats board).rotationEnd input.roster floor)
    (ratio : w≤factor*payload)
    (extent : ticket.wholeDonorEnd short prof H payload (((d).schedule payload seats board).rotationEnd input.roster floor)≤2^w) :
    let a:=(d).schedule payload seats board
    let base:=a.rotationEnd input.roster floor
    (d).PhaseRoom payload base w ((d).matcherOutput payload seats input (a.prepareAt input.roster floor)) ∧
      ((d).counter payload base header).Room w :=by
  obtain rfl:=ticket.sourceRate
  obtain rfl:=eq_of_heq ticket.placement
  exact matcher_rooms X G S br ticket before tail cut payload seats board input floor w header factor safe past ratio extent

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
