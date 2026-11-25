import OAI.Hierarchy.DescentMatcherRoomCalendar
import OAI.Hierarchy.DescentDatedProfileTariff
import OAI.Hierarchy.DescentProfileSeatCalendar
import OAI.Hierarchy.DescentMatcherRate
import OAI.Hierarchy.DescentDatedMatcherVolume
import OAI.Hierarchy.DescentDonorMatcherSpace
import OAI.Hierarchy.DescentPrivateDonorActual
import OAI.Hierarchy.DescentDatedOrdinaryPhase
import OAI.Hierarchy.DescentDatedStageVenue

namespace OAI
/-! # Charging the original selector prepass on the very same named ordinary execution -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook ProtocolRAM DescentCompiler DescentCompiler.TerminalScale DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage Chronology DescentPacking.PackedMatch.Local.Stage.Dated
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

variable (payload seats ratio w floor base : ℕ) (old src : Bank)
local notation "date" => DonorDate.atDate G S g k i p
local notation "board" => S.censusBits p
local notation "area" => (date).schedule payload seats board
local notation "A₀" => DescentPackedEpochShelves.grain (payload/2) G.C
local notation "B₀" => (area).lanesAt*(area).shapeAt.pairs
local notation "dst" => ((area).matcher old floor).raw
local notation "bill" => (DescentPackedProfileRepack.ticks base seats A₀ B₀ (DescentTerminalEpochBits.width G.C) src dst+
  7*DescentStaticWordColumn.names (DescentPackedProfileRepack.program base seats A₀ B₀
    (DescentTerminalEpochBits.width G.C) (area).shapeAt.digit src dst w))*w
local notation "unit₀" => DescentPackedEpochShelves.unit G.C

include ticket before tail cut in
theorem mounted_profile_bill {t J resetRate M tailBits : ℕ} (sched : S=stageNumbers G t J f g resetRate M tailBits)
    (field : k=groupBits t J (hostRate t resetRate) (capRate G t g) (cutRate t f g))
    (room : MatcherRoom G S k p payload) (word : w≤ratio*payload)
    (large : 64≤payload) (oldFit : 2*unit₀≤payload/2) (age : i≤S.length) (capacity : seats≤S.length*S.batch) :
    let seatsRate := (t+1)*(hostRate t resetRate+capRate G t g+1)+11
    let amountRate := (donorRates G t f g resetRate).amount
    bill ≤ S.hostSize i*payload*(262144*ratio)+S.hostSize i*(S.groupCount i*S.radix)*
      (TerminalScale.scale J (seatsRate+amountRate)*(131072*ratio*(unit₀+1))) := by
  intro seatsRate amountRate
  have eqd:=donor_date_eq X G S br ticket before tail cut
  have know:=selected_input_bounds ticket sched field (donorRates G t f g resetRate).bounds
  have record : (date).amount≤ TerminalScale.scale J amountRate :=by
    rw [←eqd]
    change ticket.installedDonorWidth (max (k+3) (Nat.clog 2 (prior.placement.degree+1)))
      (DescentTerminalEpochBits.width G.C)≤ TerminalScale.scale J amountRate
    rw [selected_amount ticket]
    exact know.2
  have fits : 2*(date).amount≤payload :=by rw [←eqd];exact (room.packed ticket).2
  have slots : seats≤S.hostSize i*(S.groupCount i*S.radix)*TerminalScale.scale J seatsRate := by
    have paid:=selector_seats S age capacity
    simpa only [sched,stageNumbers,seatsRate] using paid
  have init:= (date).raw_pitch_bill payload seats board w ratio old src base floor
    (DonorDate.dated_cap_pos G S g k i p) room.census large oldFit fits ((room.table i).trans (hostPad _)) word
  change bill≤131072*ratio*(hostRows (S.hostSize i)*payload+seats*(unit₀+(date).amount)) at init
  have perSeat : unit₀+(date).amount≤(unit₀+1)*TerminalScale.scale J amountRate := by
    have posit : 0<TerminalScale.scale J amountRate:=Nat.two_pow_pos _
    have lower:=Nat.le_mul_of_pos_right unit₀ posit
    rw [Nat.add_mul,one_mul]
    exact Nat.add_le_add lower record
  have extra:=Nat.mul_le_mul slots perSeat
  have hosts:=Nat.mul_le_mul_right payload (hostRows_double (room.hosts i))
  calc
    _ ≤ 131072*ratio*(hostRows (S.hostSize i)*payload+seats*(unit₀+(date).amount)) := init
    _ ≤ 131072*ratio*((2*S.hostSize i)*payload+
        (S.hostSize i*(S.groupCount i*S.radix)*TerminalScale.scale J seatsRate)*((unit₀+1)*TerminalScale.scale J amountRate)) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add hosts extra)
    _ = _ := by rw [←scale_mul J seatsRate amountRate]; ring

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
