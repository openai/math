import OAI.Hierarchy.DescentDatedMatchedPositiveLayout
import OAI.Hierarchy.DescentMatchedVisitSelected
import OAI.Hierarchy.DescentSelectedMatchBoard
import OAI.Hierarchy.DescentNamedDonorOutputPorts

import OAI.Hierarchy.DescentSelectedMeterRows

namespace OAI
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentSixParty.StarKeys
open DescentRawCablePanel DescentStageEdgeReceipt DescentHostDirectory DescentHostDegree
open DescentPacking DescentPacking.PackedMatch.Local
open scoped Classical Fin.CommRing
open DescentCompiler DescentPacking.PackedMatch.Local.Stage DescentPacking.PackedMatch
open DescentSixParty DescentSIMDLookup DescentColonies DescentPackedColony DescentKernelHistory.BitDescription
open DescentTerminalEpochDecoder DescentPackedProfileWindow DescentTerminalEpochChart DescentPackedProfileArchive
open DescentPackedProfileWide DescentGroupPeerOrder DescentStageEdgeReceipt
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 950000
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (input : Dated.Operands) (floor : ℕ)
local notation "r" => v.prior
local notation "A" => v.prior.placement
local notation "a" => v.area
local notation "H" => 2^v.level
local notation "J" => v.schedule.groupCount v.age
local notation "c" => (a).chooser input.roster floor
local notation "rom" => (a).prepareAt input.roster floor
local notation "plan" => (a).matcher input.roster floor
local notation "M" => (a).lanesAt
local notation "e" => (Equiv.refl (Fin J))
local notation "sh" => (a).shapeAt
local notation "native" => (r).order.trans Fin.valEmbedding
local notation "measure" => (⟨(A).wire,(A).z,(A).hist⟩ : Dated.Measures)

variable (hv : Fintype.card v.prior.V≤2^v.level)
local notation "names" => GroupStage.plane v.hostNumbers hv
local notation "rank" => groupRank ((e).toEmbedding.trans Fin.valEmbedding) ((names).trans Fin.valEmbedding)
local notation "rs" => (fun (h : Fin H) (j : Fin (A).degree)=>(r).venueRoster hv h (Fin.cast (r).branch j))
local notation "old" => input.ports (A).degree
local notation "top" => (plan).layout.topology
local notation "sel" => (a).selected v.gadget (A).fieldBits input measure
local notation "time_" => (a).selectedTicks v.gadget (A).fieldBits input measure
local notation "home" => scanHomeAt v.nonnegative (A).stage
local notation "color" => scanColorAt v.nonnegative (A).stage
variable {w : ℕ} {Pin : Type} (m : Memory w) (choice : (v.prior.placement.stage.result v.nonnegative).Choice)
    (entry : Source Pin) (z : Pin→Bool) (ext : DescentTerminalEpochBits.width entry.C≤v.area.shapeAt.digit)

local notation "nRows" => (a).batch
local notation "tag" => (c).shelves (A).degree v.k v.bitsPerField M
local notation "firstTable" => LayoutSum.Finish.first (plan).layout.topology (plan).layout.out nRows
local notation "flagEnd" => (a).flagEnd input.roster floor
local notation "rotEnd" => (a).rotationEnd input.roster floor
local notation "saved" => fun n : ℕ=>((n<floor ∨ (plan).endAddr≤n) ∧
  (n<firstTable ∨ flagEnd≤n)) ∧ (n<flagEnd ∨ rotEnd≤n)
local notation "cpu" => (a).nativePhase v.gadget (A).fieldBits input measure w floor

local notation "D" => (A).degree
local notation "date₀" => v.ticket.donorDate
local notation "packed" => ((date₀).outputPorts v.payload v.seats input floor v.bitsPerField).packedDonors
local notation "dep" => (date₀).afterMatcher v.payload v.seats input v.bitsPerField floor w
local notation "R" => hostRotor names (DescentGroupPeerOrder.hostRoster A ((names).trans Fin.valEmbedding))

/-- The board at entry to the signed-material pass is obtained from the archived
ballot, signed input wires and the paid native matcher at this same date. -/
theorem board_and_meter_of_observed_match (safe : (a).Space input w floor)
    (seen : v.reachedReport input floor hv m choice entry z ext)
    (hit : ∀i,(wideCell entry.pin z (sh).digit ext i).val=profileAt (inputNumber v.nonnegative A (e).toEmbedding names)
      ((scannedRows v.nonnegative (A).stage).profile choice) i)
    (chosen : HEq v.choice choice)
    (original : (A).SiteNamed rank ∧ ∀x y,native x<native y ↔ originalId v.world.graph.Edge x<originalId v.world.graph.Edge y)
    (budget : Fintype.card (NativePair v.world.graph v.world.core home color (A).cap)*(v.gadget.C+8+8*v.gadget.k)<2^w)
    (venue : stageVenue v.prior hv input M v.bitsPerField floor (v.prior.venueRoster hv) m)
    (height : v.level=Nat.clog 2 (v.schedule.hostSize v.age))
    (price : v.unit=v.ticket.installedDonorWidth v.short v.profile)
    (shortShape : v.short=max (v.k+3) (Nat.clog 2 (D+1)))
    (colors : v.profile=DescentTerminalEpochBits.width v.gadget.C)
    {header factor p : ℕ} (past : header≤rotEnd) (live : 0<v.unit) (ratio : w≤factor*v.payload)
    (room : v.ticket.wholeDonorEnd v.short v.profile H v.payload rotEnd≤2^w)
    (grain : (A).stage.z=v.schedule.grainAt v.gadget.b p v.age) :
    Nonempty (v.SelectedBoard hv R choice ((dep).image ((cpu safe).image m)) packed) ∧
    MeterRows v.ticket header factor ((date₀).counter v.payload rotEnd header) ((dep).image ((cpu safe).image m)) :=by
  have actual := v.matched_layout_of_observation input floor hv m choice entry z ext safe seen hit original.1 budget
  have order_ := (a).subphase_order input floor
  have dateStart : floor≤(plan).endAddr:=order_.1.trans
    (((a).phase_before_winners input.roster floor).trans (order_.2.1.trans order_.2.2.1))
  have stops : (plan).endAddr≤firstTable:=by
    have pad : nRows≤(SixBirths.tapeBank (plan).layout.out nRows).size:=Nat.le_pow_clog (by decide) _
    exact (Nat.add_le_add_left pad _).trans (le_max_right ..)
  have flagAt:=dateStart.trans order_.2.2.2
  have firstAt:=dateStart.trans stops
  have flagEndAt:flagEnd≤rotEnd:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have priorAt:=flagAt.trans flagEndAt
  have protected_ : ∀q : ℕ,q<floor→saved q :=
    fun _ h=>⟨⟨.inl h,.inl (h.trans_le firstAt)⟩,.inl (h.trans_le flagAt)⟩
  obtain ⟨_,_,_,wires,hubFit,hubSize,hubWord,_⟩:=venue
  have ports:=safe.wires
  have gate:=safe.laneWidth
  have embeds:=safe.embed
  cases v with
  | mk dim bits G S q u eps k age z degree wire hist nz nd W prior he T chosen₀ n target link priorBank reference bornBook
      ingress raster vector resolver origin palette repack metadata operandBook signed venue_ level b short payload unit profile seats =>
    obtain rfl:=link.sourceRate
    obtain rfl:=eq_of_heq link.placement
    obtain rfl:=eq_of_heq chosen
    dsimp only at height shortShape colors price
    change level = Nat.clog 2 (S.hostSize age) at height
    change short = max (k+3) (Nat.clog 2 (prior.placement.degree+1)) at shortShape
    change profile = DescentTerminalEpochBits.width G.C at colors
    change unit = link.installedDonorWidth short profile at price
    subst height
    subst shortShape
    subst colors
    subst price
    obtain ⟨assessed,i₀,j₀,hm,mu,paint,winner,rows,births,board⟩:=
      link.matched_visit_selected payload _ _ b seats _ input _ m past live gate embeds ratio room grain
        _ _ actual original flagEndAt (hubFit.2.2.trans priorAt) hubSize hubWord
        (fun j=>protected_ _ ((Nat.add_lt_add_left (j.isLt.trans_le hubSize) _).trans_le hubFit.2.2))
        wires (fun x j t=>protected_ _ ((Nat.add_lt_add_left ((row _ _ _ t).isLt.trans_le (ports x j).2) _).trans_le
          (ports x j).1.2.2))
        (fun x j=>Chooser.bank_before (ports x j).1 priorAt) (fun x j=>(ports x j).2)
    have roomOut:= (link.installed_donor_widths (max (k+3) (Nat.clog 2 (prior.placement.degree+1)))
      (DescentTerminalEpochBits.width (G).C)).2.1
    unfold DepotRAM.Fresh.laneWidth at roomOut
    constructor
    · refine ⟨selected_board_of_match _ _ _ _ _ hm _ original.1 (le_refl _) original.2 winner _ _ _ ?_ rows births board⟩
      let prof := DescentTerminalEpochBits.width G.C
      let bits₀ := max (k+3) (Nat.clog 2 (prior.placement.degree+1))
      let amount₀ := link.installedDonorWidth bits₀ prof
      let width₀ := (shape (2^k) prior.placement.degree (2*prior.placement.cap) prof).outputBits
      have coeff : width₀ ≤ amount₀ := by
        dsimp only [width₀, amount₀, bits₀, prof]
        omega
      have packedFit : amount₀ * lanes payload amount₀ ≤ payload/2 := by
        rw [Nat.mul_comm]
        exact lanes_fit payload amount₀
      change width₀ * lanes payload amount₀ ≤ w
      exact (Nat.mul_le_mul_right _ coeff).trans (packedFit.trans ((Nat.div_le_self ..).trans
        (show payload ≤ w from embeds)))
    · have pins := assessed.2.2
      refine ⟨_,?_,pins,?_⟩
      · let profile₁:=DescentTerminalEpochBits.width (G).C
        let short₁:=max (k+3) (Nat.clog 2 (prior.placement.degree+1))
        let scheduled:=link.ordinaryArea (Nat.clog 2 (S.hostSize age)) b payload
          (link.installedDonorWidth short₁ profile₁) profile₁ seats
        let nativePrior:=link.matchedBanks payload seats (scheduled.prepareAt input.roster floor)
          (input.ports prior.placement.degree) (fun x j=>input.wire x.val j.val) input.hubs
        exact (link.issuedVisit payload _ nativePrior past live gate embeds ratio room grain).fits
      · change Dated.Meter.mk _ _ _ _ _ _ _ _ prior.placement.stage.z _ _ _ =
          Dated.Meter.mk _ _ _ _ _ _ _ _ prior.placement.z _ _ _
        rw [link.quantum]
        rfl


theorem board_of_observed_match (safe : (a).Space input w floor)
    (seen : v.reachedReport input floor hv m choice entry z ext)
    (hit : ∀i,(wideCell entry.pin z (sh).digit ext i).val=profileAt (inputNumber v.nonnegative A (e).toEmbedding names)
      ((scannedRows v.nonnegative (A).stage).profile choice) i)
    (chosen : HEq v.choice choice)
    (original : (A).SiteNamed rank ∧ ∀x y,native x<native y ↔ originalId v.world.graph.Edge x<originalId v.world.graph.Edge y)
    (budget : Fintype.card (NativePair v.world.graph v.world.core home color (A).cap)*(v.gadget.C+8+8*v.gadget.k)<2^w)
    (venue : stageVenue v.prior hv input M v.bitsPerField floor (v.prior.venueRoster hv) m)
    (height : v.level=Nat.clog 2 (v.schedule.hostSize v.age))
    (price : v.unit=v.ticket.installedDonorWidth v.short v.profile)
    (shortShape : v.short=max (v.k+3) (Nat.clog 2 (D+1)))
    (colors : v.profile=DescentTerminalEpochBits.width v.gadget.C)
    {header factor p : ℕ} (past : header≤rotEnd) (live : 0<v.unit) (ratio : w≤factor*v.payload)
    (room : v.ticket.wholeDonorEnd v.short v.profile H v.payload rotEnd≤2^w)
    (grain : (A).stage.z=v.schedule.grainAt v.gadget.b p v.age) :
    Nonempty (v.SelectedBoard hv R choice ((dep).image ((cpu safe).image m)) packed) :=by
  exact (v.board_and_meter_of_observed_match input floor hv m choice entry z ext safe seen hit chosen original
    budget venue height price shortShape colors past live ratio room grain).1


end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
