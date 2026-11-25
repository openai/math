import OAI.Hierarchy.DescentArchivedStageGeometry
import OAI.Hierarchy.DescentStageVenuePeers
import OAI.Hierarchy.DescentDatedPhysicalOrdinary
import OAI.Hierarchy.DescentObservedPairDate

namespace OAI
/-! # Observe the actual elected multiplier and topology on the reached venue memory -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCompiler DescentPacking.PackedMatch.Local.Stage DescentPacking.PackedMatch
open DescentSixParty DescentSIMDLookup DescentColonies DescentPackedColony DescentKernelHistory.BitDescription
open DescentTerminalEpochDecoder DescentPackedProfileWindow DescentTerminalEpochChart DescentPackedProfileArchive
open DescentPackedProfileWide DescentGroupPeerOrder DescentStageEdgeReceipt
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentPacking.PackedMatch.Local DescentSixParty.StarKeys
noncomputable section
set_option maxHeartbeats 1000000
set_option quotPrecheck false
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

def hostNumbers : (r).V≃Fin (Fintype.card (r).V) :=
  Equiv.ofBijective (r).vertex ((Fintype.bijective_iff_injective_and_card _).mpr ⟨(r).vertex.injective,by simp⟩)

variable (hv : Fintype.card v.prior.V ≤ 2^v.level)
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
    (entry : Source Pin) (z : Pin→Bool) (ext : DescentTerminalEpochBits.width entry.C≤ v.area.shapeAt.digit)

def reachedReport : Prop :=
  ObservedReport A native v.schedule (r).valid v.nonnegative e v.hostNumbers hv c v.bitsPerField
    v.payload v.unit v.profile v.seats rom old
    (some (∀i,(wideCell entry.pin z (sh).digit ext i).val=profileAt (inputNumber v.nonnegative A (e).toEmbedding names)
      ((scannedRows v.nonnegative (A).stage).profile choice) i)) choice rs m (sel w floor)
    (time_ w floor) (fun i=>i<floor ∨ (plan).endAddr≤ i)

theorem incoming_hosts (i j : Fin H) :
    j∈DynamicSplit.incoming rs i ↔ ∃x y:(r).V,i=names x ∧ j=names y ∧ x∈(A).near y :=by
  have each : j∈DynamicSplit.incoming rs i ↔ ∃t : Fin (r).placement.degree,rs i t=some j:=by
    simp [DynamicSplit.incoming,List.mem_filterMap,List.mem_ofFn,eq_comm]
  rw [each]
  constructor
  · rintro ⟨t,ht⟩
    by_cases present : ∃x:(r).V,((r).vertex x).castLE hv=i
    · obtain ⟨x,rfl⟩:=present
      obtain ⟨y,adj,ey⟩:=((r).venueRoster_rows hv x j).mp ⟨Fin.cast (r).branch t,ht⟩
      exact ⟨x,y,rfl,ey.symm,((A).symmetric x y).mp adj⟩
    · change (r).venueRoster hv i (Fin.cast (r).branch t) = some j at ht
      rw [(r).venueRoster_missing hv i present (Fin.cast (r).branch t)] at ht
      contradiction
  · rintro ⟨x,y,rfl,rfl,adj⟩
    obtain ⟨t,ok⟩:=((r).venueRoster_rows hv x (names y)).mpr ⟨y,((A).symmetric y x).mp adj,rfl⟩
    refine ⟨Fin.cast (r).branch.symm t, ?_⟩
    change (r).venueRoster hv (((r).vertex x).castLE hv) (Fin.cast (r).branch (Fin.cast (r).branch.symm t)) = _
    simpa only [Fin.cast_cast, Fin.cast_refl, id_eq] using ok

theorem observed_venue (safe : (a).Space input w floor)
    (venue : stageVenue r hv input M v.bitsPerField floor ((r).venueRoster hv) m)
    (named : (A).SiteNamed rank) (mass : (A).wire*((A).z*v.gadget.b)*(A).cap<2^v.bitsPerField)
    (positions : J*H*2^v.k<2^w) (core : v.world.core.card<2^w)
    (seated : Fintype.card (NativePair v.world.graph v.world.core home color (A).cap)≤v.seats)
    (raw : Stored entry (sh).digit (M*(sh).pairs) ext (plan).raw z m) :
    v.reachedReport input floor hv m choice entry z ext := by
  have physical:=roster_geometry (G:=J) A v.hostNumbers hv v.bitsPerField v.payload v.unit v.profile v.seats
    input floor w rs safe (by have p : 2*v.unit ≤ v.payload := safe.laneWidth
                              have one : 1≤v.unit:=(le_max_left ..).trans safe.inputWidth
                              have hp : 0<v.payload:=by omega
                              exact Nat.le_mul_of_pos_right _ hp) (v.incoming_hosts hv) mass positions core
  obtain ⟨lower,phase,disjoint,weight,earlier,space,apart⟩:=
    chooser_addresses (G:=J) (ℓ:=v.level) A v.bitsPerField v.payload v.unit v.profile v.seats input floor safe
  obtain ⟨_,sorted,actors,cables,hub,hubSize,hubRead,atomFits,atomRead⟩:=venue
  have transport {d₀ d₁ : ℕ} (hdeg : d₀ = d₁) (roster : Fin H → Fin d₁ → Option (Fin H))
      (mounted : Mounted (input.ports d₁) roster m J M) :
      Mounted (input.ports d₀) (fun h j => roster h (Fin.cast hdeg j)) m J M := by
    cases hdeg
    exact mounted
  have ports : Mounted old rs m J M := transport (r).branch ((r).venueRoster hv) sorted
  have chart : Phase.Arena.first (c).chart (A).degree v.k v.bitsPerField (a).phaseWidth≤(plan).raw.base:=earlier
  have cRoom : (a).weightsAt floor≤(plan).raw.base:=by
    have order : (a).phaseAt floor≤Phase.Arena.first (c).chart (A).degree v.k v.bitsPerField (a).phaseWidth:=
      (show (a).phaseAt floor≤Phase.Arena.menu (c).chart (A).degree v.k from Nat.le_add_right ..).trans
      ((show Phase.Arena.menu (c).chart (A).degree v.k≤Phase.Arena.names (c).chart (A).degree v.k (a).phaseWidth
        from Nat.le_add_right ..).trans (Nat.le_add_right ..))
    exact disjoint.trans (order.trans chart)
  have cUp : (a).censusAt floor≤(a).weightsAt floor:=((a).origin_order floor).2.2.1
  apply cpu_installed_observed A native v.schedule (r).valid v.nonnegative e v.hostNumbers hv c v.bitsPerField v.payload
    v.unit w v.profile v.seats rom old input.actors (fun x j=>input.wire x.val j.val) floor input.hubs
    (fun x=>input.atoms x.val) choice rs m physical floor le_rfl lower phase (.inl disjoint) _ _ rfl apart
    named safe.accessible safe.wires actors cables ports safe.inputWidth hub hubSize hubRead
    (fun x=>atomFits x.val) atomRead le_rfl weight le_rfl safe.matchWidth space seated entry z ext m raw
    (fun _ _=>rfl)
  · change (a).censusAt floor+((a).weightsAt floor-(a).censusAt floor)≤(plan).raw.base;omega
  · change (a).phaseAt floor+(Phase.Arena.first (c).chart (A).degree v.k v.bitsPerField (a).phaseWidth-(a).phaseAt floor)≤(plan).raw.base
    have order : (a).phaseAt floor≤Phase.Arena.first (c).chart (A).degree v.k v.bitsPerField (a).phaseWidth:=
      (show (a).phaseAt floor≤Phase.Arena.menu (c).chart (A).degree v.k from Nat.le_add_right ..).trans
      ((show Phase.Arena.menu (c).chart (A).degree v.k≤Phase.Arena.names (c).chart (A).degree v.k (a).phaseWidth from Nat.le_add_right ..).trans (Nat.le_add_right ..))
    omega

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
