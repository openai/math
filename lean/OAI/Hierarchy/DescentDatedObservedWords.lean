import OAI.Hierarchy.DescentDatedPhysicalObservation
import OAI.Hierarchy.DescentDatedOrdinaryPhase
import OAI.Hierarchy.DescentOrdinaryFinalCount

namespace OAI
/-! # The retained matrix and pair count of the numbered public ordinary matcher -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentCompiler DescentPacking.PackedMatch.Local.Stage DescentPacking.PackedMatch DescentSixParty
open DescentColonies DescentPackedColony DescentKernelHistory.BitDescription DescentSIMDLookup
open DescentPackedProfileWide DescentTerminalEpochDecoder DescentPackedProfileWindow DescentTerminalEpochChart
open DescentStageEdgeReceipt DescentGroupPeerOrder DescentPackedProfileArchive
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1000000
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (input : Dated.Operands) (root : ℕ)
local notation "floor" => v.stageStart root
local notation "r" => v.prior
local notation "A" => (r).placement
local notation "a" => v.area
local notation "H" => 2^v.level
local notation "J" => v.schedule.groupCount v.age
local notation "c" => (a).chooser input.roster floor
local notation "rom" => (a).prepareAt input.roster floor
local notation "plan" => (a).matcher input.roster floor
local notation "M" => (a).lanesAt
local notation "N" => (a).batch
local notation "shape_" => (a).shapeAt
local notation "e" => Equiv.refl (Fin J)
local notation "measure" => (⟨(A).wire,(A).z,(A).hist⟩:Dated.Measures)
local notation "top" => (plan).layout.topology
local notation "ft" => LayoutSum.Finish.first top (plan).layout.out N
local notation "at_" => v.primitiveEnd floor
local notation "selected" => (a).selected v.gadget (A).fieldBits input measure
local notation "timed" => (a).selectedTicks v.gadget (A).fieldBits input measure
local notation "rot" => (a).rotationEnd input.roster floor
local notation "saved" => (a).flagEnd input.roster floor+2^v.k
local notation "μ" => multiplier (A).fieldBits (scannedRows v.nonnegative (A).stage).μ
variable (wide : Fintype.card v.prior.V ≤ 2^v.level)
local notation "names" => GroupStage.plane v.hostNumbers wide
local notation "rank" => groupRank ((e).toEmbedding.trans Fin.valEmbedding) ((names).trans Fin.valEmbedding)
local notation "rs" => (fun (h : Fin H) (j : Fin (A).degree)=>(r).venueRoster wide h (Fin.cast (r).branch j))

theorem selector_before :
    ((c).shelves (A).degree v.k v.bitsPerField M).mu< ft :=by
  have before : ((c).shelves (A).degree v.k v.bitsPerField M).mu< (a).winnerEnd input.roster floor:=by
    change Phase.Arena.seedWork (c).chart (A).degree v.k v.bitsPerField (a).phaseWidth+3*(c).chart.page+
        (2^v.k-1-1)< Phase.Arena.endAt (c).chart (A).degree v.k v.bitsPerField (a).phaseWidth+_
    unfold Phase.Arena.endAt Phase.Arena.colorWork Phase.Arena.selected
    have positive := Nat.two_pow_pos v.k
    omega
  have order := (a).subphase_order input floor
  have pads : N≤ (SixBirths.tapeBank (plan).layout.out N).size:=Nat.le_pow_clog (by decide) _
  have stop : (plan).endAddr≤ ft:=(Nat.add_le_add_left pads _).trans (le_max_right ..)
  exact before.trans_le (order.2.1.trans (order.2.2.1.trans stop))

/-- Applies even on the first rejected ballot. The observed matching is fully
determined before either output word is read. -/
theorem observed_words_at_primitive_end {w : ℕ} {Pin : Type} (m : Memory w) (choice : (v.prior.placement.stage.result v.nonnegative).Choice)
    (entry : Source Pin) (z : Pin→Bool) (ext : DescentTerminalEpochBits.width entry.C≤ (shape_).digit)
    (safe : (a).Space input w floor) (same : v.old=input.roster)
    (seen : v.reachedReport input floor wide m choice entry z ext) (named : (A).SiteNamed rank)
    (donor more : NativePhase w) (paid : ∀o,donor.Runs o) (advance : ∀o,more.Runs o)
    (frame : ∀o j,j< rot ∨ at_≤ j → (donor.seq more).image o j=o j)
    (later : rot≤ at_) (room : v.fullEnd root< 2^w) :
    let match_:=(a).nativePhase v.gadget (A).fieldBits input measure w floor safe
    let dated:=(match_.seq donor).seq (more.seq (v.counter floor w))
    dated.Runs m ∧ dated.image m (v.countAddr root)=((Fintype.card (scannedRows v.nonnegative (A).stage).pairs):Word w) ∧
      dated.image m saved=((DescentExterior.matrixCode μ).val:Word w) :=by
  intro match_ dated
  have width : SixBirths.width shape_ M≤ w:=
    (LayoutSum.Finish.width_le shape_ M v.unit v.payload safe.birthWidth
      (by
        change v.unit * lanes v.payload v.unit ≤ v.payload / 2
        rw [Nat.mul_comm]
        exact lanes_fit v.payload v.unit)).trans
      ((Nat.div_le_self ..).trans safe.embed)
  have topo : (top).Fits w at_ :=by
    have end_ : (top).base+(top).size≤ (a).flagEnd input.roster floor:=by
      rw [(a).flag_at input.roster floor]
      apply ((a).packed_last input.roster floor).1.trans
      repeat first | rfl | apply Nat.le_add_right_of_le
    have a₁ : (a).flagEnd input.roster floor≤ rot := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
    have a₂ : at_≤ v.fullEnd root:=by
      change at_ ≤ at_ + 2^v.countBits + v.area.batch + 1
      exact (Nat.le_add_right _ (2^v.countBits)).trans
        ((Nat.le_add_right _ v.area.batch).trans (Nat.le_add_right _ 1))
    exact ⟨Nat.two_pow_pos _,((Nat.le_add_left ..).trans (end_.trans (a₁.trans (later.trans a₂)))).trans_lt room,
      end_.trans (a₁.trans later)⟩
  have join:=ObservedReport.count_on_public_date A ((r).order.trans Fin.valEmbedding) v.schedule (r).valid v.nonnegative
    e v.hostNumbers wide c v.bitsPerField v.payload v.unit v.profile v.seats rom (input.ports (A).degree) _ choice
    rs m (selected w floor) (timed w floor) _ seen named (v.selector_before input root) width match_ donor more
    rfl ((a).nativePhase_all v.gadget (A).fieldBits input measure w floor safe m) paid advance at_ frame later topo room
  dsimp only [dated]
  unfold counter
  rw [same]
  exact ⟨join.1, join.2.1, join.2.2.1⟩

theorem observed_words {w : ℕ} {Pin : Type} (m : Memory w) (choice : (v.prior.placement.stage.result v.nonnegative).Choice)
    (entry : Source Pin) (z : Pin→Bool) (ext : DescentTerminalEpochBits.width entry.C≤ (shape_).digit)
    (safe : (a).Space input w floor) (same : v.old=input.roster)
    (seen : v.reachedReport input floor wide m choice entry z ext) (named : (A).SiteNamed rank)
    (donor more : NativePhase w) (paid : ∀o,donor.Runs o) (advance : ∀o,more.Runs o)
    (frame : ∀o j,j< rot ∨ v.operandEnd floor ≤ j → (donor.seq more).image o j=o j)
    (later : rot ≤ v.operandEnd floor) (room : v.fullEnd root< 2^w) :
    let match_:=(a).nativePhase v.gadget (A).fieldBits input measure w floor safe
    let dated:=(match_.seq donor).seq (more.seq (v.counter floor w))
    dated.Runs m ∧ dated.image m (v.countAddr root)=((Fintype.card (scannedRows v.nonnegative (A).stage).pairs):Word w) ∧
      dated.image m saved=((DescentExterior.matrixCode μ).val:Word w) := by
  have support : v.operandEnd floor ≤ at_ := (v.primitive_spent (v.operandEnd floor)).2
  exact v.observed_words_at_primitive_end input root wide m choice entry z ext safe same seen named donor more paid advance
    (fun o j hj => frame o j (hj.imp_right support.trans)) (later.trans support) room

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
