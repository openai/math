import OAI.Computability.VPVNP.CompressorRefreshPassCalendar
import OAI.Computability.VPVNP.CompressorPacketPassRun
import OAI.Computability.VPVNP.CompressorNativePassRates
import OAI.Computability.VPVNP.CompressorRefreshEmitSources
import OAI.Computability.VPVNP.CompressorRefreshSelectorMount

/-! # The selected refresh in the physical pass calendar

The concrete header and demand packets fix one common prefix. The incoming
graph and the selected payload history are transferred to the returning
memory, with the cost charged to the fixed catalog over all visited rows.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section
set_option quotPrecheck false

namespace CompressorRecords.RefreshPass

open BurstRAM Compression DescriptorSpace BlockPlanner PassTimeline Schedule SourceTransport
open PairSimulation.LocalHistory PairSimulation.TraversalRoles ScheduledTrace
open scoped Fin.CommRing

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f) {g w : ℕ}
variable (pub : Fin 11 → Word w) (positions blocks t n : ℕ)
variable (X : State S.portExponent (S.portExponent + g))
local notation "script" => BlockProgram.script B
local notation "L" => BlockProgram.layout B (pub 2).val positions blocks
local notation "loc" => (⟨t, .refresh⟩ : Located S.steps)
local notation "o" => PassOrigin.refresh (B := B) (f := f) (hf := hf) X
local notation "pass" => Refresh.dyadicRefreshPass X S.graph (Nat.two_pow_pos _)
  (S.port_bound.connected_and_pos S.port_order).1 B.refresh S.port_order S.degree_bounds.2
  (f ∘ Sum.inr) ((B.solution_iff f).mp hf).2
local notation "Choice" => (pass).step.Choice
local notation "cur" => Script.levelsPerBlock script * t + S.steps
local notation "total" => directoryRows L
local notation "pkt" => SourceOnline.Packet script w

variable (initial : TaggedLayer) (initialFrame : Fin 8 → Word w)
local notation "resident" =>
  CompiledResident.resident B f hf (pub 2) positions blocks n initial initialFrame

private theorem next_slots (size : X.positions ≤ positions)
    (encode : Choice → List Bool) (c : Choice) :
    IncidenceDirectory.slotCount ((pass).next c) ≤ slotCapacity L := by
  let v := ScheduledTrace.level o encode c
  have slots : v.outputSlots = IncidenceDirectory.slotCount (v.pass.next v.term) := by
    rw [SelectedLevel.outputSlots, SelectedLevel.outputSites, State.positions, Fintype.card_prod,
      Fintype.card_congr (bitWordFinEquiv _), Fintype.card_fin]
  change IncidenceDirectory.slotCount (v.pass.next v.term) ≤ positions * slotDegree S
  rw [← slots]
  exact v.outputSlots_le.trans (Nat.mul_le_mul_right _ size)

/-- Consume the actual common preparation and the verified raw suffix
returned for each selected term. The output retains the current graph and
every previous parser payload in the physical live memory. -/
theorem ofSources {small cap : ℕ} (shrinking : Fin S.steps → ℕ)
    (m : Memory w) (past : List (SelectedLevel B f hf)) (encode : Choice → List Bool)
    (ready : Boundary resident pub (levelWords L : Word w) total ((loc).first B) past X m)
    (ht : t < blocks) (depth : past.length = cur)
    (size : X.positions ≤ positions) (fit : endAddress L < 2 ^ w)
    (clock : small ≤ cap) (big : Online.Run.ControlBounds (script).plan cap (w := w))
    (bounds : Online.Run.ControlBounds (script).plan small (w := w))
    (hs ds : List pkt) (term : Choice → pkt) (tail : Choice → List pkt)
    (src : RefreshEmit.Sources B f hf (pub 2) positions blocks t small n initial initialFrame
      past X encode m hs ds term tail)
    (termCap : ℕ)
    (width : SelectedTermWorker.fitConstant B + 4 * Nat.clog 2 (X.maxWireWidth + 1) ≤ w)
    (fuel : TermWorker.budget B.refresh (RefreshBlockPlan.shape B).ties
      ((RefreshBlockPlan.shape B).ports * (RefreshBlockPlan.shape B).dH) w X.maxWireWidth ≤ termCap)
    (scanClock : SourceOnline.scanCap script (max 64 termCap) ≤ small) :
    Nonempty (PassRun resident pub (levelWords L : Word w) total cap small
      (nativePassRate script (commonRawRate shrinking (RefreshEmit.rawRate B)) * positions)
      loc o encode past m) := by
  have selector : (loc).first B + (hs ++ ds).length =
      (script).initial.length + t * (script).block.length +
        (BlockIndex.blockRefresh B).index.val := by
    rw [first_eq, Nat.add_assoc,
      RefreshSelector.before_offset B f hf pub positions blocks t X src.before]
  have endFit := finish_le_total B t (pub 2).val positions blocks ht
  have preFit : (loc).first B + (hs ++ ds).length < total := by
    rw [selector]
    have inBlock : (BlockIndex.blockRefresh B).index.val < (script).block.length :=
      (BlockIndex.blockRefresh B).index.isLt
    apply lt_of_lt_of_le _ endFit
    rw [finish_eq, Nat.add_mul, one_mul]
    change _ < (script).initial.length + (t * (script).block.length + (script).block.length)
    omega
  have dataStart : levelStart L 0 < 2 ^ w := (levelStart_mono L (Nat.zero_le _)).trans_lt fit
  apply PassRun.ofInstalledPacketGroups (hs ++ ds) term tail src.first src.middle src.last
    src.before.quiet src.emptyTail src.termBits clock big bounds rfl rfl dataStart preFit endFit
    src.lengths le_rfl (fun _ _ => rfl) ready
  · intro mid agree _ htag ord rows stride
    exact RefreshSelector.mountBefore B f hf pub positions blocks t X termCap small cap m hs ds
      src.before ht size fit width fuel scanClock clock mid agree htag (ord.trans selector)
      rows stride
  · exact src.stored
  · intro c u v agree h
    have nextIndex : (past ++ [level o encode c]).length < (L).levels := by
      simpa only [List.length_append, List.length_singleton, depth, Nat.add_assoc] using
        src.before.newLive
    exact DetailedResident.transfer h nextIndex fit (by change 14 ≤ 54; decide)
      (next_slots B f hf pub positions blocks X size encode c) agree
  · intro c
    exact passCharges_le B X loc shrinking (RefreshEmit.rawRate B) positions size
      (hs ++ ds) (term c) (tail c) (src.lengths c) (RefreshEmit.raw_le B X (src.rawCharge c))

end CompressorRecords.RefreshPass

end

end VPVNP
end Computability
end OAI
