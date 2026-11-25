import OAI.Hierarchy.TaggedWireStripReplay
import OAI.Hierarchy.ProtocolRAMCalendarStripChoices

namespace OAI
/-! # The native pre-choice election reads only the genuine earlier banks -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.StripChart.Slab
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseFrozen PurchaseStage StripDirectory
open WireTelescope Tagged Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {z d k q depth r : ℕ}
local notation "N" => List.length (Fabric.shapes (permutationFabric z d))
local notation "W" => wordBits z d copies
variable (v : Slab) (s : Boards z d k q depth) (F : Type*) [Field F]
  [SiteNaming (ColumnSite (PayloadStrip.Columns (List.length (Fabric.shapes (permutationFabric z d)))) k)] [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
  (c : Mesh) (initial width cap : ℕ) (finish : ℝ) (prices : PhasePrice) (catalogue : CatalogueRows.Board)
  (banks : RouteSettlement.Banks) (src tbl dst : ℕ) (owners : Bank)
local notation "A" => arena v s
local notation "C" => chart F c A initial width cap (install v s c) finish prices catalogue r banks src tbl dst owners
variable (room : q*rows s ≤ 2^(wordBits z d copies))
  (copyRoom : ∀a, ((chart F c (arena v s) initial width cap (install v s c)
    finish prices catalogue r banks src tbl dst owners).raw a).batch.copies < 2^(wordBits z d copies))
local notation "D" => selectorROM v s F c initial width cap finish prices catalogue banks src tbl dst owners room copyRoom

local notation "L" => (D).format.windows
local notation "E" => events c

/-- Accepting raw histograms are exactly the encodings of the signed histories,
on the original native chart. The alphabet read is taken in the genuine
right-side prefix run; no branch is required for an invalid raw candidate. -/
theorem original_admission (baseline : Memory W) (raw : Bits (CalendarTape.bits (D).format.slot E))
    (all : ∀input,mounted C E ((L).header E input baseline))
    (fits : (A).endAddress c<2^W)
    (tables : ∀a,.attempt a∈E→beforeTables v s F c initial a)
    (alphabet : ∀a prior tail,E=prior++(.attempt a::tail)→
      ∀i,CalendarTape.CounterROM.measured («C»:=C) a (run C prior ((L).header E raw baseline)) i≤q) :
    admissible C E ((L).header E raw baseline) ↔
      ∃! p : CalendarTape.Path (D).format.slot E baseline, CalendarTape.encode (D).format.slot E baseline p=raw := by
  apply authentic_admission v s F c initial width cap finish prices catalogue banks src tbl dst owners
    room copyRoom baseline raw all
  intro a prior tail m u split runEq agree readyM readyU
  have event : Event.attempt a∈E := by simp [split]
  have low : Below ((A).base c (.attempt a)) m u := by
    have seq : ((E).map (position c)).Pairwise (·<·) := by rw [positions];exact List.pairwise_lt_range
    have sorted : (E).Pairwise (fun x y=>position c x<position c y) := by simpa only [List.pairwise_map] using seq
    have later:=(List.pairwise_cons.mp (List.pairwise_append.mp (split ▸ sorted)).2.1).1
    intro x hx
    apply agree x
    rintro ⟨e,occurs,bounds⟩
    rcases List.mem_cons.mp occurs with rfl|next
    · exact (Nat.not_le_of_gt hx) bounds.1
    · have bound:=unread_page (r:=r) v s F c initial width cap finish prices catalogue banks src tbl dst owners
        room copyRoom (.attempt a) later x ⟨e,next,bounds⟩
      omega
  have wide : 4≤2^W := calc
    4=2^2:=by decide
    _≤2^W:=Nat.pow_le_pow_right (by decide) (by unfold Native.wordBits;omega)
  have baseFit : (A).base c (.attempt a)<2^W :=
    (Nat.le_add_right ..).trans_lt (((A).within c _ event).trans_lt fits)
  exact choice_before v s F c initial width cap finish prices catalogue banks src tbl dst owners D a m u low
    readyM readyU wide baseFit (tables a event) (runEq ▸ alphabet a prior tail split)

end Hierarchy.ProtocolRAM.Calendar.StripChart.Slab

end
end OAI
