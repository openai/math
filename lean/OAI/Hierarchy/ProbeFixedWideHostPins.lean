import OAI.Hierarchy.ProbeFixedWideTagHeader
import OAI.Hierarchy.ProtocolRAMCalendarBootPins
import OAI.Hierarchy.ProbeFixedCatalystMarkets

namespace OAI
/-! # Projection of the complete native input tape from tags, private counters and constants -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard CoreRoute
open StripChart WireTelescope Tagged
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "D" => 2^v.W
local notation "P" => v.widePlacement h width
local notation "B" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "slab" => v.slab (v.seed P h width) P width
local notation "w" => wordBits h D copies
local notation "V" => v.catalystMarkets P h width
open private installed_markets_eq from OAI.Hierarchy.TaggedWireFixedAdmission

set_option cleanup.letToHave false in
set_option maxHeartbeats 1500000 in
/-- All exposed and hidden assignments are admissible inputs to the *pin
map*. The word-level projection writes low exposed tags and chronological
private counters onto a single fixed, fully prepared CPU header. -/
theorem wide_header_pins (stock : Bank) (M : ℕ) (o : Orders h D k)
    (r : ℕ) (banks : RouteSettlement.Banks) (src tbl dst : ℕ) (owners : Bank)
    (size : ℕ) (covers : (A).endAddress v.mesh≤ size)
    (room : (A).endAddress v.mesh<2^w) (count : v.menu.copiesAt v.copyScale width<2^w) :
    let reader:=v.nativeSelector P h width r banks src tbl dst owners room count
    let es:=events v.mesh
    let L:=reader.format.windows
    ∀(tags : Fin (2^h)→Word w) (bits : Bits (CalendarTape.bits reader.format.slot es))
      (seed : Boot.Tape h D),
      Boot.header V size (v.wideTagHeader h width stock M o (L.header es bits seed) tags)=
        Boot.tagRows tags (L.header es bits
          (Boot.header V size (v.wideSignedWords h width stock M (Equiv.refl _) o seed))) := by
  intro reader es L tags bits seed
  have heap := (v.wideGeometryPrefix h width).2.1
  have layout:=v.catalyst_market_layout_at P h width size heap covers
  have pages := Slab.header_slots_at (r:=r) slab B F v.mesh (P).joint.initial width v.keepLimit v.finish (v.basePhase width)
    (P).catalogue banks src tbl dst owners (v.original_selector_room P h width room)
    (v.original_copy_room P h width r banks src tbl dst owners count) size covers
    (heap.trans (v.catalyst_initial_le_first P h width))
  let signed := v.wideSignedWords h width stock M (Equiv.refl _) o
  have move := v.wide_signed_header h width stock M (Equiv.refl _) o
    r banks src tbl dst owners room count bits seed
  have slots := Boot.header_slots V size L es bits (signed seed) (by
    intro event he x inside
    obtain ⟨lo,hi,free⟩ := pages event he x inside
    exact ⟨lo,hi,by simpa only [installed_markets_eq v P h width] using free⟩)
  exact (Boot.header_tagRows V size layout tags (signed (L.header es bits seed))).trans
    (congrArg (Boot.tagRows (z:=h) (d:=D) tags) ((congrArg (Boot.header V size) move).trans slots))

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
