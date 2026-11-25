import OAI.Hierarchy.TaggedWireFundedPacketWord
import OAI.Hierarchy.TaggedWireNativeContinuation

namespace OAI
/-! # Every actual funded prefix has a complete histogram history -/

noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option cleanup.letToHave false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires BoughtSockets
open WireTelescope Tagged ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "w" => Native.wordBits h D Native.copies

variable (size : ℕ) (extent : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh ≤ size) (π : Equiv.Perm (Row h))
  (seed : Boot.Tape h (2^v.W)) (age : v.wideStockHeight ≤ h) (budget : v.keepLimit*width+1 ≤ 2^h) (small : width ≤ 2^h)
local notation "reader" => v.wideSelector h width age budget small
local notation "es" => events v.mesh
local notation "slots" => (reader).format.slot
local notation "base" => v.wideOrigin h width size seed π

include extent in
/-- Starting at any actually chosen prefix, each future funded selection can
place all its copies on a genuine letter of its elected packet. -/
theorem wide_funded_continuation {tail : List Event} {x : Memory w}
    (reached : CalendarTape.Prefix slots es base tail x) :
    Nonempty (CalendarTape.Path slots tail x) := by
  apply CalendarTape.CounterROM.continuation (reader) es base _ reached
  intro a future mem hist row active
  apply lt_of_lt_of_le _ (min_le_min_left _ (v.catalogue_words (v.seed P h width) width).1.ge)
  exact (v.funded_packet_word_of_nonzero h width size extent π seed age budget small hist row active).choose_spec.2.2

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
