import OAI.Hierarchy.TaggedWireCalibratedRouting
import OAI.Hierarchy.TaggedWireReachedInput
import OAI.Hierarchy.ProtocolRAMCalendarRemainders

namespace OAI
/-! # The signed native routing and its exact selector language at every matching -/

noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1500000
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AdaptiveProbe StripChart StripDirectory PurchaseFrozen
open WireTelescope Tagged CoreBoard CoreBoard.PhysicalTerm ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (P : v.Placement) (z width r : ℕ) (banks : RouteSettlement.Banks) (src tbl dst : ℕ) (owners : Bank)
local notation "d" => 2^v.W
local notation "N" => List.length (Fabric.shapes (permutationFabric z d))
local notation "slab" => v.slab (v.seed P z width) P width
local notation "B" => v.nativeBoards P z width
local notation "A" => v.privateArena P z width
local notation "H" => v.publicHeader P z width
local notation "W" => wordBits z d copies
local notation "q₀" => (catalogue F (v.configured (v.seed P z width)) v.cost).alphabet
local notation "C" => v.nativeChart P z width r banks src tbl dst owners
local notation "E" => events v.mesh
local notation "V" => Whole.markets v.mesh v.finish (v.basePhase width) (v.nativeFormats P z width)

variable (fits : (v.privateArena P z width).endAddress v.mesh<2^(wordBits z (2^v.W) copies))
  (copiesFit : v.menu.copiesAt v.copyScale width<2^(wordBits z (2^v.W) copies))

local notation "D" => v.nativeSelector P z width r banks src tbl dst owners fits copiesFit
local notation "L" => (D).format.windows

local notation "Tag" => Equiv.Perm (Tagged.Row z)
local notation "R" => CatalystArchive.fuel v.mesh*width

variable (size : ℕ) (input : Equiv.Perm (Tagged.Row z)→Boot.Tape z (2^v.W))
local notation "state" => v.baseline P z width size input

variable (p : Equiv.Perm (Tagged.Row z))
    (tag : ∀i : Fin (2^z),input p i.val=((p.symm i).val:Word (wordBits z (2^v.W) copies)))
    (covers : (v.privateArena P z width).endAddress v.mesh≤ size)
    (heap : heapEnd z (2^v.W) copies≤P.joint.initial)
    (mountedAll : ∀raw,Calendar.mounted (v.nativeChart P z width r banks src tbl dst owners) (events v.mesh)
      (Boot.booted (Whole.markets v.mesh v.finish (v.basePhase width) (v.nativeFormats P z width)) size
        ((v.nativeSelector P z width r banks src tbl dst owners fits copiesFit).format.windows.header
          (events v.mesh) raw (input p))))

private theorem prefix_markets :
    Whole.markets v.mesh v.finish (v.basePhase width)
      (StripChart.formats F v.mesh (Slab.arena slab B) P.joint.initial (Slab.install slab B v.mesh))=V := by
  rw [v.nativeBoards_install P z width]
  rfl

include tag covers heap in
theorem raw_boot (raw : Bits (CalendarTape.bits (D).format.slot E)) :
    Boot.booted V size ((L).header E raw (input p))=(L).header E raw (state p) := by
  have original:=Slab.boot_original_at (r:=r) slab B F v.mesh P.joint.initial width v.keepLimit v.finish (v.basePhase width) P.catalogue
    banks src tbl dst owners (v.original_selector_room P z width fits)
    (v.original_copy_room P z width r banks src tbl dst owners copiesFit)
    size covers (heap.trans (v.catalyst_initial_le_first P z width)) Nat.one_le_two_pow p.symm (input p) tag raw
  simpa only [baseline,nativeSelector,v.prefix_markets P z width] using! original

local notation "EF" => Slab.effects (r:=r) slab B F v.mesh P.joint.initial width v.keepLimit v.finish (v.basePhase width) P.catalogue
  banks src tbl dst owners
local notation "date" => Slab.dates_separate (r:=r) slab B F v.mesh P.joint.initial width v.keepLimit v.finish (v.basePhase width)
  P.catalogue banks src tbl dst owners (v.original_selector_room P z width fits)
    (v.original_copy_room P z width r banks src tbl dst owners copiesFit)
local notation "boot_eq" => v.raw_boot P z width r banks src tbl dst owners fits copiesFit size input p tag covers heap

include tag covers heap mountedAll in
/-- The same joint structural mount handles all reachable prefixes, including
the state just before the next private word is installed. -/
def visited {remaining m} (t : CalendarTape.Prefix (D).format.slot E (state p) remaining m) :
    CalendarTape.CounterROM.OnTape D E remaining (state p) m :=
  (D).original_input EF E (state p) date (fun raw=>boot_eq raw ▸ mountedAll raw) t

variable {e : Event} {remaining : List Event} {m : Memory (wordBits z (2^v.W) copies)}
    (t : CalendarTape.Prefix (v.nativeSelector P z width r banks src tbl dst owners fits copiesFit).format.slot
      (events v.mesh) (v.baseline P z width size input p) (e::remaining) m)

local notation "T" => v.visited P z width r banks src tbl dst owners fits copiesFit size input p tag covers heap mountedAll t

theorem visited_slot :
    Calendar.Slot C (Boot.booted V size ((L).header E (T).bits (input p))) e (T).prior remaining m :=
  slot_of_split C _ e (T).prior remaining m (T).split ((congrArg (run C (T).prior) (boot_eq (T).bits)).trans (T).state)
    (mountedAll (T).bits)

include t tag covers heap mountedAll in
/-- Installing an authentic histogram before its event changes no earlier
elections. This yields the original booted RAM slot for each independent
hypothetical branch in the local *sum*, including the genuine funded stocks. -/
theorem visited_choice (c : ((D).format.slot e).choice m) :
    ∃ raw : Bits (CalendarTape.bits (D).format.slot E), ∃ prior : List Event,
      Calendar.Slot C (Boot.booted V size ((L).header E raw (input p))) e prior remaining ((D).patch e m c) := by
  let row:=(T).patch D EF E (state p) date (fun raw=>boot_eq raw ▸ mountedAll raw) c
  exact ⟨row.bits,row.prior,slot_of_split C _ e row.prior remaining _ row.split
    ((congrArg (run C row.prior) (boot_eq row.bits)).trans row.state) (mountedAll row.bits)⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
