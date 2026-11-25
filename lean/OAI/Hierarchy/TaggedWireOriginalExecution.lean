import OAI.Hierarchy.TaggedWireFixedPrefix
import OAI.Hierarchy.TaggedWireBranchReplay

namespace OAI
/-! # An encoded complete branch reaches its actual original funded terminal store -/

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

local notation "EF" => Slab.effects (r:=r) slab B F v.mesh P.joint.initial width v.keepLimit v.finish (v.basePhase width) P.catalogue
  banks src tbl dst owners
local notation "date" => Slab.dates_separate (r:=r) slab B F v.mesh P.joint.initial width v.keepLimit v.finish (v.basePhase width)
  P.catalogue banks src tbl dst owners (v.original_selector_room P z width fits)
    (v.original_copy_room P z width r banks src tbl dst owners copiesFit)
local notation "boot_eq" => v.raw_boot P z width r banks src tbl dst owners fits copiesFit size input p tag covers heap

private theorem original_disjoint : (L).disjoint E := by
  unfold nativeSelector
  exact Slab.original_pages_separate (r:=r) slab B F v.mesh P.joint.initial width v.keepLimit v.finish (v.basePhase width)
    P.catalogue banks src tbl dst owners (v.original_selector_room P z width fits)
    (v.original_copy_room P z width r banks src tbl dst owners copiesFit)

local notation "apart" => original_disjoint v P z width r banks src tbl dst owners fits copiesFit

include tag covers heap mountedAll in
theorem original_execution (j : CalendarTape.Path (D).format.slot E (state p)) :
    CalendarTape.terminal (D).format.slot E (state p) j=
      run C E (Boot.booted V size ((L).header E (CalendarTape.encode (D).format.slot E (state p) j) (input p))) := by
  rw [boot_eq]
  exact (D).terminal_encoded EF E (state p) apart date (fun raw=>boot_eq raw ▸ mountedAll raw) j

include tag covers heap mountedAll in
theorem original_suffix_replay {tail x} (t : CalendarTape.Prefix (D).format.slot E (state p) tail x)
    (j : CalendarTape.Path (D).format.slot tail x) :
    let full:=t.withSuffix j
    let raw:=CalendarTape.encode (D).format.slot E (state p) full
    let source:=Boot.booted V size ((L).header E raw (input p))
    ∃prior,E=prior++tail ∧ ReadBanks.Agree ((D).hidden tail) x (run C prior source) := by
  dsimp only
  rw [boot_eq]
  obtain ⟨prior,eq,mem,_⟩:=(D).replay_suffix EF E (state p)
    apart
    date (fun raw=>boot_eq raw ▸ mountedAll raw) t j
  exact ⟨prior,eq,mem⟩

include tag covers heap mountedAll in
theorem original_choice_replay {e tail x} (t : CalendarTape.Prefix (D).format.slot E (state p) (e::tail) x)
    (c : ((D).format.slot e).choice x) (next : CalendarTape.Path (D).format.slot tail (((D).format.slot e).next x c)) :
    let j:=t.withSuffix ⟨c,next⟩
    let raw:=CalendarTape.encode (D).format.slot E (state p) j
    let source:=Boot.booted V size ((L).header E raw (input p))
    ∃prior,Calendar.Slot C source e prior tail (run C prior source) ∧
      ReadBanks.Agree ((D).hidden tail) ((D).patch e x c) (run C prior source) := by
  dsimp only
  rw [boot_eq]
  exact (D).replay_choice EF E (state p)
    apart
    date (fun raw=>boot_eq raw ▸ mountedAll raw) t c next

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
