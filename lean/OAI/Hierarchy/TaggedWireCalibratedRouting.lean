import OAI.Hierarchy.TaggedWireFixedAdmission
import OAI.Hierarchy.TaggedWireActiveRouting
import OAI.Hierarchy.ProbeCatalystArchiveRows

namespace OAI
/-! # The signed native routing and its exact selector language at every matching -/

noncomputable section
set_option quotPrecheck false
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

/-- The matching read from the tag is the inverse of the path convention in
the native exterior center-to-center CT rows. Every initial memory here has
only the original permutation and public tape. -/
def baseline (size : ℕ) (input : Tag→Boot.Tape z d) (p : Tag) :=
  Boot.booted V size (input p)

variable (size : ℕ) (input : Equiv.Perm (Tagged.Row z)→Boot.Tape z (2^v.W))
local notation "state" => v.baseline P z width size input

abbrev RoutedSchedule :=
  CalendarTerms F z d k width R v.radius 1 (D).format.slot E state

variable (Z : v.RoutedSchedule P z width r banks src tbl dst owners fits copiesFit size input)

/-- A single board for all original permutations, with physical catalyst
fibers and one common selector encoding, regardless of the signed branch. -/
def routing (Shared : Type) [Fintype Shared] : Tagged.NativeRouting F k z width v.radius :=
  Z.nativeRouting Shared

theorem routing_language (Shared : Type) [Fintype Shared] (p : Tag)
    (tag : ∀i:Fin (2^z),input p i.val=((p.symm i).val:Word W)) (raw : Bits (CalendarTape.bits (D).format.slot E))
    (covers : (A).endAddress v.mesh≤ size) (heap : heapEnd z d copies≤P.joint.initial)
    (keyEnd : (stratumHeader z d k v.sampler.degree v.depth P.routes.directory.keysBase).stop≤P.joint.initial)
    (cap : v.menu.maximum<2^W) (threshold : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊<2^W)
    (origin : (H).menus.leftAlphabet.Capped q₀ (Boot.booted V size ((L).header E raw (input p))) ∧
      (H).menus.rightAlphabet.Capped q₀ (Boot.booted V size ((L).header E raw (input p))))
    (mounted : ∀bits,Calendar.mounted C E (Boot.booted V size ((L).header E bits (input p)))) :
    let rout:=v.routing P z width r banks src tbl dst owners fits copiesFit size input Z Shared
    admissible C E (Boot.booted V size ((L).header E raw (input p))) ↔
      ∃! i:Fin (rout.count p),rout.encoding p i=raw :=
  (v.tape_admission_at P z width r banks src tbl dst owners fits copiesFit size covers p.symm (input p) tag raw heap keyEnd cap threshold origin mounted).trans
    (Z.encoding_iff Shared p raw).symm

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
