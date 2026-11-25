import OAI.Hierarchy.TaggedWireBootAdmission
import OAI.Hierarchy.ProbeFixedElectionPages

namespace OAI
/-! # The literal selector tape and authenticated branch of a calibrated native protocol -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AdaptiveProbe StripChart StripDirectory PurchaseFrozen
open WireTelescope Tagged ThreeFlat.RAM
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

theorem original_selector_room (fits : (A).endAddress v.mesh<2^W) :
    q₀*Slab.rows B≤2^W := by
  have lower : q₀*Slab.rows B≤(A).stride := by
    change q₀*Slab.rows B≤Slab.stride slab B
    apply (Slab.selector_room B).trans
    change Slab.selectorSpan B≤Slab.stride slab B
    simp only [Slab.stride,PostLayout.column,PostLayout.startColumns,Slab.mask,Slab.flags,Slab.first,
      Nat.zero_add,Nat.add_assoc]
    exact Nat.le_add_right ..
  have positive : 0<(E).length:=by rw [event_count];have h:=v.clock.inject_pos;positivity
  have total : (A).stride≤(E).length*(A).stride := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (A).stride positive
  exact lower.trans (total.trans ((Nat.le_add_left _ _).trans fits.le))

theorem original_copy_room (fits : v.menu.copiesAt v.copyScale width<2^W) (a : Attempt) :
    ((C).raw a).batch.copies<2^W := by
  have count:=(v.ordinary_dimensions P z width a).2
  have same : ((C).raw a).batch.copies=(v.nativeFormats P z width a).histMass := by
    cases a <;> rfl
  rw [same]
  exact count.trans_lt fits

variable (fits : (v.privateArena P z width).endAddress v.mesh<2^(wordBits z (2^v.W) copies))
  (copiesFit : v.menu.copiesAt v.copyScale width<2^(wordBits z (2^v.W) copies))

def nativeSelector : CalendarTape.CounterROM C :=
  Slab.selectorROM (r:=r) slab B F v.mesh P.joint.initial width v.keepLimit v.finish (v.basePhase width) P.catalogue
    banks src tbl dst owners (v.original_selector_room P z width fits)
    (v.original_copy_room P z width r banks src tbl dst owners copiesFit)

local notation "D" => v.nativeSelector P z width r banks src tbl dst owners fits copiesFit
local notation "L" => (D).format.windows

private theorem installed_chart_eq :
    StripChart.chart F v.mesh (Slab.arena slab B) P.joint.initial width v.keepLimit
      (Slab.install slab B v.mesh) v.finish (v.basePhase width) P.catalogue r banks src tbl dst owners=C := by
  rw [v.nativeBoards_install P z width]; rfl

private theorem installed_markets_eq :
    Whole.markets v.mesh v.finish (v.basePhase width)
      (StripChart.formats F v.mesh (Slab.arena slab B) P.joint.initial (Slab.install slab B v.mesh))=V := by
  rw [v.nativeBoards_install P z width]; rfl

set_option cleanup.letToHave false in
set_option maxHeartbeats 1500000 in
theorem tape_admission_at (size : ℕ) (covers : (A).endAddress v.mesh≤ size) (π : Equiv.Perm (Fin (2^z))) (mem : Boot.Tape z d)
    (perm : ∀i:Fin (2^z),mem i.val=((π i).val:Word W)) (raw : Bits (CalendarTape.bits (D).format.slot E))
    (heap : heapEnd z d copies≤P.joint.initial)
    (keyEnd : (stratumHeader z d k v.sampler.degree v.depth P.routes.directory.keysBase).stop≤P.joint.initial)
    (cap : v.menu.maximum<2^W) (threshold : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊<2^W)
    (origin : (H).menus.leftAlphabet.Capped q₀ (Boot.booted V size ((L).header E raw mem)) ∧
      (H).menus.rightAlphabet.Capped q₀ (Boot.booted V size ((L).header E raw mem)))
    (mounted : ∀bits,Calendar.mounted C E (Boot.booted V size ((L).header E bits mem))) :
    admissible C E (Boot.booted V size ((L).header E raw mem)) ↔
      ∃! j : CalendarTape.Path (D).format.slot E (Boot.booted V size mem),
        CalendarTape.encode (D).format.slot E (Boot.booted V size mem) j=raw := by
  refine Slab.boot_admission_at (r:=r) slab B F v.mesh P.joint.initial width v.keepLimit v.finish (v.basePhase width) P.catalogue
    banks src tbl dst owners (v.original_selector_room P z width fits)
    (v.original_copy_room P z width r banks src tbl dst owners copiesFit) size covers
    (heap.trans (v.catalyst_initial_le_first P z width))
    Nat.one_le_two_pow π mem perm raw (by
      intro bits
      simpa only [nativeSelector, v.installed_chart_eq P z width r banks src tbl dst owners,
        v.installed_markets_eq P z width] using! mounted bits)
    fits (fun a _=>v.election_pages P z width a cap threshold keyEnd) ?_
  intro a prior tail split i
  let initial := Boot.booted V size ((L).header E raw mem)
  have all : Calendar.mounted C E initial := mounted raw
  have h := (mounted_append C prior (.attempt a::tail) initial).mp
    ((congrArg (fun days => Calendar.mounted C days initial) split).mp all)
  exact v.native_measured P z width r banks src tbl dst owners prior a _ origin h.1 h.2.1 i

theorem tape_admission (π : Equiv.Perm (Fin (2^z))) (mem : Boot.Tape z d)
    (perm : ∀i:Fin (2^z),mem i.val=((π i).val:Word W)) (raw : Bits (CalendarTape.bits (D).format.slot E))
    (heap : heapEnd z d copies≤P.joint.initial)
    (keyEnd : (stratumHeader z d k v.sampler.degree v.depth P.routes.directory.keysBase).stop≤P.joint.initial)
    (cap : v.menu.maximum<2^W) (threshold : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊<2^W)
    (origin : (H).menus.leftAlphabet.Capped q₀ (Boot.booted V ((A).endAddress v.mesh) ((L).header E raw mem)) ∧
      (H).menus.rightAlphabet.Capped q₀ (Boot.booted V ((A).endAddress v.mesh) ((L).header E raw mem)))
    (mounted : ∀bits,Calendar.mounted C E (Boot.booted V ((A).endAddress v.mesh) ((L).header E bits mem))) :
    admissible C E (Boot.booted V ((A).endAddress v.mesh) ((L).header E raw mem)) ↔
      ∃! j : CalendarTape.Path (D).format.slot E (Boot.booted V ((A).endAddress v.mesh) mem),
        CalendarTape.encode (D).format.slot E (Boot.booted V ((A).endAddress v.mesh) mem) j=raw :=
  v.tape_admission_at P z width r banks src tbl dst owners fits copiesFit ((A).endAddress v.mesh) le_rfl
    π mem perm raw heap keyEnd cap threshold origin mounted

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
