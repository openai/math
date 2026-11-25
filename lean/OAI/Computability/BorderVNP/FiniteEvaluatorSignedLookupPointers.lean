import OAI.Computability.BorderVNP.FiniteEvaluatorSignedCubeAllocation
import OAI.Computability.BorderVNP.CubeScatterReturnedOwnedDeck

/-! # Lookup pointers decoded from the signed task extension

The ordinary boot installs the allocated lookup arrays and the fixed cube deck
operands at their addressed frame positions. The end of the allocation bounds
the addresses and both dimensions of the fixed recipe.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open DiagonalTallyPacketEmit

/-- A pass preserving the five lookup words preserves the allocated lookup pointers. -/
theorem LookupPointers.transfer {f : Frame} {dst base : ℕ} {m m' : ℕ → ℕ}
    (ptr : LookupPointers f dst base m)
    (keep : ∀ j ∈ [45, 71, 80, 83, 84], m' (base + j) = m (base + j)) :
    LookupPointers f dst base m' :=
  ⟨(keep 45 (by decide)).trans ptr.descriptors, (keep 71 (by decide)).trans ptr.destination,
    (keep 80 (by decide)).trans ptr.references, (keep 83 (by decide)).trans ptr.width,
    (keep 84 (by decide)).trans ptr.vertices⟩

end TeamContraction

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Tally DiagonalTallyPacketEmit
open DiagonalTallyAllocation TeamContraction
open private lookup_order from OAI.Computability.BorderVNP.FiniteEvaluatorSignedCubeAllocation

variable {w : ℕ} (l : Layout)

local notation "digits" => argumentWidth l.cube.n l.cube.b l.cube.h l.cube.K l.cube.s
local notation "idBase" => CubeConstants.idBase l.cube.stop l.cube.n l.cube.b l.cube.h l.cube.K
  l.cube.s

private theorem deck_room (room : l.after.packed ≤ 2 ^ w) :
    idBase + 2 ^ digits < 2 ^ w := by
  obtain ⟨_, _, _, _, _, before, after⟩ := lookup_order l
  have h : l.after.lookupRows < l.after.packed := by
    dsimp only [AfterTasks.packed, AfterTasks.ids, AfterTasks.lookupRefs]
    omega
  have deck := (before.trans after).trans_lt (h.trans_le room)
  simpa only [CubeConstants.arenaEnd, CubeConstants.ids, List.length_ofFn] using deck

private theorem read_field (frame raw team subtotal : ℕ) (mem : Memory w)
    (old : Fin 81 → Word w) (i : Fin 81) {value : ℕ}
    (encoded : (l.extension raw team subtotal old i).val = value % (2 ^ w))
    (fit : value < 2 ^ w) :
    readings (ExtendedFrame.installed mem frame (l.extension raw team subtotal old))
      (frame + (31 + i.val)) = value := by
  rw [← Nat.add_assoc, readings, ExtendedFrame.installed_at, encoded, Nat.mod_eq_of_lt fit]

/-- The ordinary extension supplies the actual descriptor, destination and reference
bases and the two finite lookup dimensions, for every choice of untouched frame words. -/
theorem Layout.lookupPointers_at_boot (count frame raw team subtotal : ℕ) (mem : Memory w)
    (old : Fin 81 → Word w) (room : l.after.packed ≤ 2 ^ w) :
    LookupPointers (l.lookupFrame count) l.after.ids frame
      (readings (ExtendedFrame.installed mem frame (l.extension raw team subtotal old))) := by
  have ids : l.after.ids < 2 ^ w := by
    dsimp only [AfterTasks.packed] at room
    omega
  have refs : l.after.lookupRefs < 2 ^ w := (Nat.le_add_right ..).trans_lt ids
  have rows : l.after.lookupRows < 2 ^ w := (Nat.le_add_right ..).trans_lt refs
  have bound : 2 ^ digits < 2 ^ w := (Nat.le_add_left ..).trans_lt (deck_room l room)
  have width : digits < 2 ^ w := Nat.lt_two_pow_self.trans bound
  have vertex : Fintype.card (Vertex (l.cube.n + 1)) < 2 ^ w :=
    (Nat.le_pow_clog (by decide) _).trans_lt ((Nat.pow_le_pow_right (by decide : 0 < 2)
      (show Nat.clog 2 (Fintype.card (Vertex (l.cube.n + 1))) ≤ digits by
        unfold argumentWidth
        omega)).trans_lt bound)
  exact ⟨read_field l frame raw team subtotal mem old 14 rfl rows,
    read_field l frame raw team subtotal mem old 40 rfl ids,
    read_field l frame raw team subtotal mem old 49 rfl refs,
    read_field l frame raw team subtotal mem old 52 (Nat.mod_mod ..) width,
    read_field l frame raw team subtotal mem old 53 (Nat.mod_mod ..) vertex⟩

/-- The same extension supplies the four input pointers used by the native
constant installer for the fixed field deck. -/
theorem Layout.constantFields_at_boot (template : Frame) (frame raw team subtotal : ℕ)
    (mem : Memory w) (old : Fin 81 → Word w) (room : l.after.packed ≤ 2 ^ w) :
    CubeConstants.Fields
      (CubeConstants.inArena template l.cube.stop l.cube.n l.cube.b l.cube.h l.cube.K l.cube.s)
      frame idBase
      (readings (ExtendedFrame.installed mem frame (l.extension raw team subtotal old))) := by
  have deck := deck_room l room
  have base : idBase < 2 ^ w := (Nat.le_add_right ..).trans_lt deck
  have lo : l.cube.stop + 2 ≤ idBase := Nat.le_add_right ..
  dsimp only [CubeConstants.Fields, CubeConstants.inArena]
  exact ⟨read_field l frame raw team subtotal mem old 50 (Nat.mod_mod ..) (by omega),
    read_field l frame raw team subtotal mem old 51 (Nat.mod_mod ..) (by omega),
    read_field l frame raw team subtotal mem old 48 (Nat.mod_mod ..) (by omega),
    read_field l frame raw team subtotal mem old 16 (Nat.mod_mod ..) base⟩

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
