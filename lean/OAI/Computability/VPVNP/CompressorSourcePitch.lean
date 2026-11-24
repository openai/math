import OAI.Computability.VPVNP.CompressorSourceLaunch

/-! # Preservation of the online calendar's level stride -/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SourceOnline

open BurstRAM DescriptorSpace BlockPlanner Schedule SourceTransport
open scoped Fin.CommRing
open private field_addresses from OAI.Computability.VPVNP.CompressorScriptSnapshot

variable {w : ℕ} (A : Script) (L : Layout) (base : Word w)
local notation "g" => arity A.catalog
local notation "pt" => Workspace.ports (arity A.catalog) base
local notation "H" => levelStart L 0

/-- The pitch word is strictly above the complete active frame and below
every directory row. A source packet writing in the data suffix also leaves
it untouched. All five parts of the actual packet preserve its value. -/
theorem pitch_packet (hg : g = L.shape.arity) (hb : base.val = L.base) (fit : H < 2^w)
    (v : Visit A w) (m : Memory w) (rs : List (Report w))
    (room : (m (pt).ordinal.val).val < directoryRows L) (writes : Writes (H ≤ ·) (eventLog rs)) :
    (Online.post A.catalog A.size pt (v.row pt m rs)) ((pt).directory-1).val = m ((pt).directory-1).val := by
  let gap := ((pt).directory-1).val
  have top : H = L.base+(11+g)+directoryRows L*(g+3) := by
    rw [hg]
    simp only [levelStart,levelsBase,directoryBase,plannerTag,frameBase,Nat.zero_mul,Nat.add_zero]
    omega
  have dirRoom : base.val+(11+g) < 2^w := by omega
  obtain ⟨tagAddr,ordAddr,_,dirAddr,frameAddr⟩ := field_addresses g base dirRoom
  have gapVal : gap = base.val+(10+g) := by
    have one : (1 : Word w).val = 1 := by
      change 1 % 2^w = 1
      exact Nat.mod_eq_of_lt (by omega)
    have lo : (1 : Word w) ≤ (pt).directory := Fin.le_def.mpr (by rw [one,dirAddr]; omega)
    rw [show gap = ((pt).directory-1).val from rfl, Fin.sub_val_of_le lo,dirAddr,one]
    omega
  have tagNe : gap ≠ (pt).tag.val := by omega
  have ordNe : gap ≠ (pt).ordinal.val := by omega
  have frameNe (i : Fin (g+1)) : gap ≠ ((pt).activeFrame+(i.val : Word w)).val := by
    have := frameAddr i
    have := i.isLt
    omega
  let j := v.phase
  let pre := Online.calendarMemory (d := A.size) pt m j
  have preGap : pre gap = m gap := ite_eq_right tagNe
  have preOrd : pre (pt).ordinal.val = m (pt).ordinal.val := ite_eq_right (by omega)
  have offset : (pt).directory.val+(pre (pt).ordinal.val).val*(g+3) < H := by
    rw [preOrd,top,dirAddr,hb]
    exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right room (by omega)) _
  have rowVal := Directory.rowBase_val A.catalog pt pre (offset.trans fit)
  have before : gap < (Controller.rowBase g (pt).data pre).val := by
    change gap < (Directory.rowBase A.catalog pt pre).val
    rw [rowVal,dirAddr,gapVal]
    omega
  let s := LevelCalendar.header (Online.calendar A.plan) (pt).data m
  let R := (A.phase j).recipe
  have bound := OnlineFootprint.row_bound A L base hg hb fit pre (preOrd ▸ room)
  have preserved := RowRecipe.row_outside R (pt).data s pre
    (by rw [PhaseRecipe.recipe_address]; exact bound.trans fit.le) gap
    (.inl (by rw [PhaseRecipe.recipe_address]; exact before))
  rw [RowRecipe.after_row] at preserved
  have input : Online.rowInput A.plan pt m j gap = m gap := by
    change writeMemory (Greedy.writeRow pre (R.address (pt).data s pre) (R.words (pt).data s pre)) (pt).tag 0 gap = _
    rw [writeMemory,ite_eq_right tagNe,preserved,preGap]
  have prep : Directory.prepared A.catalog pt (Online.rowInput A.plan pt m j) gap = m gap :=
    (Controller.after_row_outside g (pt).data _ gap ordNe tagNe frameNe).trans input
  have source := after_outside (Directory.prepared A.catalog pt (Online.rowInput A.plan pt m j))
    writes (i := gap) (by omega)
  change writeMemory (after (Directory.prepared A.catalog pt (Online.rowInput A.plan pt m j)) (eventLog rs))
    (pt).tag _ gap = m gap
  rw [writeMemory,ite_eq_right tagNe,source,prep]

end CompressorRecords.SourceOnline

end VPVNP
end Computability
end OAI
