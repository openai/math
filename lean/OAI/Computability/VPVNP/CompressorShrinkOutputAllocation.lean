import OAI.Computability.VPVNP.CompressorShrinkSelectedSlices
import OAI.Computability.VPVNP.CompressorSlotBuild

/-! # Allocation of a selected shrinking pass

Place the surviving width rectangle beyond the current role table, term
rows and retained directories. Dense interval records follow that rectangle.
The slot constructor then uses fresh consecutive heads for roles, cyclic
successors, subdivision counts and the ordered-slot workspace.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkOutput

open Compression Compression.PackingData Compression.ShrinkMotif Compression.ShrinkEnergy
open MotifBlocks MotifGrid MotifConversion SlotLevel ShrinkSlots
open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM ShrinkSliceSweep

variable {a b g w : ℕ} (X : State a (packingLaneBits a g))

/-- Number of motif descriptors in the shrinking output allocation, one per numbered piece of
each packed-site bundle. -/
abbrev motifCount := ((Fintype.card X.Base*(2^(Shrink.J a)*2^g))*2^a)*pieceCount (2^a) (Shrink.colors a)
/-- Number of old arcs in absolute role-table order, used to size the four-word role records. -/
abbrev absoluteCount := DemandRAM.absoluteCount X

/-- First address available for surviving width data, taken after the term rows, old-arc role
records and all retained directories. -/
def widthBase (term stride role retained : ℕ) :=
  max (term+motifCount X*stride) (max (role+4*absoluteCount X) retained)

/-- Start of the ordered-slot allocation after reserving the surviving width rectangle and the
per-motif interval records for every subdivision. -/
def slotsBase (width : ℕ) (s : Shape) :=
  let sum := ∑ i, s.subdivisions i
  width+(absoluteCount X*4)*sum+(motifCount X*4)*(5+7*sum)

/-- Place the role, next-site, subdivision and scratch tables for slot construction from the
given start, using the existing old-arc role records. -/
def heads (s : Shape) (role start : ℕ) : Heads :=
  ⟨role,start,start+8+sites s,start+8,start+8+sites s+4⟩

/-- Compute the slot-constructor table bases for this level after allocating its surviving
width and interval records. -/
def slotHeads (term stride role retained : ℕ) :=
  let s := levelShape (b := b) X
  heads s role (slotsBase X (widthBase X term stride role retained) s)

/-- Exclusive end of the shrinking output allocation, including the slot constructor's
workspace at this level. -/
def stop (term stride role retained : ℕ) :=
  finish (levelShape (b := b) X) (slotHeads (b := b) X term stride role retained)

private theorem scratch_le_finish (s : Shape) (h : Heads) : h.scratch ≤ finish s h := by
  unfold finish widthHead inHead outHead inverseBaseHead stopAddress shiftsHead targetsHead inverseHead rowsHead
  omega

variable {k : Type*} [_root_.Field k] {factor δ : ℝ}
variable (F : FixedBlock k demandSource demandTarget supply (realWidths demandMass) (realWidths supplyMass) (31/16) factor)
variable (sel : X.ShrinkSelection F) (term : Word w) (stride role retained : ℕ)

/-- Allocate the selected term's surviving widths and slice records using its actual
subdivision counts and the space after the retained data. -/
abbrev splitBank :=
  selectedAllocation F X sel term stride (widthBase X term.val stride role retained) (levelShape (b := b) X).subdivisions

theorem splitBank_last :
    (splitBank (b := b) X F sel term stride role retained).last =
      (slotHeads (b := b) X term.val stride role retained).role := rfl

theorem width_le_slots :
    widthBase X term.val stride role retained ≤ (slotHeads (b := b) X term.val stride role retained).role :=
  (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)

theorem slots_le_stop :
    (slotHeads (b := b) X term.val stride role retained).role ≤ stop (b := b) X term.val stride role retained := by
  let s := levelShape (b := b) X
  let h := slotHeads (b := b) X term.val stride role retained
  have he : h.scratch = h.role+8+sites s+4 := rfl
  exact (by omega : h.role ≤ h.scratch).trans (scratch_le_finish s h)

theorem fits (ready : Ready (2^a) (2*2^a+1) (2^b) δ) (wide : 10 ≤ stride)
    (room : stop (b := b) X term.val stride role retained < 2^w) :
    (splitBank (b := b) X F sel term stride role retained).Fits := by
  let h := slotHeads (b := b) X term.val stride role retained
  have hstop := scratch_le_finish (levelShape (b := b) X) h
  have he : h.scratch = h.role+8+sites (levelShape (b := b) X)+4 := rfl
  change finish _ h < 2^w at room
  refine ⟨wide,le_max_left ..,ready.count_pos,(slots_le_stop X term stride role retained).trans_lt room,?_⟩
  omega

theorem role_room : role + 4*absoluteCount X ≤ widthBase X term.val stride role retained :=
  (le_max_left ..).trans (le_max_right ..)

theorem retained_room : retained ≤ widthBase X term.val stride role retained :=
  (le_max_right ..).trans (le_max_right ..)

end CompressorRecords.ShrinkOutput

end

end VPVNP
end Computability
end OAI
