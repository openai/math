import OAI.Computability.VPVNP.CompressorResidentNativeWalk
import OAI.Computability.VPVNP.CompressorBlockCapacity
import OAI.Computability.VPVNP.CompressorWindowPackets

/-! # Persistent inputs and succeeding level fields after the resident group

The six publications target offsets 30 through 35. The data workers
target only table five. The current scalar inputs, both sets of incidence
heads, all six old table heads, and all of table zero retain their values.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkResidentPackets

open Compression BurstRAM BlockPlanner DescriptorSpace SourceTransport
open ShrinkResidentLayout
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
  {g w : ℕ} (X : State (ShrinkBlockInputs.a i) (packingLaneBits (ShrinkBlockInputs.a i) g))
variable (base : Word w) (positions blocks : ℕ)
local notation "A" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "pt" => Workspace.ports (Schedule.arity (BlockPlanner.Script.catalog A)) base

/-- The resident group preserves the row and pitch words, old header fields outside its six
publications, incidence and table heads, table zero, and all addresses from the next level
onward. -/
structure PhysicalFrame (old : Fin (L).levels) (m out : Memory w) : Prop where
  rows : out (pt).rows.val = m (pt).rows.val
  pitch : out ((pt).directory-1).val = m ((pt).directory-1).val
  scalar (j : ℕ) (low : j < 30) : out (levelStart L old+j) = m (levelStart L old+j)
  higher (j : ℕ) (lo : 36 ≤ j) (hi : j < 66) : out (levelStart L old+j) = m (levelStart L old+j)
  incidence (c : Fin 6) : out (incidenceHead L old c) = m (incidenceHead L old c)
  tables (a : Fin 6) : out (tableHead L old a) = m (tableHead L old a)
  tableZero (x : ℕ) (lo : tableBase L old (0 : Fin 6) ≤ x)
    (hi : x < tableBase L old (0 : Fin 6)+tableWords L) : out x = m x
  next (x : ℕ) (lo : levelStart L (old.val+1) ≤ x) : out x = m x

/-- The finite header and table readbacks follow from the exact footprint of
the physical group and the capacity of table five. -/
theorem physical_frame (old : Fin (L).levels) (size : X.positions ≤ positions) (room : endAddress L < 2^w)
    (abs role : Word w) (side : Bool) (m out : Memory w)
    (keep : ∀ x, ¬ Mutable (values (plan B i) X (tableBase L old (5 : Fin 6)) (levelStart L old) abs role side) x →
      out x = m x) : PhysicalFrame B base positions blocks old m out := by
  let header := levelStart L old
  let start := tableBase L old (0 : Fin 6)
  let first := tableBase L old (5 : Fin 6)
  let D := values (plan B i) X first header abs role side
  have cap : X.positions*ShrinkLevelSpace.tableFactor S ≤ tableWords L := by
    change _ ≤ positions*(BlockProgram.allocationShape B).slots*(BlockProgram.allocationShape B).fields
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul size (BlockProgram.field_rates B base.val positions blocks).1
  have endData : (layout X first).endAddr ≤ levelStart L (old.val+1) :=
    (ShrinkLevelSpace.resident_table S i X start first w).2.trans
      ((Nat.add_le_add_left cap _).trans (tableEnd_le_nextLevel L old (5 : Fin 6)))
  have headLow : levelStart L 0 ≤ header := levelStart_mono L (Nat.zero_le _)
  have firstArray : header+66 ≤ start := by
    change header+66 ≤ header+66+6*slotCapacity L+0*tableWords L
    omega
  have order : start+tableWords L ≤ first := tableEnd_le_tableBase L old (a := (0 : Fin 6)) (b := (5 : Fin 6)) (by decide : (0 : Fin 6)<5)
  have dataNext := (layout X first).ranges false
  obtain ⟨b,c,r,e⟩ := dataNext
  change first ≤ (layout X first).owner false at b
  have cells := Window.lowCells («A» := BlockProgram.script B) L base (BlockProgram.layout_arity B ..).symm rfl
    ((levelStart_mono L (Nat.zero_le (L).levels)).trans_lt room)
  have early (x : ℕ) (h : x < first) (d : x < header+30 ∨ header+36 ≤ x) : out x = m x := by
    apply keep
    rintro (hw|hh)
    · exact (Nat.not_le_of_gt h) hw.1
    · change header+30 ≤ x ∧ x < header+36 at hh
      omega
  refine ⟨early _ (by have := cells.1; omega) (.inl (by have := cells.1; omega)),
    early _ (by have := cells.2; omega) (.inl (by have := cells.2; omega)),
    fun j hj => early _ (by omega) (.inl (by omega)),fun j lo hi => early _ (by omega) (.inr (by omega)),
    ?_,?_,fun x lo hi => early x (hi.trans_le order) (.inr (by omega)),?_⟩
  · intro c
    change out (header+54+c.val) = m (header+54+c.val)
    exact early _ (by have := c.isLt; omega) (.inr (by omega))
  · intro a
    change out (header+54+6+a.val) = m (header+54+6+a.val)
    exact early _ (by have := a.isLt; omega) (.inr (by omega))
  · intro x lo
    apply keep
    rintro (hw|hh)
    · change first ≤ x ∧ x < (layout X first).endAddr at hw
      omega
    · change header+30 ≤ x ∧ x < header+36 at hh
      omega

end CompressorRecords.ShrinkResidentPackets

end

end VPVNP
end Computability
end OAI
