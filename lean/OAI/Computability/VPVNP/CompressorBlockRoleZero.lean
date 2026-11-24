import OAI.Computability.VPVNP.CompressorRecordsBlockPlanner
import OAI.Computability.VPVNP.CompressorRecordsShrinkFrame

/-!
# Publishing the initial cursor role

The fourth initial visit writes the cursor role at scalar offset 27. Its
worker receives the two operands computed by the planner. The six packed
incidence columns begin after the level header, so their typed readback
survives the role write.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BlockRoleZero

open BurstRAM BurstRAM.PrivateRAM Compression DescriptorSpace BlockPlanner PhaseRecipe IncidenceDirectory
open scoped Fin.CommRing

variable {w a l : ℕ}

/-- The level-zero visit that stores the cursor role tag at header offset 27. -/
def visit := BlockPlanner.publish (LevelFields.address 0 27) (.lit 0)

/-- Machine-word address of the initial level's role tag. -/
def role (w : ℕ) (L : DescriptorSpace.Layout) : Word w := ((levelStart L 0+27 : ℕ) : Word w)

/-- The initial role writer's report, storing zero at the role address and returning cursor
one. -/
def report (w : ℕ) (L : DescriptorSpace.Layout) : Report w :=
  ⟨[.tick,.tick,.tick,.write (role w L) 0,.tick,.tick],some 1⟩

/-- The operands are evaluated at the first level header; the worker enters
at its own initial cursor zero and returns cursor one. -/
theorem run (L : DescriptorSpace.Layout) (pub : Fin 5 → Word w) (m : Memory w) :
    let header := ((levelStart L 0 : ℕ) : Word w)
    let ports : Fin 2 → Word w := fun j ↦ (visit.params j).eval pub header m
    let P := (visit.worker.table.instantiate w ports).program
    visit.initial.eval pub header m = 0 ∧ visit.stop.eval pub header m = 1 ∧
      execute P 7 (P.start 0) m [] = some (report w L) ∧
      after m (report w L).events = writeMemory m (role w L) 0 ∧ (report w L).probes = 1 ∧
      choiceBits (report w L).events = [] ∧ ∀ x v, Event.read x v ∉ (report w L).events := by
  intro header ports P
  have dest : ports 0 = role w L := by
    change header + (0 : Word w) * LevelFields.stride.eval pub header m + (27 : Word w) = _
    simp [header,role]
  have zero : ports 1 = 0 := rfl
  obtain ⟨exec,_,_,_⟩ := BlockPlanner.publish_native (LevelFields.address 0 27) (.lit 0) ports 0 m
  refine ⟨rfl,rfl,?_,rfl,rfl,rfl,?_⟩
  · change execute ((BlockPlanner.publish (LevelFields.address 0 27) (.lit 0)).worker.table.instantiate w ports).program 7
      (((BlockPlanner.publish (LevelFields.address 0 27) (.lit 0)).worker.table.instantiate w ports).program.start 0) m [] = _
    rw [exec, dest, zero, zero_add]; rfl
  · intro x v
    simp [report]

/-- The header write preserves all six base and actual incidence columns.
The column stride may exceed the exact slot count of the represented state. -/
theorem preserve (L : DescriptorSpace.Layout) (X : State a l) (rows : ℕ) (m : Memory w)
    (rep : (packedIncidence L w 0 rows).Represents X m)
    (fits : IncidenceDirectory.slotCount X ≤ rows)
    (room : incidenceStart L 0 + 6*rows ≤ 2^w)
    (before : levelStart L 0+27 < incidenceStart L 0) :
    (packedIncidence L w 0 rows).Represents X (after m (report w L).events) := by
  let T := packedIncidence L w 0 rows
  have roleVal : (role w L).val = levelStart L 0+27 := Nat.mod_eq_of_lt (by omega)
  have keep (c : Fin 6) (v : Word w) (hv : v.val < IncidenceDirectory.slotCount X) :
      after m (report w L).events (T.column c+v).val = m (T.column c+v).val := by
    have hc := Nat.mul_le_mul_right rows c.isLt
    rw [Nat.succ_mul] at hc
    have top : incidenceBase L 0 rows c+v.val < 2^w := by unfold incidenceBase; omega
    have val : (T.column c+v).val = incidenceBase L 0 rows c+v.val := by
      rw [show T.column c = CursorRAM.encode w (incidenceBase L 0 rows c) from packed_column ..,
        Fin.val_add, show (CursorRAM.encode w (incidenceBase L 0 rows c)).val = incidenceBase L 0 rows c
          from Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt top]
    change writeMemory m (role w L) 0 _ = _
    rw [val, writeMemory, ite_eq_right]
    unfold incidenceBase
    omega
  have base (c : Fin 6) (e : X.Base × Fin (2^a)) := keep c (basePort X e) (basePort_lt X e)
  have actual (c : Fin 6) (e : (X.Base × BitWord l) × Fin (2^a)) := keep c (actualPort X e) (actualPort_lt X e)
  exact ⟨fun e ↦ (base 0 e).trans (rep.baseOut e),fun e ↦ (base 1 e).trans (rep.baseIn e),
    fun e ↦ (base 2 e).trans (rep.shift e),fun e ↦ (actual 3 e).trans (rep.actualOut e),
    fun e ↦ (actual 4 e).trans (rep.actualIn e),fun e ↦ (actual 5 e).trans (rep.width e)⟩

/-- In a physical level-zero allocation the slot-capacity and exclusive
end-address bounds imply the column room required by the frame proof. -/
theorem preserve_allocated (L : DescriptorSpace.Layout) (X : State a l) (m : Memory w)
    (hl : 0 < L.levels) (scalars : 28 ≤ L.shape.scalarFields) (fit : endAddress L < 2^w)
    (slots : IncidenceDirectory.slotCount X ≤ slotCapacity L)
    (rep : (packedIncidence L w 0 (IncidenceDirectory.slotCount X)).Represents X m) :
    (packedIncidence L w 0 (IncidenceDirectory.slotCount X)).Represents X (after m (report w L).events) :=
  preserve L X _ m rep le_rfl (packed_incidence_room L fit ⟨0,hl⟩ slots).le
    (by unfold incidenceStart levelHeaderWords; omega)

end CompressorRecords.BlockRoleZero

end VPVNP
end Computability
end OAI
