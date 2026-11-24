import OAI.Computability.VPVNP.PairShrinkHiddenInputs
import OAI.Computability.VPVNP.CompressorRegisterSetupTrace

/-!
# External addresses read by the absorbed-field scan

The setup reads five cells in the old-level header. The loop reads the
owner count, one dense ID per field, and the repetition and payload cells
of the selected term. The private guesses perform no external accesses.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkHiddenGuess

open BurstRAM PrivateRAM CompressorRecords PhaseRecipe SourceTransport
open scoped Fin.CommRing
open private headEvents from OAI.Computability.VPVNP.PairSimulationPrivateFields
open private reads_append from OAI.Computability.VPVNP.CompressorFormulaFootprint

variable {W p r : ℕ}

/-- All chronological header probes belong to the five selected cells. -/
theorem Header.trace_reads (D : ℕ → Prop) (s t : ℕ) (inputs : Fin 6 → Fin r)
    (vm : Fin (RegisterSetup.regCount (Header.recipe s t)) ↪ Fin r)
    (c : Config W p r) (m : Memory W) (oldLevel : ℕ)
    (level : c.reg (inputs 5) = (oldLevel : Word W)) (fit : oldLevel+38 < 2^W)
    (allowed : ∀ j ∈ ([31,32,36,37,38] : List ℕ), D (oldLevel+j)) :
    Reads D (Header.trace s t inputs vm c m) := by
  apply RegisterSetup.lines_reads
  intro i
  let pub := fun j : Fin 5 => c.reg (inputs j.castSucc)
  let state := c.reg (inputs (Fin.last 5))
  have head (j : ℕ) (hj : j ∈ ([31,32,36,37,38] : List ℕ)) :
      (Expr.header j).ReadsFrom D pub state m := by
    have lim : j ≤ 38 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; omega
    refine ⟨⟨trivial,trivial⟩,?_⟩
    change D ((c.reg (inputs 5))+(j : Word W)).val
    rw [level,← Nat.cast_add,Fin.val_cast_of_lt (by omega : oldLevel+j < 2^W)]
    exact allowed j hj
  fin_cases i <;> first | exact head _ (by decide) | trivial

private theorem private_reads (D : ℕ → Prop) (bs : List Bool) : Reads D (PrivateFields.events (w := W) .guess bs) := by
  induction bs with
  | nil => simp [PrivateFields.events,Reads]
  | cons b bs ih =>
    apply reads_append _ ih
    simp [headEvents,Reads]

/-- The three addresses of one field's actual external reads. -/
def FieldCells (D : ℕ → Prop) (g : Args W) (m : Memory W) (ptr : ℕ) :=
  let a : Word W := ptr
  let id := m a.val
  let base := ShrinkHiddenWidth.rowBase g.termBase g.termStride id
  let coord := ShrinkHiddenWidth.coordinate (g.layout.toNat : Word W) id
  D a.val ∧ D (base+1).val ∧ D (base+2+coord).val

theorem field_reads (D : ℕ → Prop) (g : Args W) (m : Memory W) (ptr : ℕ) (e : Row)
    (cells : FieldCells D g m ptr) : Reads D (fieldEvents g m ptr e) := by
  apply reads_append _ (private_reads D e.2)
  refine reads_append ?_ ?_
  swap
  · intro a v h; simp at h
  intro a v h
  simp only [Args.header,ShrinkHiddenWidth.events,List.mem_cons,List.not_mem_nil,Event.read.injEq,
    reduceCtorEq,false_or,or_false] at h
  obtain (⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩) := h
  exacts [cells.1,cells.2.1,cells.2.2]

private theorem loop_reads (D : ℕ → Prop) (g : Args W) (m : Memory W) (es : List Row) (ptr : ℕ)
    (cells : ∀ i : Fin es.length, FieldCells D g m (ptr+i.val)) : Reads D (loopEvents g m ptr es) := by
  induction es generalizing ptr with
  | nil => simp [loopEvents,Reads]
  | cons e es ih =>
    apply reads_append _ (ih (ptr+1) fun j => by
      simpa only [Fin.val_succ,← Nat.add_assoc,Nat.add_right_comm] using cells j.succ)
    intro a v h
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,reduceCtorEq,false_or,or_false] at h
    exact field_reads D g m ptr e (by simpa using cells 0) a v h

theorem events_reads (D : ℕ → Prop) (g : Args W) (m : Memory W) (es : List Row)
    (count : D ((g.countBase+g.owner : ℕ) : Word W).val)
    (cells : ∀ i : Fin es.length, FieldCells D g m (g.row+i.val)) : Reads D (events g m es) := by
  apply reads_append _ (loop_reads D g m es g.row cells)
  intro a v h
  simp only [setupEvents,List.mem_cons,List.not_mem_nil,Event.read.injEq,reduceCtorEq,false_or,or_false] at h
  exact h.1 ▸ count

end PairSimulation.ShrinkHiddenGuess

end VPVNP
end Computability
end OAI
