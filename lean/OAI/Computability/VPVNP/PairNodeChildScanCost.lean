import OAI.Computability.VPVNP.PairNodeChildScan
import OAI.Computability.VPVNP.RAMProcessorReportPrefix
import OAI.Computability.VPVNP.PrimedInputRAMFlowEval

/-!
# Work of the child argument scan

Every old port requires one width probe. Each incoming port also requires
one inverse-incidence probe. Each guessed bit uses six local instructions.
The row scan adds one descriptor probe and ten instructions per child and
two final exit instructions, including for an empty row.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NodeArguments.ChildScan

open BurstRAM BurstRAM.PrivateRAM Compression CompressorRecords
open PrimedInputRAM.Flow (choiceBits_append)

variable {w a g : ℕ} (X : State a g) (T : IncidenceDirectory w) (m : Memory w)

private def slotProbes {n : ℕ} (i : Bool × Fin n) : ℕ := if i.1 then 2 else 1
private def slotWork {n : ℕ} (i : Bool × Fin n) : ℕ := if i.1 then 8 else 7

private theorem slots_cost (x : Child X) (slots : List (Bool × Fin (2 ^ a))) :
    let es := ChildSlots.events X x.site T m x.data slots
    let bs := ChildSlots.bits X x.site x.data slots
    choiceBits es = bs ∧ countProbes es = (slots.map slotProbes).sum ∧
      es.length = (slots.map slotWork).sum + 6 * bs.length := by
  induction slots with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons i slots ih =>
    have hdr := FieldGuess.header_cost T m i.1 (IncidenceDirectory.actualPort X (x.site, i.2))
    have guess := PrivateFields.events_work (w := w) .guess (List.ofFn (x.data i))
    have bits := PrivateFields.events_bits (w := w) .guess (List.ofFn (x.data i))
    simp only [ChildSlots.events, ChildSlots.bits, List.flatMap_cons, choiceBits_append,
      BurstRAM.countProbes_append, List.length_append, List.map_cons, List.sum_cons,
      hdr.2.2, hdr.1, hdr.2.1, guess.2, guess.1, bits, List.length_cons,
      List.length_nil] at *
    change _ = _ ∧ _ = _ ∧ _ = _
    obtain ⟨ihb, ihp, ihw⟩ := ih
    rw [ihb, ihp, ihw]
    by_cases hi : i.1 = true <;> simp [choiceBits, countProbes, slotProbes, slotWork, hi] <;> omega

private theorem one_cost (src : ℕ) (x : Child X) :
    let es := childEvents X T m src x
    choiceBits es = x.payload X ∧ countProbes es = 1 + 3 * 2 ^ a ∧
      es.length = 10 + 15 * 2 ^ a + 6 * (x.payload X).length := by
  have h := slots_cost X T m x (ChildSlots.slots (2 ^ a))
  have p : ((ChildSlots.slots (2 ^ a)).map slotProbes).sum = 3 * 2 ^ a := by
    simp [ChildSlots.slots, List.map_ofFn, Function.comp_def, slotProbes]
    omega
  have v : ((ChildSlots.slots (2 ^ a)).map slotWork).sum = 15 * 2 ^ a := by
    simp [ChildSlots.slots, List.map_ofFn, Function.comp_def, slotWork]
    omega
  have setup : choiceBits (setupEvents m src) = [] ∧ countProbes (setupEvents m src) = 1 ∧
      (setupEvents m src).length = 10 := ⟨rfl, rfl, rfl⟩
  simp only [childEvents, choiceBits_append, BurstRAM.countProbes_append, List.length_append,
    setup.1, setup.2.1, setup.2.2, List.nil_append, h.1, h.2.1, h.2.2, p, v, Child.payload,
    Nat.add_assoc, and_self]

/-- Exact guessed bits, probes, and instructions of the native scan. These
counts include the exit after the last child. -/
theorem events_cost (src : ℕ) (xs : List (Child X)) :
    let es := events X T m src xs
    let bs := xs.flatMap (Child.payload X)
    choiceBits es = bs ∧ countProbes es = (1 + 3 * 2 ^ a) * xs.length ∧
      es.length = (10 + 15 * 2 ^ a) * xs.length + 6 * bs.length + 2 := by
  induction xs generalizing src with
  | nil => exact ⟨rfl, by simp [events, countProbes], by simp [events]⟩
  | cons x xs ih =>
    have h := one_cost X T m src x
    obtain ⟨hb, hp, hw⟩ := ih (src + 1)
    simp only [events, List.flatMap_cons, choiceBits_append, BurstRAM.countProbes_append,
      List.length_append, List.length_cons, h.1, h.2.1, h.2.2, hb, hp, hw, Nat.mul_add, Nat.mul_one]
    exact ⟨trivial, by omega, by omega⟩

end PairSimulation.NodeArguments.ChildScan

end VPVNP
end Computability
end OAI
