import OAI.Computability.VPVNP.PairVertexLevelLocator
import OAI.Computability.VPVNP.PairSimulationTerminalSplice

/-! # Read footprint of the traversal-level locator -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexLevel

open BurstRAM CompressorRecords TraversalControllerInputs TraversalRoles
open scoped Fin.CommRing

variable {w : ℕ} {pub : Fin 11 → Word w} {m : Memory w}

private theorem boot_reads {data : ℕ → Prop}
    (safe : ∀ i ∈ ({1, 15, 16, 17} : Finset ℕ), data (terminalHead pub + (i : Word w)).val) :
    SourceTransport.Reads data (bootEvents pub m) := by
  intro a v h
  simp only [bootEvents, List.mem_append, List.mem_replicate, List.mem_cons, List.not_mem_nil,
    reduceCtorEq, Event.read.injEq, and_false, false_or, or_false] at h
  rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact safe 16 (by decide)
  · exact safe 17 (by decide)
  · exact safe 15 (by decide)
  · exact safe 1 (by decide)

private theorem scan_reads (j later : ℕ) {data : ℕ → Prop}
    (safe : ∀ i, j ≤ i → i ≤ j + later → data (levelHead pub m i + 14).val) :
    SourceTransport.Reads data (scanEvents pub m j later) := by
  induction later with
  | zero =>
    intro a v h
    simp only [scanEvents, testEvents, List.mem_cons, List.not_mem_nil, reduceCtorEq,
      Event.read.injEq, false_or, or_false] at h
    exact h.1 ▸ safe j le_rfl le_rfl
  | succ n ih =>
    intro a v h
    simp only [scanEvents, testEvents, List.mem_append, List.mem_cons, List.not_mem_nil,
      reduceCtorEq, Event.read.injEq, false_or, or_false] at h
    rcases h with ⟨rfl, _⟩ | h
    · exact safe (j + n + 1) (by omega) (by omega)
    · exact ih (fun i hlo hhi => safe i hlo (by omega)) a v h

/-- The boot reads four terminal fields. Each tested level contributes a
read of its start cell at offset 14, and the arithmetic exit has no reads. -/
theorem trace_reads (j later : ℕ) {data : ℕ → Prop}
    (terminal : ∀ i ∈ ({1, 15, 16, 17} : Finset ℕ), data (terminalHead pub + (i : Word w)).val)
    (levels : ∀ i, j ≤ i → i ≤ j + later → data (levelHead pub m i + 14).val) :
    SourceTransport.Reads data (trace pub m j later) := by
  intro a v h
  simp only [trace, List.mem_append, List.mem_replicate, reduceCtorEq, and_false, or_false] at h
  exact h.elim (boot_reads terminal a v) (scan_reads j later levels a v)

/-- All reads avoid the terminal control cells at offsets 0 and 31.
The level scalars precede the terminal header, and their word addresses
agree with the natural addresses of their published fields. -/
theorem trace_worker_reads {H first pitch offset cap base : ℕ} {old : TaggedLayer}
    {ls : List (Fiber w)} (d : Resident pub m H first pitch offset cap base old ls)
    (beforeH : ∀ i ≤ ls.length, first + i * pitch + 28 ≤ H)
    (j later : ℕ) (live : j + later ≤ ls.length) :
    SourceTransport.Reads (TerminalLink.workerCell (TerminalLink.header pub))
      (trace pub m j later) := by
  have head : TerminalLink.header pub = (H : Word w) := d.header
  have fit := d.headerFits
  have headVal : (TerminalLink.header pub).val = H := by
    rw [head, Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have lastVal : (TerminalLink.header pub + 31).val = H + 31 := by
    rw [head, show (31 : Word w) = ((31 : ℕ) : Word w) from rfl, ← Nat.cast_add,
      Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
  apply trace_reads
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [TerminalLink.workerCell, headVal, lastVal, d.header, ← Nat.cast_add,
      Fin.val_natCast, Nat.mod_eq_of_lt (show H + i < 2 ^ w by omega)]
    omega
  · intro i _ hi
    have hl := hi.trans live
    have hb := beforeH i hl
    have addr : (levelHead pub m i + 14).val = first + i * pitch + 14 := by
      rw [levelHead, terminal_read d 16 (by decide), terminal_read d 17 (by decide),
        d.firstHead, d.levelPitch, show (14 : Word w) = ((14 : ℕ) : Word w) from rfl,
        ← Nat.cast_mul, ← Nat.cast_add, ← Nat.cast_add, Fin.val_natCast,
        Nat.mod_eq_of_lt (by omega)]
    simp only [TerminalLink.workerCell, headVal, lastVal, addr]
    omega

end PairSimulation.VertexLevel

end VPVNP
end Computability
end OAI
