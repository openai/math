import OAI.Computability.VPVNP.PairSimulationMapArgumentWriter
import OAI.Computability.VPVNP.CompressorRegisterSetupClock

/-!
# Canonical event sequence of the map argument writer

The native writer evaluates its expressions using the six live input
words and the external memory. The events are exactly those of the same
expression list evaluated with a zeroed compiler bank, followed by the
private descriptor stores. Thus their order and contents are determined
by the inputs even when the caller's other registers and memory vary.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapArgumentWriter

open BurstRAM BurstRAM.PrivateRAM CompressorRecords CompressorRecords.PhaseRecipe
open scoped Fin.CommRing

variable {n w p r k : ℕ} (base : Expr) (fields : Fin n → Expr)

/-- Every public record read in assignment order followed by the fixed
private-store and cursor instructions. -/
def events (pub : Fin 5 → Word w) (state : Word w) (m : Memory w) : List (Event w) :=
  (RowRecipe.evaluate pub state m (lines base fields) (fun _ ↦ 0)).1 ++
    List.replicate (3 + 2 * n) .tick

/-- Every external read in the writer's canonical trace belongs to the
region certified for its base and field expressions. -/
theorem events_readsFrom (data : ℕ → Prop) (pub : Fin 5 → Word w) (state : Word w) (m : Memory w)
    (baseSafe : base.ReadsFrom data pub state m)
    (fieldSafe : ∀ i, (fields i).ReadsFrom data pub state m) :
    SourceTransport.Reads data (events base fields pub state m) := by
  have allowed (i : Fin (n + 1)) : ((recipes base fields) i).ReadsFrom data pub state m := by
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [recipes, Fin.snoc_last] using baseSafe
    · simpa only [recipes, Fin.snoc_castSucc] using fieldSafe j
  intro a v h
  rcases List.mem_append.mp h with entry | entry
  · exact RegisterSetup.lines_reads (recipes base fields) data pub state m allowed _ a v entry
  · cases List.eq_of_mem_replicate entry

/-- The external memory is read-only during the complete writer, including
the descriptor stores in the private memory. -/
theorem events_noWrites (pub : Fin 5 → Word w) (state : Word w) (m : Memory w) :
    SourceTransport.Writes (fun _ ↦ False) (events base fields pub state m) := by
  have rows {r : ℕ} (ls : List (RowRecipe.Assign r 5)) (rs : PrimedStackRAM.Regs w r) :
      SourceTransport.Writes (fun _ ↦ False) (RowRecipe.evaluate pub state m ls rs).1 := by
    induction ls generalizing rs with
    | nil => simp [SourceTransport.Writes, RowRecipe.evaluate]
    | cons line rest ih =>
      intro a v h
      rcases List.mem_cons.mp h with head | tail
      · cases eq : line.rhs <;> simp [RowRecipe.RHS.event, eq] at head
      · exact ih _ a v tail
  intro a v h
  rcases List.mem_append.mp h with entry | entry
  · exact rows _ _ a v entry
  · cases List.eq_of_mem_replicate entry

variable (vm : Fin (RegisterSetup.regCount (recipes base fields)) ↪ Fin r)
  (inputs : Fin 6 → Fin r) (aux : Fin 3 ↪ Fin r)
  (loc : Address base fields → Fin p) (done : Fin p)

/-- On every caller configuration, the linked writer executes the same
canonical trace for its input words and external records. The output
descriptor and exterior memory frame refer to this very execution. -/
theorem native_exact (M : Machine w p r k) (link : ∀ a,
    M.code (loc a) = (text base fields vm inputs aux loc done a).resize w)
    (safe : ∀ i j, vm i ≠ inputs j) (apart : ∀ i j, vm i ≠ aux j)
    (c : Config w p r) (m : Memory w) (start : c.pc = setupPC base fields loc 0) :
    let pub := fun i : Fin 5 ↦ c.reg (inputs i.castSucc)
    let state := c.reg (inputs (Fin.last 5))
    let addr := base.eval pub state m
    addr.val + n ≤ 2 ^ w →
    let ev := events base fields pub state m
    ∃ out : Config w p r,
      ev.length = clock base fields ∧ countProbes ev = ∑ i, ((recipes base fields) i).loads ∧
      choiceBits ev = [] ∧ out.pc = done ∧ out.reg (aux 0) = addr ∧
      out.persistent = c.persistent ∧
      (∀ i : Fin n, out.privateMem (addr + (i.val : Word w)) = (fields i).eval pub state m) ∧
      (∀ a : Word w, a.val < addr.val ∨ addr.val + n ≤ a.val →
        out.privateMem a = c.privateMem a) ∧
      (∀ j, (∀ i, j ≠ vm i) → (∀ i, j ≠ aux i) → out.reg j = c.reg j) ∧
      ∀ fuel bs, execute M.program (fuel + ev.length) c m bs =
        (execute M.program fuel out m bs).map (fun rep ↦ ⟨ev ++ rep.events, rep.result⟩) := by
  intro pub state addr fit
  obtain ⟨out, prop⟩ :=
    native_raw base fields vm inputs aux loc done M link safe apart c m start fit
  have eq := RegisterSetup.events_eq (recipes base fields) pub state m (fun i ↦ c.reg (vm i))
  change (RowRecipe.evaluate pub state m (lines base fields) (fun i ↦ c.reg (vm i))).1 =
    (RowRecipe.evaluate pub state m (lines base fields) (fun _ ↦ 0)).1 at eq
  dsimp only [events]
  rw [← eq]
  exact ⟨out, prop⟩

end PairSimulation.MapArgumentWriter

end VPVNP
end Computability
end OAI
