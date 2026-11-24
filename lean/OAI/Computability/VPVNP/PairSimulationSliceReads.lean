import OAI.Computability.VPVNP.CompressorRegisterSetupTrace
import OAI.Computability.VPVNP.PairSimulationPrivateSlices

/-!
# External cells read by operand setup and private slice transfers

The native setup reads only the cells reached by its evaluated load expressions.
The slice header always reads its length and reads its offsets only for a nonempty
intersection. The private bit loop adds no external reads.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PhaseRecipe

open BurstRAM

theorem Expr.ReadsFrom.mono {w : ℕ} {data data' : ℕ → Prop} {pub : Fin 5 → Word w}
    {state : Word w} {mem : Memory w} {e : Expr} (h : e.ReadsFrom data pub state mem)
    (incl : ∀ i, data i → data' i) : e.ReadsFrom data' pub state mem := by
  induction e with
  | lit | state | publicWord => trivial
  | load e ih => exact ⟨ih h.1, incl _ h.2⟩
  | binary op a b ha hb => exact ⟨ha h.1, hb h.2⟩

end CompressorRecords.PhaseRecipe

namespace CompressorRecords.RegisterSetup

open BurstRAM BurstRAM.PrivateRAM PhaseRecipe RowRecipe SourceTransport

variable {w p r k n : ℕ} (f : Fin n → Expr) (inputs : Fin 6 → Fin r)
  (vm : Fin (regCount f) ↪ Fin r)

/-- The actual continuation trace of a linked setup reads only the cells visited by
its evaluated load expressions, including nested loads that compute later addresses. -/
theorem execute_setup_trace_reads (M : Machine w p r k) (m : Memory w) (pc : ℕ → Fin p)
    (link : Linked vm inputs M pc (lines f)) (safe : ∀ i j, vm i ≠ inputs j)
    (c : Config w p r) (hpc : c.pc = pc 0) (data : ℕ → Prop)
    (allowed : ∀ i, (f i).ReadsFrom data (fun j : Fin 5 => c.reg (inputs j.castSucc))
      (c.reg (inputs (Fin.last 5))) m) :
    let pub := fun i : Fin 5 => c.reg (inputs i.castSucc)
    let state := c.reg (inputs (Fin.last 5))
    ∃ events d, Reads data events ∧ events.length = (lines f).length ∧
      countProbes events = ∑ i, (f i).loads ∧ choiceBits events = [] ∧ d.pc = pc (lines f).length ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent ∧
      (∀ i, d.reg (vm (output f i)) = (f i).eval pub state m) ∧
      (∀ j, (∀ i, j ≠ vm i) → d.reg j = c.reg j) ∧
      ∀ fuel bs, execute M.program (fuel + events.length) c m bs =
        (execute M.program fuel d m bs).map (fun rep => ⟨events ++ rep.events, rep.result⟩) := by
  intro pub state
  let rs := fun i => c.reg (vm i)
  let events := (evaluate pub state m (lines f) rs).1
  obtain ⟨d, exitData⟩ := execute_setup_raw f inputs vm M m pc link safe c hpc
  exact ⟨events, d, lines_reads f data pub state m allowed rs, exitData⟩

end CompressorRecords.RegisterSetup

namespace PairSimulation

open BurstRAM CompressorRecords CompressorRecords.PhaseRecipe CompressorRecords.SourceTransport
open scoped Fin.CommRing

variable {w : ℕ} {data : ℕ → Prop}

/-- Guesses and copies within the private bit loop read no external cell. -/
theorem PrivateFields.events_reads (mode : PrivateFields.Mode) (bs : List Bool) :
    Reads data (PrivateFields.events (w := w) mode bs) :=
  (FlowFootprint.bounds_of_noProbes data data (PrivateFields.events_work mode bs).2).1

/-- The physical frame reads its length on every branch. Its offsets are needed
only if that length is nonzero, even when the external cells contain stale values. -/
theorem PrivateSlices.frameEvents_reads_iff (m : Memory w) (f : Word w) (bs : List Bool) :
    Reads data (PrivateSlices.frameEvents m f bs) ↔
      data (f + 1 + 1).val ∧ (m (f + 1 + 1).val ≠ 0 → data f.val ∧ data (f + 1).val) := by
  have copy : Reads data (if bs.isEmpty then [] else PrivateFields.events (w := w) .copy bs) := by
    split
    · simp [Reads]
    · exact PrivateFields.events_reads .copy bs
  have header : Reads data (PrivateSlices.frameEvents m f bs) ↔
      Reads data (PrivateSlices.headerEvents m f) := by
    constructor
    · exact fun h a v hv => h a v (List.mem_append_left _ hv)
    · intro h a v hv
      exact (List.mem_append.mp hv).elim (h a v) (copy a v)
  rw [header]
  by_cases empty : m (f + 1 + 1).val = 0
  · simp [PrivateSlices.headerEvents, empty, Reads]
  · simp [PrivateSlices.headerEvents, empty, Reads, or_imp, forall_and]

theorem PrivateSlices.frameEvents_reads (m : Memory w) (f : Word w) (bs : List Bool)
    (src : data f.val) (dst : data (f + 1).val) (len : data (f + 1 + 1).val) :
    Reads data (PrivateSlices.frameEvents m f bs) :=
  (PrivateSlices.frameEvents_reads_iff m f bs).mpr ⟨len, fun _ => ⟨src, dst⟩⟩

end PairSimulation

end VPVNP
end Computability
end OAI
