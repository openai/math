import OAI.Computability.VPVNP.PairRefreshVertexPrefix
import OAI.Computability.VPVNP.CompressorFlowFootprint

/-!
# External write footprint of the refresh vertex inputs

The level locator and each child header probe external memory. The child scan
stores the guessed half-wire bits in private memory. Its chronological trace,
including each choice, contains no external write.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation

open BurstRAM Compression CompressorRecords NodeArguments

variable {w a g : ℕ}

theorem VertexLevel.trace_noWrites (pub : Fin 11 → Word w) (m : Memory w) (level later : ℕ) :
    SourceTransport.Writes (fun _ => False) (VertexLevel.trace pub m level later) := by
  intro p v h
  have scan (n : ℕ) : Event.write p v ∉ VertexLevel.scanEvents pub m level n := by
    induction n with
    | zero => simp [VertexLevel.scanEvents, VertexLevel.testEvents]
    | succ n ih => simp [VertexLevel.scanEvents, VertexLevel.testEvents, ih]
  simp [VertexLevel.trace, VertexLevel.bootEvents, scan] at h

theorem NodeArguments.ChildHeader.events_noWrites (m : Memory w) (node base : Word w) :
    SourceTransport.Writes (fun _ => False) (ChildHeader.events m node base) := by
  intro p v h
  simp [ChildHeader.events] at h

/-- Every ordered child row only reads the external descriptor and columns.
The bit payloads may be chosen arbitrarily. -/
theorem NodeArguments.ChildScan.events_noWrites (X : State a g) (U : IncidenceDirectory w)
    (m : Memory w) (src : ℕ) (xs : List (ChildScan.Child X)) :
    SourceTransport.Writes (fun _ => False) (ChildScan.events X U m src xs) := by
  intro p v
  induction xs generalizing src with
  | nil => simp [ChildScan.events]
  | cons x xs ih =>
    intro h
    simp only [ChildScan.events, ChildScan.childEvents, ChildScan.setupEvents, ChildAddress.events,
      List.mem_append, List.mem_cons, List.not_mem_nil, reduceCtorEq, false_or] at h
    rcases h with h | tail
    · obtain ⟨i, _, slot⟩ := List.mem_flatMap.mp h
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, reduceCtorEq, false_or] at slot
      rcases slot with header | bits
      · cases dir : i.1 <;> simp [FieldGuess.headerEvents, dir] at header
      · exact (FlowFootprint.bounds_of_noProbes (fun _ => False) (fun _ => False)
          (PrivateFields.events_work (w := w) .guess (List.ofFn (x.data i))).2).2 p v bits
    · exact ih (src+1) tail

/-- The complete input trace for a typed old half leaves all external words
untouched, independently of the values returned by its probes. -/
theorem RefreshVertexAssembly.inputTrace_noWrites (X : State a g) (site : X.network.Site)
    (old : X.network.Half site) (U : IncidenceDirectory w) (m : Memory w) (listHead : ℕ)
    (pub : Fin 11 → Word w) (node : Word w) (level later : ℕ) :
    SourceTransport.Writes (fun _ => False) (inputTrace a X site old U m listHead pub node level later) := by
  intro p v h
  simp only [inputTrace, List.mem_append] at h
  rcases h with levelRead | handoff | bank | header | scan
  · exact VertexLevel.trace_noWrites pub m (level+1) later p v levelRead
  · simp at handoff
  · simp [List.mem_replicate] at bank
  · exact ChildHeader.events_noWrites m _ _ p v header
  · exact ChildScan.events_noWrites X U m listHead _ p v scan

end PairSimulation

end VPVNP
end Computability
end OAI
