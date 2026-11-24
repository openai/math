import OAI.Computability.VPVNP.PairShrinkNodeStageCost
import OAI.Computability.VPVNP.CompressorSourceTransport

/-!
# Read-only support of a complete shrinking vertex visit

A successful visit follows the child, absorbed-field and map readers on the
scratch and tape returned by their predecessors. The union of their actual
read domains bounds the chronological trace even if a later DFS visit fails.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM DFS Compression CompressorRecords CompressorRecords.SourceTransport
open NodeArguments NodeArguments.ChildScan ShrinkHiddenGuess

/-- Every external memory access in the trace is a read at an address satisfying `allow`. -/
abbrev TraceSupport {w : ℕ} (allow : ℕ → Prop) (es : List (Event w)) : Prop :=
  Reads allow es ∧ Writes (fun _ ↦ False) es

theorem TraceSupport.append {w : ℕ} {allow : ℕ → Prop} {a b : List (Event w)}
    (first : TraceSupport allow a) (last : TraceSupport allow b) : TraceSupport allow (a ++ b) :=
  ⟨fun i v h ↦ (List.mem_append.mp h).elim (first.1 i v) (last.1 i v),
    fun i v h ↦ (List.mem_append.mp h).elim (first.2 i v) (last.2 i v)⟩

theorem TraceSupport.memory {w : ℕ} {allow : ℕ → Prop} {es : List (Event w)}
    (h : TraceSupport allow es) (m : Memory w) : after m es = m :=
  funext fun _ ↦ after_outside m h.2 id

variable {w n a g : ℕ} {X : State a g} (arena : Arena) (inc : IncidenceDirectory w)
  (m : Memory w) (older cap : ℕ) (desc : Word w → ChildArguments.Descriptor w X)
  (args : List (Child X) → Args w) (seed : List (Child X) → List Row)
  (maps : List (Child X) → List Row → List (ResidentMapLoop.Exact.Action w n))
  (first : Setup w n) (second : List (Child X) → Setup w n)
  (third : List (Child X) → List Row → Setup w n) (node : Word w) (allow : ℕ → Prop)

/-- Only readers that the native visit reaches contribute to the footprint. -/
theorem visit_footprint (saved : Scratch w n) (bits tail : List Bool) (job : VisitPath w n)
    (entry : TraceSupport allow (first.trace node saved))
    (child : ∀ c rest, ChildArguments.reader arena inc m older cap desc node
      (first.updated node saved) bits = some (c, rest) → TraceSupport allow c.trace)
    (hiddenSetup : ∀ xs s, TraceSupport allow ((second xs).trace node s))
    (hidden : ∀ xs (s : Scratch w n) b out rem,
      hiddenReader (args xs) m (seed xs) node s b = some (out, rem) →
      TraceSupport allow out.trace)
    (mapSetup : ∀ xs hs s, TraceSupport allow ((third xs hs).trace node s))
    (scan : ∀ xs hs s trace final,
      ResidentMapLoop.Exact.scan node (maps xs hs) s = some (trace, final) →
        TraceSupport allow trace)
    (hit : (hook (visitReader arena inc m older cap desc args seed maps first second third)).read
      node saved bits = some (job, tail)) : TraceSupport allow job.trace := by
  obtain ⟨⟨out, rest⟩, found, eqn⟩ := Option.map_eq_some_iff.mp hit
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj eqn
  obtain ⟨c, middle, h, final, trace, childRead, hiddenRead, scanned, _, _, _, events⟩ :=
    ShrinkNodeCost.visit_trace_reached arena inc m older cap desc args seed maps first second third
      node saved bits rest out found
  have childTrace := congrArg Outcome.trace
    (ChildArguments.reader_some arena inc m older cap desc childRead).2.1
  have hiddenTrace := (ShrinkNodeCost.hidden_trace (args c.value) m (seed c.value) node
    ((second c.value).updated node c.updated) middle rest h hiddenRead).1
  change TraceSupport allow out.trace
  rw [events, ← hiddenTrace]
  have ch : TraceSupport allow (ChildHeader.events m node (desc node).directoryBase ++
      ChildScan.events X inc m (desc node).source c.value) :=
    (congrArg (TraceSupport allow) childTrace).mp (child c middle childRead)
  have throughChild := (entry.append ch).append (hiddenSetup c.value c.updated)
  have throughHidden := throughChild.append (hidden _ _ _ _ _ hiddenRead)
  exact (throughHidden.append (mapSetup c.value h.value h.updated)).append (scan _ _ _ _ _ scanned)

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
