import OAI.Computability.MultitapeWeakETH.TerminalEnumeration
import OAI.Computability.MultitapeWeakETH.ResidentHistory

/-! # The logs used by the outer sum are retained histories for the private reader -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP Compression CompressorRecords BurstRAM DyadicBudget TerminalWords
open PairSimulation LocalHistory TraversalRoles TraversalRows Filter DescriptorSpace ScheduledTrace
open FactorizedCompression
open scoped Classical Fin.CommRing
noncomputable section

variable {k R V : Type} [Field k] [Field R] [AddCommMonoid V] {S : BlockSchedule k} (B : S.Templates)

attribute [local irreducible] BlockProgram.script BlockProgram.layout OnlineWorkspace.table source scale entryMemory BlockClock.small

set_option maxHeartbeats 1400000 in
theorem terminal_branches (f : B.Entry → R) (hf : B.IsSolution f) :
    ∃ eval : SharedQuery → Option SharedData, Poly eval ∧
      ∀ᶠ N : ℕ in atTop, ∀ v : Tally, v.length=N →
        let E := gridExecution B f hf v
        let L := (searchWidth (2*(4*stepSize B)) v).length
        let _ : Fintype E.Choices := choiceFintype E
        ∃ log : E.Choices → CallProgram.Stores (gridWidth B v),
          (∀ z, Recorded B f hf v z (log z)) ∧ ∀ weight : SharedData → V,
          ReaderEnumeration.treeSum (fun outer => ReaderEnumeration.treeSum
            (fun inner => (eval ((v,outer),inner)).elim 0 weight) L []) L [] =
            ∑ z, let Y := E.finalState z
                 ∑ h : (e : Y.network.Edge) → Y.network.Payload e,
                   weight ((writes (log z),widths Y,inverse Y),List.ofFn ((TerminalGatherGeometry.payload Y).symm h)) := by
  obtain ⟨eval,cost,ok⟩ := terminal_enumeration (V:=V) B f hf
  refine ⟨eval,cost,?_⟩
  filter_upwards [ok] with N good
  intro v len E L inst
  obtain ⟨H,terms⟩ := good v len
  let log (z : E.Choices) := CallProgram.storeEvents [] (eventLog (H.trace.cut.part z).logs)
  refine ⟨log,?_,terms⟩
  intro z
  have mem := CallProgram.memory_storeEvents (entryMemory B (3*(stepSize B*gridIndex B v)) (stepSize B*gridIndex B v)
    (scale B (gridIndex B v)) (gridIndex B v) (gridWidth B v)) [] (eventLog (H.trace.cut.part z).logs)
  unfold Recorded
  dsimp only
  rw [show memory _ (log z) = (H.trace.cut.part z).memory from mem]
  exact (H.final z).stored

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
