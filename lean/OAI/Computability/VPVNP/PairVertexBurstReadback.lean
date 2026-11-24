import OAI.Computability.VPVNP.RAMProcessorReportPrefix
import OAI.Computability.VPVNP.PairVertexSiteReport
import OAI.Computability.VPVNP.PairVertexOccurrence
import OAI.Computability.VPVNP.PairSimulationTerminalSiteRun

/-!
# Returning one terminal vertex at the burst cutoff

The prefix enters the DFS after preparing the actual root argument. The
native occurrence supplies the choice events and the histogram update.
Conversely, every returning input must pass the same deterministic prefix.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage

open BurstRAM PrivateRAM DFS LocalHistory

variable {w p r k : ℕ} {M : Machine w p r k} {m : Memory w}
    {start cfg : Config w p r} {es : List (Event w)}

open private returns_prefix from OAI.Computability.VPVNP.PairSimulationDFSDecode

/-- Pull a complete accepting word back through the native bootstrap,
geometry and gather prefixes. Empty words are allowed. -/
theorem prefix_occurrences {X : Type*} (encode : X → List Bool)
    (pre : TerminalSiteStart.Continues M m start cfg es)
    (decode : ∀ bits, Returns M cfg m bits ↔ ∃! x, bits = encode x) (bits : List Bool) :
    Returns M start m bits ↔ ∃! x, bits = encode x := by
  exact (returns_prefix (fun f => pre f bits)).trans (decode bits)

/-- When the actual report fits the public clock, the reported output
includes exactly the prefix events and preserves the semantic update of the
DFS and flush. The clock may have arbitrary spare instructions. -/
theorem emit_at_cutoff (pre : TerminalSiteStart.Continues M m start cfg es)
    (readOnly : after m es = m) (det : choiceBits es = [])
    (rep : Report w) (bits : List Bool) (choice : choiceBits rep.events = bits)
    (run : ∀ extra, execute M.program (extra + rep.events.length + 1) cfg m bits = some rep)
    (fuel : ℕ) (enough : es.length + rep.events.length + 1 ≤ fuel) :
    let whole : Report w := ⟨es ++ rep.events, rep.result⟩
    execute M.program fuel start m bits = some whole ∧ choiceBits whole.events = bits ∧
      after m whole.events = after m rep.events ∧
      countProbes whole.events = countProbes es + countProbes rep.events := by
  intro whole
  have clock : fuel = (fuel-(es.length+rep.events.length+1)+rep.events.length+1)+es.length := by omega
  refine ⟨?_,?_,?_,?_⟩
  · rw [clock,pre,run]
    rfl
  · exact (PrimedInputRAM.Flow.choiceBits_append ..).trans (by rw [det,choice,List.nil_append])
  · exact (show after m (es ++ rep.events) = after (after m es) rep.events from List.foldl_append).trans
      (congrArg (fun a => after a rep.events) readOnly)
  · exact countProbes_append ..

/-- Uniqueness and external readback also hold for an arbitrary observed
return, including a report first supplied by the burst interpreter. -/
theorem observed_at_cutoff {X : Type*} (encode : X → List Bool) (update : X → Memory w)
    (next : Word w) (fuel : ℕ)
    (decode : ∀ bits, Returns M start m bits ↔ ∃! x, bits = encode x)
    (emit : ∀ x, ∃ rep, execute M.program fuel start m (encode x) = some rep ∧
      rep.result = some next ∧ after m rep.events = update x)
    (bits : List Bool) (observed : Report w) (run : execute M.program fuel start m bits = some observed) :
    ∃! x, bits = encode x ∧ observed.result = some next ∧ after m observed.events = update x := by
  obtain ⟨x,word,unique⟩ := (decode bits).mp ⟨fuel,observed,run⟩
  obtain ⟨rep,hr,state,memory⟩ := emit x
  rw [←word,run] at hr
  cases Option.some.inj hr
  exact ⟨x,⟨word,state,memory⟩,fun y hy => unique y hy.1⟩

end PairSimulation.VertexImage

end VPVNP
end Computability
end OAI
