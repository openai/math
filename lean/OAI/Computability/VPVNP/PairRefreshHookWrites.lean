import OAI.Computability.VPVNP.PairRefreshHookSite
import OAI.Computability.VPVNP.PairRefreshTraversalQuiet
import OAI.Computability.VPVNP.PairRefreshVertexInputWrites

/-! # The accepted refresh hook leaves external RAM intact

The row locator and older-half reader change only private state. The selected
action updates private scratch and the label histogram. Their complete
chronological trace therefore replays on the same external memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook.Site

open BurstRAM Compression Compression.Refresh Compression.DegreeRefresh CompressorRecords CompressorRecords.PortRefresh
open NodeArguments TraversalControllerInputs

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates} {bits n hist t : ℕ}
  (R : Site B n hist bits) (ties : Fin t ≃ Tie (2^S.portExponent)) (stride : ℕ) (order : B.Entry ≃ Fin hist)
  (pub : Fin 11 → BurstRAM.Word bits) (m : Memory bits)

variable {node : BurstRAM.Word bits} {s : DFS.Scratch bits n} {bs tail : List Bool}
  {out : ShrinkRole.Outcome bits n (R.state.network.Half R.olderSite × R.nextState.network.Half R.newerSite)}

theorem read_noWrites (h : R.read ties stride order pub m node s bs = some (out,tail)) :
    SourceTransport.Writes (fun _ => False) out.trace := by
  obtain ⟨_,_,es,selected,trace⟩ := (RefreshHook.read_some_iff R.state R.olderSite R.nextState R.newerSite
    R.arena R.oldNode R.parent (R.front pub m) (R.action ties stride order pub m) node s bs out tail).mp h
  rw [trace]
  intro a value ha
  rcases List.mem_append.mp ha with setup | visit
  · exact RefreshVertexAssembly.inputTrace_noWrites R.state R.olderSite out.value.1 R.prev m R.listHead
      pub node R.level R.later a value setup
  · exact TraversalPlan.canonicalAction_noWrites B ties stride order R.state R.choice R.port R.degree n R.rowEnd
      R.oldNode R.parent R.room out.value.1 out.value.2 m (levelHead pub m R.level).val
      (levelHead pub m (R.level+1)).val R.geometry selected a value visit

theorem read_after (h : R.read ties stride order pub m node s bs = some (out,tail)) :
    after m out.trace = m :=
  funext fun _ => SourceTransport.after_outside m (R.read_noWrites ties stride order pub m h) id

end PairSimulation.RefreshHook.Site

end VPVNP
end Computability
end OAI
