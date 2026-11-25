import OAI.Computability.NearSquareRoot.PhysicalWalshRoundedCommand
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeRate

/-! # Termination of the generated agenda with input-dependent piece budgets

Each reached piece is a genuine recursive invocation. The finite agenda bounds
the time and workspace of those particular calls even when the bounds depend
on all represented input records.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Pieces

open IntegerMultiplication Code Space KernelPass PhysicalWalshNode EffectiveBoundedTask

set_option maxHeartbeats 800000 in
/-- Recursively evaluate each member of the finite, generated agenda. -/
theorem roundedSweepTotal {a W : ℕ} (hw : 0 < W) (p : Plan (a+1) W W) (step : Cmd)
    (ha : 1<a+1) {I : Type} (b : I → Root)
    (capacity : ∀ i, (b i).size (a:=a) (W:=W) ≤ 2^((b i).w+1))
    (fits : ∀ i, (b i).Feasible hw p ha)
    (raw : ∃ t s, EffectiveBoundedTask.Runs step t s (rawInput hw p) (rawOutput hw p)) :
    ∃ t s, EffectiveBoundedTask.Runs (sweepCmd (a+1) W step) t s (fun i => send
      (((tally (b i).k,tally (b i).s),tally ((b i).w+1)),words ((b i).size (a:=a) (W:=W)) (b i).row))
      (fun i => send ((b i).stream hw p ((b i).pieces (a:=a) hw).length)) := by
  classical
  obtain ⟨time,space,run⟩ := raw
  let L (i : I) := (b i).pieces (a:=a) hw
  let X := (i : I) × Fin (L i).length
  have packet (z : X) := reachedPackets hw p ha (b z.1) (capacity _) (fits _) z.2
  let request (z : X) : Admitted hw p := (packet z).choose
  let clock (i : I) := Finset.univ.sup (fun j : Fin (L i).length => time (request ⟨i,j⟩))
  let scratch (i : I) := Finset.univ.sup (fun j : Fin (L i).length => space (request ⟨i,j⟩))
  let array (i : I) := (b i).size (a:=a) (W:=W)*(4*((b i).w+1)+4)+1
  let arena (i : I) := max (array i) (scratch i)
  have visit := (run.on request).mono (t':=fun z : X => clock z.1) (s':=fun z : X => arena z.1)
    (fun z => Finset.le_sup (f:=fun j => time (request ⟨z.1,j⟩)) (Finset.mem_univ z.2))
    (fun z => (Finset.le_sup (f:=fun j => space (request ⟨z.1,j⟩)) (Finset.mem_univ z.2)).trans (le_max_right ..))
  have reached : EffectiveBoundedTask.Runs step (fun z : X => clock z.1) (fun z => arena z.1)
      (fun z => send (Header.wire (a+1) ((L z.1).get z.2),(b z.1).stream hw p z.2))
      (fun z => send (Header.wire (a+1) ((L z.1).get z.2),(b z.1).stream hw p (z.2.val+1))) :=
    AgendaOps.conform visit (fun _ => rfl) (fun _ => rfl)
      (fun z => (packet z).choose_spec.2.1) (fun z => (packet z).choose_spec.2.2)
  have sweep := generatedSweepNamed (step:=step) ha hw (fun i => (b i).k) (fun i => (b i).s) (fun i => (b i).w)
    (fun i => (b i).stream hw p) (fun i _ => clock i) arena
    (fun i j _ => ((b i).stream_size hw p j).le.trans (le_max_left ..)) reached
  obtain ⟨d,C,h⟩ := sweep
  exact ⟨_,_,h⟩

end PhysicalWalsh.Pieces

end NearSquareRoot
end Computability
end OAI
