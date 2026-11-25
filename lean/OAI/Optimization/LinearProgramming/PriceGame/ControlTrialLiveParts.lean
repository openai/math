import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialLiveKernel
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialSourceCaps
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialNativeBase
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialFinishCorrect
import OAI.Optimization.LinearProgramming.PriceGame.ControlAssemblyDeploy

/-! The literal bit-stack transition implements every instruction on actual
recursive-trial data, including both successors of an unanswered public query. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open Trial Wire States.Mass Moment TrialExecution

attribute [local irreducible] Moment.probes

variable {N ne R : ℕ}

def publicTrialGlobals (N R : ℕ) (experts : Fin ne → Expert N) : TrialGlobals :=
  (N,R,List.ofFn fun e => packExpert (experts e))

set_option exponentiation.threshold 300 in
theorem trialKernelUsing_live (preparePacket : PrepareWords → Prepared)
    (correct : ∀ x : PrepareWords, x.1.1*2^x.2.1.level ≤ 2*(x.1.1*x.1.1) →
      (∀ i < x.1.2.2.length, scoreTotal x.2.2 i ≤ 2*probes*(2*x.1.1)^274) →
      preparePacket x = preparePacketSized x.1.1 x.1.2.1 x.1.2.2.length x.1.2.2 x.2.1 x.2.2)
    (hN : 0 < N) (experts : Fin ne → Expert N) (R : ℕ) :
    LiveKernelRefinement probes R experts (trialKernelUsing preparePacket (publicTrialGlobals N R experts)) where
  leaf := by
    intro c hd
    change leafPacketSized (publicTrialGlobals N R experts) c.input = leafPacket N R ne c.input
    have e := leafPacketSized_eq (publicTrialGlobals N R experts) c.input hd
    simpa only [publicTrialGlobals,List.length_ofFn] using e
  prepare := by
    intro k j c hdepth hj p
    simp only [trialKernelUsing,SourceNode.prepared,fixedKernel,packetKernelSized]
    have width : N*2^c.level ≤ 2*(N*N) := calc
      N*2^c.level = 2^c.level*N := Nat.mul_comm ..
      _ = Fintype.card (Vertex N c.level) := (card_vertices N c.level).symm
      _ ≤ 2*N^2 := card_vertices_le N c.level hN (by omega)
      _ = _ := by rw [pow_two]
    let g := publicTrialGlobals N R experts
    let x := (prepareGlobals g,c.input,c.rows (r:=probes) p.calls.val)
    have score (i : ℕ) (hi : i < ne) : scoreTotal (c.rows (r:=probes) p.calls.val) i ≤ 2*probes*(2*N)^274 :=
      (p.scoreTotal hN (by omega) ⟨i,hi⟩).trans (Nat.mul_le_mul_right _ hj.le)
    have hp := correct x width (by
      intro i hi
      have hi' : i < ne := by
        simpa only [x,prepareGlobals,g,publicTrialGlobals,List.length_ofFn] using hi
      exact score i hi')
    simpa only [x,prepareGlobals,g,publicTrialGlobals,List.length_ofFn] using hp
  descend := fun _ _ => rfl
  assemble := by
    intro k c p
    simp only [trialKernelUsing,fixedKernel,packetKernelSized,publicTrialGlobals,SourceNode.input,SourceNode.rows]
    let x := liveFrame (r:=probes) (l:=c.level) experts c.history c.weights p.calls
    have shape := liveFrame_full (r:=probes) (l:=c.level) probes_pos experts c.history c.weights p.calls
    have eq := assembleValue_eq_assemblePacketSized N probes x shape.1 shape.2
    simpa only [x,liveFrame,List.length_ofFn] using eq
  finish := by
    intro k j c p tr ch emitted tape
    let roster := List.ofFn fun a => packExpert (experts a)
    simp only [trialKernelUsing,fixedKernel,packetKernelSized,publicTrialGlobals,SourceNode.input]
    have eq := boundedTrialFinish_eq (N:=N) (l:=c.level) R c.history c.weights roster (c.rows (r:=probes) p.calls.val)
      (c.prepared (r:=probes) R experts p.calls.val) (codeOutput ch.val) tape
      (c.selectedPrice (r:=probes) experts p.calls.val) ch.val.prices (c.prepared_baseline R experts p.calls.val) rfl
    simpa only [roster,List.length_ofFn] using eq

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
