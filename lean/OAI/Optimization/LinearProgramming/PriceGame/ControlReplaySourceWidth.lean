import OAI.Optimization.LinearProgramming.PriceGame.ControlReplaySource
import OAI.Optimization.LinearProgramming.PriceGame.ControlReplayWidth
import OAI.Optimization.LinearProgramming.PriceGame.ControlGuardDeterminism

/-! Finite-tape memory bound for every physical replay iteration. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native
namespace Replay

open ExactQuantumFactoring.BitStackProgram

/-- Independently established guards on a source branch cover the very same data-only
trace and terminal state. -/
theorem SourceRuns.and {i : PublicInput} {P Q : Driver.PC → Prop}
    (first : SourceRuns i P) (second : SourceRuns i Q) :
    SourceRuns i (fun s => P s ∧ Q s) := by
  intro tr b emit
  obtain ⟨m,hp,stop⟩ := first emit
  obtain ⟨n,hq,_⟩ := second emit
  have same : m = n := hp.steps.target_eq hq.steps
  subst n
  exact ⟨m,hp.zip hq,stop⟩

theorem source_width (t : Tape) {P : Driver.PC → Prop} (runs : SourceRuns t.input P)
    {micro : ℕ × Driver.PC → Driver.Action}
    (stepP : Procedure (prodCode unaryCode Wire.combinedCode) Join.actionCode micro)
    (agree : ∀ s, P s → micro (t.input.goods,s) = Driver.step s)
    (pc : Polynomial ℕ) (bound : ∀ s, P s →
      (Wire.combinedCode s).length ≤ pc.eval (Campaign.inputSize t.input.goods t.input.range)) (j : ℕ) :
    (stateCode ((advance micro)^[j] (live t.input.goods t.reverseReplies.reverse
      (initialPC t.input)))).length ≤ (functionWidth pc stepP.bound).eval (ecPad t).length := by
  have hN : t.input.goods ≤ (ecPad t).length := by
    have := inputSize_le_ecPad t
    unfold Campaign.inputSize at this
    omega
  have hbits : t.reverseReplies.reverse.length ≤ (ecPad t).length := by
    rw [List.length_reverse,ecPad_length,encodeTape_length]
    omega
  have hb (s) (hs : P s) : (Wire.combinedCode s).length ≤ pc.eval (ecPad t).length :=
    (bound s hs).trans (Procedure.eval_nat_mono pc (inputSize_le_ecPad t))
  obtain ⟨tr,b,emit,coverage⟩ := Driver.fits_source (campaignSolver Campaign.rounds t.input)
    t.reverseReplies.reverse
  obtain ⟨last,run,stop⟩ := runs emit
  rcases coverage with ⟨moreBits,hit⟩ | ⟨k,hk,hit⟩
  · rw [hit] at hbits ⊢
    exact width_on_complete run.steps stepP _ hN agree hb b run.endpoint
      ((agree _ run.endpoint).trans stop) moreBits hbits j
  · rw [hit] at hbits ⊢
    exact width_on_short run.steps stepP _ hN agree hb k hk hbits j

end Replay
end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
