import OAI.Computability.MultitapeWeakETH.ProgramDecision
import OAI.Computability.IntegerMultiplication.Interface
import OAI.Computability.IntegerMultiplication.Code.CodePolyBasic

/-! # From a charged decision on encoded words to the deterministic Weak ETH machine -/

namespace OAI.Computability.MultitapeWeakETH.DecisionTapes

open IntegerMultiplication Code DepthThreeLowerBound
open private raw codeY inList_cost Ybase frame from OAI.Computability.IntegerMultiplication.Interface
noncomputable section

private def observation : Option Ltr → Bool
  | some (.bit b) => b
  | _ => false

/-- Encoding a single raw Boolean input costs linear time. Reading the
Boolean result uses the observation included in the multitape compiler. -/
theorem compile_word_decision {I : Type} (scale : I → ℕ) (input : I → List Bool) (answer : I → Bool)
    (inputSize : Dom scale (fun i => (input i).length))
    (program : Task.BT scale (fun i => send (input i)) (fun i => send (answer i))) :
    ∃ (M : FiniteMultiTapeMachine) (time : I → ℕ), Dom scale time ∧
      ∀ i, MultiTapeHaltsIn M (input i) (answer i) (time i) := by
  classical
  obtain ⟨budget,small,c,C,checked⟩ := program
  let p := Prog.join (.tie codeY) c
  obtain ⟨M,compile⟩ := compile_program p Ltr.bit (fun _ _ => Ltr.bit.inj) observation
  have result (i : I) :
      ∃ t ≤ 2*(11*(input i).length+C*(budget i+1)+8)+1, MultiTapeHaltsIn M (input i) (answer i) t := by
    obtain ⟨j,hj,exec⟩ := checked i [] (fun _ => [])
    simp only [frame] at exec
    have sub := inList_cost _ _ [] [] 5 [] (Ybase []) (input i)
    simp only [List.append_nil] at sub
    have load := Prog.Run.tie sub
    have joined := Prog.Run.join load exec
    have done := compile (input i) _ _ joined
    refine ⟨_,?_,by simpa [raw,Interface.letters_word,Tree.spell,observation] using done⟩
    omega
  choose t h stop using result
  refine ⟨M,t,?_,stop⟩
  have cost := (((Dom.const scale 11).mul inputSize).add
    ((Dom.const scale C).mul (small.add (Dom.const scale 1)))).add (Dom.const scale 8)
  exact (((Dom.const scale 2).mul cost).add (Dom.const scale 1)).mono h

end
end OAI.Computability.MultitapeWeakETH.DecisionTapes
