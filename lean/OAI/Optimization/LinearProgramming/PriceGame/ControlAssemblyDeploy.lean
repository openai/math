import OAI.Optimization.LinearProgramming.PriceGame.ControlAssemblyMachine
import OAI.Optimization.LinearProgramming.PriceGame.ControlAssemblySpec
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialAssemble

/-! The binary program assembles exactly the public data of each completed recursive trial. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram
open States.Mass TrialExecution Trial Wire

abbrev FullFrame (N r : ℕ) :=
  {x : AssemblyFrame // x.calls.length = 2*r ∧ outputWidth r x = N * 2^x.input.level}

/-- The machine reads the original frame words. The dependent type restricts the
correctness statement to a frame with exactly the dimensions expected by its caller. -/
noncomputable def assemblePacketP (N r : ℕ) :
    Procedure (fun x : FullFrame N r => assemblyFrameCode x.val) packedRoundCode
      (fun x => assemblePacketSized N r x.val.experts.length x.val.experts x.val.input x.val.calls) :=
  ((assembleFrameP r).precompose (fun x : FullFrame N r => x.val)).congrFun
    (fun x => assembleValue_eq_assemblePacketSized N r x.val x.property.1 x.property.2)

/-- The packed frame built from the actually returned child data. -/
def liveFrame {N ne r l : ℕ} (experts : Fin ne → Expert N) (hist : History N)
    (w : Weights ne) (s : NodeRun experts w r l) : AssemblyFrame :=
  ⟨List.ofFn (fun i => packExpert (experts i)), codeInput l hist w, List.ofFn (fun j => codeCall (s.val j))⟩

theorem liveFrame_full {N ne r l : ℕ} (hr : 0 < r) (experts : Fin ne → Expert N)
    (hist : History N) (w : Weights ne) (s : NodeRun experts w r l) :
    let x := liveFrame experts hist w s
    x.calls.length = 2*r ∧ outputWidth r x = N * 2^x.input.level := by
  intro x
  constructor
  · exact List.length_ofFn
  · have h : r < 2*r := by omega
    simp [x, liveFrame, outputWidth, finalRows, codeInput, List.headD_eq_head?_getD, List.head?_drop,
      h, codeCall, length_packTable]

/-- Every positive-arity completed schedule has the correct dimensions automatically.
The finite stack program and its polynomial clock are uniform in all other frame data. -/
noncomputable def assembleNodeP {N ne r l : ℕ} (hr : 0 < r) (experts : Fin ne → Expert N)
    (hist : History N) (w : Weights ne) :
    Procedure (fun s : NodeRun experts w r l => assemblyFrameCode (liveFrame experts hist w s))
      packedRoundCode (fun s => codeOutput (assemble experts hist w s).val) := by
  let inject := fun s : NodeRun experts w r l =>
    (⟨liveFrame experts hist w s, liveFrame_full hr experts hist w s⟩ : FullFrame N r)
  apply ((assemblePacketP N r).precompose inject).congrFun
  intro s
  simpa only [inject, liveFrame, List.length_ofFn] using assemblePacket_spec experts hist w s

/-- Specializing to a reached schedule changes only the specification of the input;
the compiled finite instruction sequence and polynomial clock are the same for all
dimensions, expert rosters, histories, and weights. -/
theorem assembleNodeP_uniform {N ne r l : ℕ} (hr : 0 < r) (experts : Fin ne → Expert N)
    (hist : History N) (w : Weights ne) :
    (assembleNodeP (l:=l) hr experts hist w).program = (assembleFrameP r).program ∧
      (assembleNodeP (l:=l) hr experts hist w).bound = (assembleFrameP r).bound :=
  ⟨rfl, rfl⟩

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
