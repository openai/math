import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialPackets

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Trial

open States.Mass TrialExecution Moment

variable {N ne r l : ℕ}

@[simp] theorem atD_vector {α : Type*} [Inhabited α] {n : ℕ} (v : Vector α n) (i : Fin n) :
    atD v.toList i.val = v[i] := by simp [atD, i.isLt]

/-- Numeric averaging reads exactly the scheduled vectors and the cached child scores.
The probe log lists each probe before its descendants and each final call's descendants
in their original chronological order. -/
theorem assemblePacket_spec (experts : Fin ne → Expert N) (history : History N) (w : Weights ne)
    (run : NodeRun experts w r l) :
    assemblePacketSized N r ne (List.ofFn (fun e => packExpert (experts e))) (codeInput l history w)
      (List.ofFn fun j => codeCall (run.val j)) = codeOutput (assemble experts history w run).val := by
  apply PackedRound.mk.injEq .. |>.mpr
  constructor
  · change packTable N l (fun i => median fun a : Fin r =>
      lookupTable N l (atD (List.ofFn fun j => codeCall (run.val j)) (finalIndex a).val).mapped i) =
      packTable N l (fun i => median fun a : Fin r => (run.val (finalIndex a)).data.mapped i)
    apply congrArg (packTable N l)
    funext i
    simp only [atD_ofFn, codeCall, lookupTable_pack]
  constructor
  · change List.ofFn _ = (nodeScores experts run.val).toList
    rw [nodeScores, Vector.toList_ofFn]
    apply congrArg List.ofFn
    funext e
    simp only [atD_ofFn, packExpert, codeCall, codeOutput, atD_vector, codeInput, mask, Expert.isLocal,
      decide_eq_true_eq]
    rfl
  · change _ = (nodeLog history run.val).map packProbe
    rw [nodeLog, List.map_flatten, List.map_ofFn]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext j
    by_cases hj : j.val < r <;> simp [hj, codeInput, codeCall, codeOutput, packProbe]

end Trial
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
