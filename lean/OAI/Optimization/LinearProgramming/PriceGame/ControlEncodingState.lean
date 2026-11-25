import OAI.Optimization.LinearProgramming.PriceGame.ControlWireState
import OAI.Optimization.LinearProgramming.PriceGame.ControlEncodingPackets
import OAI.Optimization.LinearProgramming.PriceGame.ControlEncodingShape

/-! Total size of a reachable serialized program counter plus all saved frames, measured
on the actual numeric packets. Structural bounds follow from the interpreter's transitions. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Wire
namespace Envelope

open Trial ExactQuantumFactoring.BitStackProgram

variable (e : Envelope)

def frameSize (calls : ℕ) := pairBound e.depth (pairBound calls (pairBound e.inputSize
  (pairBound (listBound calls e.completedSize) e.preparedSize)))

def pcSize (calls ticks : ℕ) := 2 + pairBound e.depth e.inputSize +
  pairBound e.depth (pairBound calls (pairBound e.inputSize (listBound calls e.completedSize))) +
  e.resultSize + pairBound (e.frameSize calls) (pairBound e.resultSize ticks)

def stateSize (calls ticks : ℕ) :=
  pairBound (e.pcSize calls ticks) (listBound e.depth (e.frameSize calls))

structure FramePayload (f : Frame NodeInput Prepared Completed) : Prop where
  input : e.InputFits f.input
  rows : ∀ x ∈ f.prefix, e.CompletedFits x
  prep : e.PreparedFits f.prepared

def PCPayload : PC NodeInput Prepared PackedRound Completed → Prop
  | .enter _ i => e.InputFits i
  | .schedule _ _ i xs => e.InputFits i ∧ ∀ c ∈ xs, e.CompletedFits c
  | .returned out => e.ResultFits out
  | .feedback f out _ => e.FramePayload f ∧ e.ResultFits out

def StatePayload (s : State NodeInput Prepared PackedRound Completed) : Prop :=
  e.PCPayload s.pc ∧ ∀ f ∈ s.stack, e.FramePayload f

theorem frame_length (calls : ℕ) (f : Frame NodeInput Prepared Completed)
    (fd : f.childFuel ≤ e.depth) (rem : f.remaining ≤ calls) (pre : f.prefix.length ≤ calls)
    (payload : e.FramePayload f) : (frameCode f).length ≤ e.frameSize calls :=
  prod_le _ _ _ _ ((nat_le_self _).trans fd) (prod_le _ _ _ _ ((nat_le_self _).trans rem)
    (prod_le _ _ _ _ (e.input_length _ payload.input)
      (prod_le _ _ _ _ (list_le _ _ pre (fun c hc => e.completed_length _ (payload.rows c hc)))
        (e.prepared_length _ payload.prep))))

theorem pc_length (calls ticks level : ℕ) (pc : PC NodeInput Prepared PackedRound Completed)
    (shape : LocalShape e.depth calls ticks level pc) (payload : e.PCPayload pc) :
    (pcCode pc).length ≤ e.pcSize calls ticks := by
  cases pc with
  | enter fuel i =>
    change level + fuel ≤ e.depth at shape
    have h := prod_le Nat.bits nodeInputCode fuel i ((nat_le_self fuel).trans (by omega : fuel ≤ e.depth))
      (e.input_length i payload)
    simp only [pcCode,List.length_cons,pcSize]
    omega
  | schedule fuel rem i xs =>
    change level + fuel + 1 ≤ e.depth ∧ xs.length + rem ≤ calls at shape
    obtain ⟨hi,hx⟩ := payload
    have hh := prod_le Nat.bits (prodCode Nat.bits (prodCode nodeInputCode (listCode completedCode)))
      fuel (rem,i,xs) ((nat_le_self fuel).trans (by omega : fuel ≤ e.depth))
      (prod_le _ _ _ _ ((nat_le_self rem).trans (by omega : rem ≤ calls)) (prod_le _ _ _ _
        (e.input_length _ hi) (list_le completedCode xs (by omega : xs.length ≤ calls)
          (fun c hc => e.completed_length _ (hx c hc)))))
    simp only [pcCode,List.length_cons,pcSize]
    omega
  | returned out =>
    have h := e.result_length _ payload
    simp only [pcCode,List.length_cons,pcSize]
    omega
  | feedback f out replies =>
    change level + f.childFuel + 1 ≤ e.depth ∧ f.prefix.length + f.remaining + 1 ≤ calls ∧
      replies.length ≤ ticks at shape
    obtain ⟨hf,ho⟩ := payload
    have hh := prod_le frameCode (prodCode packedRoundCode id) f (out,replies)
      (e.frame_length calls f (by omega) (by omega) (by omega) hf)
      (prod_le _ id out replies (e.result_length _ ho) shape.2.2)
    simp only [pcCode,List.length_cons,pcSize]
    omega

/-- Every prefix of the small-step evaluator obeys this bound. In particular,
`calls` pays for each cached completion, and the allocation table pays for each
expert-good cell at every saved level. -/
theorem reachable_state_length {ops : Kernel NodeInput Prepared PackedRound Completed PackedQuery}
    {calls ticks : ℕ} {i : NodeInput} {tr} {s : State NodeInput Prepared PackedRound Completed}
    (run : Steps ops calls (initial e.depth i) tr ticks s) (payload : e.StatePayload s) :
    (stateCode s).length ≤ e.stateSize calls ticks := by
  have shape := shape_of_reachable run
  apply prod_le _ _ _ _ (e.pc_length _ _ _ _ shape.2 payload.1)
  apply list_le _ _ (stack_length_of_shape shape)
  intro f hf
  obtain ⟨hd,hr,hp⟩ := frame_sizes_of_shape shape f hf
  exact e.frame_length calls f hd hr hp (payload.2 f hf)

end Envelope
end Wire
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
