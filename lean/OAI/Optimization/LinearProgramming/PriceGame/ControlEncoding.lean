import OAI.Optimization.LinearProgramming.PriceGame.ControlPrefix
import OAI.Optimization.LinearProgramming.OracleSpec.Dialogue
import OAI.Optimization.LinearProgramming.OracleSpec.PriceEncoding

/-! External continuation of the price-game dispatcher. The first frame is the reverse
reply tape. Its terminating zero is the initial dialogue tag; each incoming tagged answer
is literally a framed cons. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control

open OracleSpec
open ExactQuantumFactoring.BitStackProgram

def encodeInput (i : PublicInput) : OracleSpec.Word := priceInput i.range i.anchor

def encodeTape (t : Tape) : OracleSpec.Word := frame t.reverseReplies ++ encodeInput t.input

theorem encode_startTape (event : PublicInput ⊕ (Bool × Tape)) :
    Dialogue.inputCode encodeInput encodeTape event = encodeTape (startTape event) := by
  cases event with
  | inl i => rfl
  | inr p => rcases p with ⟨b,t⟩; rfl

theorem encodeInput_length (i : PublicInput) :
    (encodeInput i).length = 2*(i.goods.size + i.range.size + i.anchor.val.size)+3 := by
  simp only [encodeInput,priceInput,List.length_append,encodeNat_length]
  omega

theorem encodeTape_length (t : Tape) :
    (encodeTape t).length = 2*(t.reverseReplies.length + t.input.goods.size +
      t.input.range.size + t.input.anchor.val.size) + 4 := by
  simp only [encodeTape,List.length_append,frame_length,encodeInput_length]
  omega

theorem encodeInput_injective : Function.Injective encodeInput := by
  rintro ⟨n,r,a⟩ ⟨m,s,b⟩ h
  change (encodeNat n ++ encodeNat r) ++ encodeNat a.val =
    (encodeNat m ++ encodeNat s) ++ encodeNat b.val at h
  simp only [List.append_assoc,encodeNat_prefix] at h
  obtain ⟨rfl,rfl,h⟩ := h
  have he := (encodeNat_prefix a.val b.val [] []).mp (by simpa using h)
  have := Fin.ext he.1
  subst b
  rfl

theorem encodeTape_injective : Function.Injective encodeTape := by
  rintro ⟨i,r⟩ ⟨j,s⟩ h
  obtain ⟨hr,hi⟩ := (frame_prefix r s (encodeInput i) (encodeInput j)).mp h
  cases hr
  cases encodeInput_injective hi
  rfl

/-- Length of every returned carry before the next oracle reply. -/
theorem returned_tape_length (solver : PublicSolver) (event : PublicInput ⊕ (Bool × Tape))
    (packet : OracleSpec.Word) (t : Tape) (run : dispatch solver event = .inr (packet,t)) :
    (encodeTape t).length + 2 ≤
      2*(solver t.input).height + 4*t.input.goods.size + 2*t.input.range.size + 4 := by
  obtain ⟨_,q,hq,_⟩ := (dispatch_query_iff solver event packet t).mp run
  obtain ⟨_,_,hn⟩ := pending_of_observe (solver t.input) t.reverseReplies.reverse hq
  rw [List.length_reverse] at hn
  have ha := Nat.size_le_size t.input.anchor.isLt.le
  rw [encodeTape_length]
  omega

/-- This charge includes the tag and the received bit in the *next* dispatch's input
and applies regardless of whether the preceding replies are consistent. -/
theorem resumed_input_length (solver : PublicSolver) (event : PublicInput ⊕ (Bool × Tape))
    (packet : OracleSpec.Word) (t : Tape) (run : dispatch solver event = .inr (packet,t))
    (b : Bool) : (Dialogue.inputCode encodeInput encodeTape (.inr (b,t))).length ≤
      2*(solver t.input).height + 4*t.input.goods.size + 2*t.input.range.size + 4 := by
  simpa [Dialogue.inputCode] using returned_tape_length solver event packet t run

/-- Read the public input and *chronological* replies in a single traversal of the first
frame. The auxiliary stack directly receives the reversal, avoiding a second traversal. -/
def readTape {K : Type} (wire replies ctrl : K) : Program K :=
  .seq (.push ctrl true) (unquoteLoop wire replies ctrl)

theorem readTape_runs {K : Type} [DecidableEq K] (wire replies ctrl : K)
    (hwr : wire ≠ replies) (hwc : wire ≠ ctrl) (hrc : replies ≠ ctrl)
    (memory : Store K) (t : Tape) (hw : memory wire = encodeTape t)
    (hr : memory replies = []) (hc : memory ctrl = []) :
    ∃ state, Runs (readTape wire replies ctrl) memory state (5*t.reverseReplies.length+5) ∧
      state wire = encodeInput t.input ∧ state replies = t.reverseReplies.reverse ∧
      state ctrl = [] ∧ ∀ k, k ≠ wire → k ≠ replies → k ≠ ctrl → state k = memory k := by
  let m := Function.update memory ctrl (true :: memory ctrl)
  have hw' : m wire = quoteBits t.reverseReplies ++ encodeInput t.input := by
    simpa [m, hwc, encodeTape, quoteBits_eq_frame] using hw
  have hc' : m ctrl = [true] := by simp [m,hc]
  have u := unquoteLoop_runs wire replies ctrl hwr hwc hrc t.reverseReplies (encodeInput t.input) m hw' hc'
  let state := Function.update (Function.update (Function.update m wire (encodeInput t.input)) ctrl [])
    replies (t.reverseReplies.reverse ++ m replies)
  refine ⟨state,?_,?_,?_,?_,?_⟩
  · change Runs (.seq _ _) _ _ _
    convert Runs.seq (Runs.push memory ctrl true) u using 1
  · simp [state,hwr,hwc]
  · simp [state,m,hrc,hr]
  · simp [state,hrc.symm]
  · intro k kw kr kc
    simp [state,m,kw,kr,kc]

end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
