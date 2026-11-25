import OAI.Optimization.LinearProgramming.PriceGame.ControlEncoding

/-! The inner procedure receives a unary copy of the dimension before the immutable public
header. The one-time bootstrap obtains it from the original binary input. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control

open OracleSpec
open ExactQuantumFactoring.BitStackProgram

def unaryGoods (i : PublicInput) : List Bool := List.replicate i.goods true

def eiPad (i : PublicInput) : OracleSpec.Word := frame (unaryGoods i) ++ encodeInput i

def ecPad (t : Tape) : OracleSpec.Word := frame t.reverseReplies ++ eiPad t.input

theorem inputCode_pad (event : PublicInput ⊕ (Bool × Tape)) :
    Dialogue.inputCode eiPad ecPad event = ecPad (startTape event) := by
  cases event <;> rfl

theorem eiPad_length (i : PublicInput) :
    (eiPad i).length = 2*i.goods + 1 + (encodeInput i).length := by
  simp [eiPad,frame_length,unaryGoods]

theorem ecPad_length (t : Tape) :
    (ecPad t).length = (encodeTape t).length + (2*t.input.goods+1) := by
  simp only [ecPad,encodeTape,List.length_append,eiPad_length]
  omega

private theorem eiPad_is_pair (i : PublicInput) :
    prodCode id id (unaryGoods i, encodeInput i) = eiPad i := by
  simp [prodCode,pairBits,quoteBits_eq_frame,eiPad]

private theorem ecPad_is_pair (t : Tape) :
    prodCode id eiPad (t.reverseReplies,t.input) = ecPad t := by
  simp [prodCode,pairBits,quoteBits_eq_frame,ecPad]

/-- A real finite-stack program extracting the physically supplied unary N cells. -/
noncomputable def unaryGoodsP : Procedure eiPad id unaryGoods :=
  ((Procedure.first id id).precompose (fun i : PublicInput => (unaryGoods i,encodeInput i))).congrEncoding
    eiPad_is_pair (fun _ => rfl)

/-- The literal frozen three-field binary header after removal of its unary padding. -/
noncomputable def publicInputP : Procedure eiPad id encodeInput :=
  ((Procedure.second id id).precompose (fun i : PublicInput => (unaryGoods i,encodeInput i))).congrEncoding
    eiPad_is_pair (fun _ => rfl)

noncomputable def priorRepliesP : Procedure ecPad id Tape.reverseReplies :=
  ((Procedure.first id eiPad).precompose (fun t : Tape => (t.reverseReplies,t.input))).congrEncoding
    ecPad_is_pair (fun _ => rfl)

noncomputable def replayRepliesP : Procedure ecPad id (fun t => t.reverseReplies.reverse) :=
  Procedure.reverse.comp priorRepliesP

noncomputable def tapeInputP : Procedure ecPad eiPad Tape.input :=
  ((Procedure.second id eiPad).precompose (fun t : Tape => (t.reverseReplies,t.input))).congrEncoding
    ecPad_is_pair (fun _ => rfl)

end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
