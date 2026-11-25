import OAI.Computability.NearSquareRoot.CRTTableStageStream
import OAI.Computability.NearSquareRoot.CRTTableSetup

/-! # The finite physical machine which produces the whole CRT stage program -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable
open IntegerMultiplication.Code

/-- From only the direction and unary address width, generate the mixed-radix
box, its padded common block width, the balanced CRT depths, and all switch
stage descriptors, with positions and table-program tags. -/
def stageProgram (p : Bool × Tally) :=
  headerStream (p.1,tally (BoxScale.width p.2.length),BoxProgram.encoded p.2)

theorem stageProgram_poly : Poly stageProgram := by
  have width := (Easy.snd (X := Bool) (Y := Tally)).poly.compose BoxParameterTask.width_poly
  have box := (Easy.snd (X := Bool) (Y := Tally)).poly.compose BoxProgram.encoded_poly
  exact (Easy.fst.poly.pair (width.pair box)).compose headerStream_poly

theorem stageProgram_length (k : ℕ) (inv : Bool) :
    (stageProgram (inv,tally k)).length =
      Nat.clog 2 (CoprimeBox.box k).length * (2*BoxScale.width k) := by
  simp only [stageProgram,tally_length,headerStream_eq,List.length_map,switchOrder_length]
  simp [BoxProgram.encoded]

private theorem programInput_size : Dom (fun p : Bool × ℕ => p.2)
    (fun p => size (p.1,tally p.2)) := by
  refine ⟨1,4,fun p => ?_⟩
  simp only [size_prod,size_bit,size_tally,tally_length,pow_one]
  omega

/-- One machine emits the full program with polynomially many tape steps
and visited cells in address width, including the parameter search. -/
theorem stageProgram_machine : PolyTreeMachine (fun p : Bool × ℕ => p.2)
    (fun p => send (p.1,tally p.2)) (fun p => send (stageProgram (p.1,tally p.2))) :=
  polyTreeMachine_of_BT (stageProgram_poly.on programInput_size) programInput_size

end CRTTable

end NearSquareRoot
end Computability
end OAI
