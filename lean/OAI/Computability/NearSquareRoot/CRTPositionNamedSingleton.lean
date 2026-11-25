import OAI.Computability.NearSquareRoot.CRTPositionOpcodeCall
import OAI.Computability.NearSquareRoot.CRTControlledEffectiveRectangle

/-! # Fixed native position commands for a singleton CNOT and a tail swap -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram

open IntegerMultiplication Code Adic Staff Strip Loom
open private nativeFrom from OAI.Computability.NearSquareRoot.CRTPositionOpcodeStage

private theorem fixedOperand {T : Type} [Codec T] (wrap : T → Op) (op : OpFamily 0 wrap)
    (payload : (Call.regime wrap).Has Call.operand) :
    ∃ t : Effective.Template, ∀ c ρ, 0 ≤ ρ → Effective.rectContract c ρ → OpAt (t.eval c) ρ wrap := by
  apply Effective.Program.fixed
  have execute := op (R := Call.regime wrap) Call.k Call.operand Call.widthHas payload Call.legal
    (fun x => Series.natural x.width) (l := Call.width) (fun _ => (Series.count_natural _).le) Call.data
  exact execute

/-- A single command computes the upper singleton CNOT for every legal pair
of positions and every payload. -/
theorem highCnotTemplate :
    ∃ t : Effective.Template, ∀ c ρ, 0 ≤ ρ → Effective.rectContract c ρ → OpAt (t.eval c) ρ highCnot := by
  apply fixedOperand highCnot _ (highPayload_has Call.opcodeHas)
  intro X R l k q hk hq valid U u hu f
  have same (x : X) := nativeFrom (G := guardWidth (k x)) (k := k x) (highCnot (q x))
    (highCnotBlock (q x) (valid x)) (highCnotBlock_bits (q x) (valid x))
  simpa only [← same] using highCnotStage k q hk hq (fun x => guardWidth (k x)) valid 0 le_rfl u hu f

/-- A single command exchanges the two indicated tail positions while
retaining the order of the records at all other positions. -/
theorem tailSwapTemplate :
    ∃ t : Effective.Template, ∀ c ρ, 0 ≤ ρ → Effective.rectContract c ρ → OpAt (t.eval c) ρ tailSwap := by
  apply fixedOperand tailSwap _ (tailPayload_has Call.opcodeHas)
  intro X R l k q hk hq valid U u hu f
  have same (x : X) := nativeFrom (G := guardWidth (k x)) (k := k x) (tailSwap (q x))
    (tailBlock (q x) (valid x)) (tailBlock_bits (q x) (valid x))
  simpa only [← same] using tailStage k q hk hq (fun x => guardWidth (k x)) valid 0 le_rfl u hu f

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
