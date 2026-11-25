import OAI.Computability.NearSquareRoot.CRTPositionDispatchSum
import OAI.Computability.NearSquareRoot.CRTPositionPackedDispatch
import OAI.Computability.NearSquareRoot.CRTPositionChunkSwap
import OAI.Computability.NearSquareRoot.CRTPositionSingletonStage

/-! # Uniform four-way physical interpretation of the position bytecode -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Adic IntegerMultiplication.Staff
open IntegerMultiplication.Strip IntegerMultiplication.Loom IntegerMultiplication.Packed

private theorem nativeFrom {k G : ℕ} (q : Op) (g : Block 2 k → Block 2 k)
    (h : ∀ y, prefixBit (g y) = act G (prefixBit y) q) (y : Block 2 k) :
    nativeOp k G q y = g y :=
  prefixBit_injective k ((nativeOp_bits ..).trans (h y).symm)

/-- One physical P192 command decodes the requested opcode from the regime header
and reindexes the complete row of records by its native address action. -/
theorem opcodeStage {ρ : ℝ} (hρ : 1/2 < ρ) : OpFamily ρ id := by
  apply opFamily_sum
  · intro X R l k q hk hq valid U u hu f
    have same (x : X) := nativeFrom (G:=guardWidth (k x)) (k:=k x) (swapChunks (q x))
      (swapNative (k x) (q x)) (swapNative_bits (k x) (q x).1 (q x).2 (valid x))
    simpa only [Function.comp_apply,id_eq,←same] using swapNativeStage q k hq hk hρ u hu f
  apply opFamily_sum
  · intro X R l k q hk hq valid U u hu f
    have supplied : R.Has (fun x => packed (q x)) := hq.thenDo (poly_left.compose poly_right)
    have same (x : X) := nativeFrom (G:=guardWidth (k x)) (k:=k x) (packed (q x))
      (packedPass (q x)) (packedPass_bits (q x) (valid x))
    simpa only [Function.comp_apply,id_eq,←same] using packedPassStage k q hk supplied valid ρ hρ u hu f
  apply opFamily_sum
  · intro X R l k q hk hq valid U u hu f
    have same (x : X) := nativeFrom (G:=guardWidth (k x)) (k:=k x) (highCnot (q x))
      (highCnotBlock (q x) (valid x)) (highCnotBlock_bits (q x) (valid x))
    simpa only [Function.comp_apply,id_eq,←same] using
      highCnotStage k q hk hq (fun x => guardWidth (k x)) valid ρ (by linarith) u hu f
  · intro X R l k q hk hq valid U u hu f
    have same (x : X) := nativeFrom (G:=guardWidth (k x)) (k:=k x) (tailSwap (q x))
      (tailBlock (q x) (valid x)) (tailBlock_bits (q x) (valid x))
    simpa only [Function.comp_apply,id_eq,←same] using
      tailStage k q hk hq (fun x => guardWidth (k x)) valid ρ (by linarith) u hu f

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
