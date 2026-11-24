import OAI.Computability.VPVNP.SliceArithmeticCallPorts
import OAI.Computability.VPVNP.SliceArithmeticMultiplyReverse

/-! # Installing the digit-order conversion in a reusable multiplication call -/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmetic.MultiplyCall

open RAMTape BurstRAM HornerControl
open SliceArithmeticRound (packed)
open SliceArithmeticStreamRow (state)

private def orderPort : SliceArithmeticMultiplyReverse.Port → Port
  | .query => .inr .query
  | .digits => localStream (.outer .digits)
  | .old => localStream .old
  | .marker => localStream (.outer .rows)
  | .staging => reg 4
  | .zero => persistent
  | .scratch => localStream .scratch

private theorem orderPort_injective : Function.Injective orderPort := by
  intro i j h
  cases i <;> cases j <;> simp_all [orderPort, reg, localStream, persistent]

/-- Consume the query in increasing degree order to prepare high-degree-first Horner digits and
a zero accumulator. -/
def orderInput : FiniteRoutine Port := SliceArithmeticMultiplyReverse.prepare.onPorts orderPort

theorem orderInput_runs {p e w : ℕ} [NeZero p] (cb bb : List Bool) (a : Vector p e) :
    let ab := packed w (List.ofFn a)
    let digits := packed w (List.ofFn a).reverse
    let zeros := packed w (List.ofFn (zero p e))
    let r := initialRegisters p w
    orderInput.Runs (e * (15*w+7) + 1 + (10*w+4))
      (workspace (state r (streams [] [] [] [] (extra cb bb e [] e e))) (external p e w cb ab bb))
      (workspace (state r (streams zeros [] [] [] (extra cb bb e digits e 0))) (external p e w cb [] bb)) := by
  intro ab digits zeros r
  let words := (List.ofFn a).map (Word.limb w)
  have hin : SliceArithmeticMultiplyReverse.pack words = ab := by
    simp only [SliceArithmeticMultiplyReverse.pack, words, ab, packed, List.flatMap_map]
  have hout : SliceArithmeticMultiplyReverse.pack words.reverse = digits := by
    rw [show words.reverse = (List.ofFn a).reverse.map (Word.limb w) from List.map_reverse.symm]
    simp only [SliceArithmeticMultiplyReverse.pack, digits, packed, List.flatMap_map]
  have hz : SliceArithmeticMultiplyReverse.pack (List.replicate e (0 : BurstRAM.Word w)) = zeros := by
    have hv : List.ofFn (zero p e) = List.replicate e (0 : Fin p) := List.ofFn_const e 0
    simp [zeros, hv, packed, SliceArithmeticMultiplyReverse.pack, Word.limb, List.flatMap_replicate]
  have run := SliceArithmeticMultiplyReverse.prepare_runs words [] [] [] (0 : BurstRAM.Word w)
  rw [show words.length = e by simp [words], hin, hout, hz] at run
  simp only [List.append_nil] at run
  apply SliceArithmeticMultiplyReverse.prepare.runs_onPorts_framed orderPort_injective run
  · intro i
    cases i <;> rfl
  · intro i
    cases i <;> rfl
  · rintro ((k | k) | k) h
    · rfl
    · cases k with
      | old => exact (h .old rfl).elim
      | outer x =>
        cases x with
        | digits => exact (h .digits rfl).elim
        | rows => exact (h .marker rfl).elim
        | _ => rfl
      | _ => rfl
    · cases k with
      | query => exact (h .query rfl).elim
      | _ => rfl

end SliceArithmetic.MultiplyCall

end VPVNP
end Computability
end OAI
