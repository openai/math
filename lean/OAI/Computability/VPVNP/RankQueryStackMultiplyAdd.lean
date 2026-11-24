import OAI.Computability.VPVNP.RankQueryStackAccumulate
import OAI.Computability.VPVNP.RankQueryStackEngineSpec

/-!
# The Schur stack machine's multiply-and-add callback

After the right child returns, the live frame contains its parent's
accumulator and the saved left factor. The callback mounts the coefficient
arithmetic on these fields and the returned value. It then clears the two
consumed factors and resumes the parent's scan with its updated accumulator.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Engine.MultiplyAdd

open RAMTape SliceArithmetic

set_option backward.isDefEq.respectTransparency false in
/-- Persistent arithmetic inputs for a Schur product, consisting of the prime, a zero word, the
extension degree, and the reduction coefficients. -/
inductive Advice where
  | prime | zeroWord | degree | coeff
  deriving DecidableEq, Fintype

/-- Private stacks and persistent arithmetic inputs for the multiply-and-add callback. -/
abbrev Aux := MultiplyAccumulate.Private ⊕ Advice

variable {K : Type} {n U Z p e w v : ℕ}

/-- Connect the arithmetic routine to its auxiliary stacks and to the Schur frame's left
operand, returned right operand, and accumulator. -/
def port (f : Aux → K) : MultiplyAccumulate.Port → Engine.Port K
  | .inl i => .aux (f (.inl i))
  | .inr .prime => .aux (f (.inr .prime))
  | .inr .zeroWord => .aux (f (.inr .zeroWord))
  | .inr .degree => .aux (f (.inr .degree))
  | .inr .coeff => .aux (f (.inr .coeff))
  | .inr .left => .frame (.inl 9)
  | .inr .returned => .result
  | .inr .acc => .frame (.inl 8)

theorem port_injective {f : Aux → K} (hf : Function.Injective f) : Function.Injective (port f) := by
  rintro (i|i) (j|j) h
  · exact congrArg Sum.inl (Sum.inl.inj (hf (Engine.Port.aux.inj h)))
  · cases j <;> simp_all [port, hf.eq_iff]
  · cases i <;> simp_all [port, hf.eq_iff]
  · cases i <;> cases j <;> simp_all [port, hf.eq_iff]

/-- Initial arithmetic stack contents, with empty private stacks and the field parameters
encoded at limb width `v`. -/
def expected (v : ℕ) (c : Vector p e) : Stacks Aux
  | .inl _ => []
  | .inr .prime => BurstRAM.wordBits (Fin.ofNat (2 ^ v) p)
  | .inr .zeroWord => BurstRAM.wordBits (0 : BurstRAM.Word v)
  | .inr .degree => List.replicate e true
  | .inr .coeff => SliceArithmeticRound.packed v (List.ofFn c)

/-- The other auxiliary ports are available for the query description and
the controller's remaining subroutines. -/
def Ready (f : Aux → K) (v : ℕ) (c : Vector p e) (aux : Stacks K) := ∀ i, aux (f i) = expected v c i

/-- Add the product of the saved left factor and the returned right factor to the parent
accumulator, then clear both factors. -/
def machine (f : Aux → K) : FiniteRoutine (Engine.Port K) :=
  ((MultiplyAccumulate.machine.onPorts (port f)).followedBy (CallClear.clear (.frame (.inl 9)))).followedBy
    (CallClear.clear .result)

/-- Step bound for the multiply-and-add callback, including the cost of clearing two scalars of
`e*v` bits. -/
def callCap (e v : ℕ) := MultiplyAccumulate.callCap e v + 2 * (e * v + 1)

variable [DecidableEq K] [Fact p.Prime] [NeZero e] {c : Vector p e}

/-- The precise multiply-and-add execution required by the engine's contracts.
The stored stack history and the entire auxiliary bank are preserved. -/
theorem machine_runs (f : Aux → K) (hf : Function.Injective f) (hw : Word.workingWidth p ≤ v)
    (w : ℕ) (q : Key n U Z) (k : ℕ) (acc left returned : Scalar c)
    (fs : List (F n U Z c)) (aux : Stacks K) (hready : Ready f v c aux) :
    ∃ t ≤ callCap e v, (machine f).Runs t
      (store (popped w v (.right q k acc left)) (history w v fs) [] (scalar v returned) aux)
      (atControl w v (.scan q k (acc + left * returned)) fs aux) := by
  let result := acc + left * returned
  let pre := store (popped w v (.right q k acc left)) (history w v fs) [] (scalar v returned) aux
  let mid := Function.update pre (.frame (.inl 8)) (scalar v result)
  let consumed := Function.update mid (.frame (.inl 9)) []
  obtain ⟨t, ht, mac⟩ := Scalar.accumulate_runs hw c left returned acc
  have hmac : (MultiplyAccumulate.machine.onPorts (port f)).Runs t pre mid := by
    apply MultiplyAccumulate.machine.runs_onPorts_framed (port_injective hf) mac
    · rintro (i|i)
      · cases i <;> exact hready _
      · cases i with
        | prime => exact hready (.inr .prime)
        | zeroWord => exact hready (.inr .zeroWord)
        | degree => exact hready (.inr .degree)
        | coeff => exact hready (.inr .coeff)
        | left | acc | returned => rfl
    · rintro (i|i)
      · cases i <;> exact (Function.update_of_ne (by simp [port]) ..).trans (hready _)
      · cases i with
        | prime => exact (Function.update_of_ne (by simp [port]) ..).trans (hready (.inr .prime))
        | zeroWord => exact (Function.update_of_ne (by simp [port]) ..).trans (hready (.inr .zeroWord))
        | degree => exact (Function.update_of_ne (by simp [port]) ..).trans (hready (.inr .degree))
        | coeff => exact (Function.update_of_ne (by simp [port]) ..).trans (hready (.inr .coeff))
        | left | returned => rfl
        | acc => exact Function.update_self ..
    · intro i hi
      exact Function.update_of_ne (Ne.symm (hi (.inr .acc))) ..
  have leftLen : (mid (.frame (.inl 9))).length = e*v := scalar_length v left
  have retLen : (consumed .result).length = e*v := scalar_length v returned
  have eraseLeft := CallClear.clear_runs (.frame (.inl 9)) mid
  have eraseRet := CallClear.clear_runs .result consumed
  rw [leftLen] at eraseLeft
  rw [retLen] at eraseRet
  have hfinal : Function.update consumed .result [] = atControl w v (.scan q k result) fs aux := by
    funext j
    cases j with
    | frame j => cases j with
      | inl i => fin_cases i <;> rfl
      | inr i => rfl
    | aux | result | condition => rfl
  rw [hfinal] at eraseRet
  exact ⟨_, by unfold callCap; omega, (hmac.followedBy eraseLeft).followedBy eraseRet⟩

end RankQuery.Stack.Engine.MultiplyAdd

end VPVNP
end Computability
end OAI
