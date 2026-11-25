import OAI.Computability.NearSquareRoot.CRTControlledFlatSwaps
import OAI.Computability.NearSquareRoot.CRTPositionProgram

/-! # Native binary address semantics for the physical instruction stream -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram
open IntegerMultiplication IntegerMultiplication.Adic IntegerMultiplication.Strip

noncomputable def nativeWord (k : ℕ) : Block 2 k ≃ (Fin k → Bool) := by
  letI : Fintype (Block 2 k) := Fintype.ofEquiv (Fin (2^k)) (flatAddress 2 k).symm
  apply Equiv.ofBijective prefixBit
  apply (Fintype.bijective_iff_injective_and_card _).2
  exact ⟨prefixBit_injective k,by rw [Fintype.card_congr (flatAddress 2 k)]; simp⟩

@[simp] theorem nativeWord_apply (k : ℕ) (a : Block 2 k) : nativeWord k a = prefixBit a := rfl

noncomputable def nativeOp (k G : ℕ) (q : Op) (a : Block 2 k) : Block 2 k :=
  (nativeWord k).symm (act G (prefixBit a) q)

@[simp] theorem nativeOp_bits (k G : ℕ) (q : Op) (a : Block 2 k) :
    prefixBit (nativeOp k G q a) = act G (prefixBit a) q :=
  (nativeWord k).apply_symm_apply _

theorem nativeOp_twice (k G : ℕ) (q : Op) : Function.Involutive (nativeOp k G q) := by
  intro a
  apply prefixBit_injective k
  rw [nativeOp_bits,nativeOp_bits,act_twice]

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
