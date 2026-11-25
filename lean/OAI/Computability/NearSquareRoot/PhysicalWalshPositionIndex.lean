import OAI.Computability.NearSquareRoot.CRTPositionProgramNative
import OAI.Computability.NearSquareRoot.SynchronizedBitAddress

/-! # Numeric read direction of the native position program

A native instruction reads each output position through its position table.
Reading a routed payload applies the inverse native map. The resulting numeric
address moves source bits to the destinations specified in the table.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.PositionCloth

open IntegerMultiplication.Adic Controlled Controlled.PositionProgram

private theorem address_of_reads {k : ℕ} (p : Equiv.Perm (Fin k)) (a b : Block 2 k)
    (read : prefixBit b = prefixBit a ∘ p.symm) :
    flatAddress 2 k b = BoxFin.bitAddress p (flatAddress 2 k a) := by
  apply (BoxFin.addressDigits k).injective
  funext j
  obtain ⟨i,rfl⟩ := p.surjective j
  change (flatAddress 2 k b).val.testBit (p i).val =
    (BoxFin.bitAddress p (flatAddress 2 k a)).val.testBit (p i).val
  rw [BoxFin.bitAddress_testBit,flatAddress_val,flatAddress_val,← prefixBit_number,← prefixBit_number]
  simpa only [Function.comp_apply,Equiv.symm_apply_apply] using congrFun read (p i)

/-- Numeric read address seen by a payload after running the complete
position permutation on its native binary blocks. -/
theorem flat_native_symm {k : ℕ} (p : Equiv.Perm (Fin k)) (a : Block 2 k) :
    flatAddress 2 k ((permuteNative p).symm a) = BoxFin.bitAddress p (flatAddress 2 k a) :=
  address_of_reads p a _ (permuteNative_symm_bits p a)

/-- Numeric address of the native forward position update. -/
theorem flat_native {k : ℕ} (p : Equiv.Perm (Fin k)) (a : Block 2 k) :
    flatAddress 2 k (permuteNative p a) = BoxFin.bitAddress p.symm (flatAddress 2 k a) :=
  address_of_reads p.symm a _ (permuteNative_bits p a)

end PhysicalWalsh.PositionCloth

end NearSquareRoot
end Computability
end OAI
