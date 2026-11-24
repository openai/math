import OAI.Computability.VPVNP.CompressorRecordsBundleKeys
import OAI.Computability.VPVNP.CompressorSlotOwnerDecode

/-!
# Converting the old source-port order to the role-record order

The shrink role table keeps the residual lane as its last digit. Its preceding
digits are the same normalized source-port key used to sort CD records.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BundleKeys

open Compression

variable {V : Type} {n a g : ℕ}
variable (G : LiftedSlots V (2^a) (BitWord (packingLaneBits a g))) (order : V ≃ Fin n)

/-- Reindex every old actual wire, including thick wires and parallel padding. -/
theorem oldArcIndex_eq_key_lane (e : OldArc V a g) :
    (Slots.oldArcIndex (orderedDyadicPacking G order) order (bitWordFinEquiv (Shrink.J a))
      (bitWordFinEquiv g) e).val =
      keyAt order false e * 2^g + (bitWordFinEquiv g e.1.1.2.2).val := by
  rw [keyAt, Shrink.decode_oldNumber, numericKey]
  dsimp only
  have ht : Shrink.lowNumber (sourcePosition e).1.2 / 2^g =
      (bitWordFinEquiv (Shrink.J a) e.1.1.2.1).val := by
    unfold Shrink.lowNumber Shrink.join
    rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt (Fin.isLt _), Nat.add_zero]
    rfl
  rw [ht]
  let x := (order e.1.1.1).val
  let t := (bitWordFinEquiv (Shrink.J a) e.1.1.2.1).val
  let s := e.1.2.val
  let u := (bitWordFinEquiv (Shrink.colors a) e.2.1).val
  let h := (bitWordFinEquiv a e.2.2).val
  let v := (bitWordFinEquiv g e.1.1.2.2).val
  let d := 2^a
  let C := 2^(Shrink.colors a)
  let J := 2^(Shrink.J a)
  change v + 2^g * ((h+d*u)+C*d*s+d*(C*d)*t+J*(d*(C*d))*x) =
    ((((x*J+t)*d+s)*C+u)*d+h)*2^g+v
  ring

end CompressorRecords.BundleKeys

end VPVNP
end Computability
end OAI
