import OAI.Computability.VPVNP.PairSimulationLeafSuccessorCode

/-!
# Successor fields in the serialized incident buffer

At cursor zero every successor mask selects the flip arc for a send. A
receive selects that arc exactly for the mask reaching the last cursor bit.
The first site's absent receive and the final site's absent send each supply
one entire zero field.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafSuccessorFields

open CursorNetwork CursorRouting RAMLayout

variable {D H w : ℕ} [NeZero D]

private theorem mask_last (j : Fin D) :
    (systemMask (.inl j)).val.testBit (-1 : Fin D).val = decide (j.val = D-1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne D)
  simp only [systemMask, Fin.coe_neg_one, Nat.testBit_two_pow_sub_one]
  simp only [show n < j.val + 1 ↔ j.val = n.succ - 1 by have := j.isLt; omega]

/-- The outgoing and incoming successor blocks loaded by the native RAM
are the corresponding slices of the site's decoded cursor-zero input. -/
theorem succBits_eq (recv : Bool) (v : Site D) (buf : Buffers D H w) :
    succBits recv v buf = List.ofFn fun j : Fin (8*w) =>
      incidentBuffer (0,v) buf (offset D H w (.inl (if recv then 1 else 0, j))) := by
  unfold succBits LeafIncidentLoad.Field
  apply congrArg List.ofFn
  funext j
  simp only [incidentBuffer, decodeIncident, Function.comp_apply, Equiv.symm_apply_apply]
  cases recv with
  | false =>
    by_cases hv : v.val + 1 < 2^D
    · simp [selected, active, sender, sourceOffset, port, useSide, decodeSlot, hv, systemMask, readBuffer]
      exact congrArg (buf (.outgoing true)) (Fin.ext (ramFieldOffset_successor _ _).symm)
    · simp [selected, active, port, decodeSlot, hv]
  | true =>
    by_cases hv : 0 < v.val
    · simp [selected, active, sender, sourceOffset, port, useSide, decodeSlot, hv, mask_last, readBuffer]
      exact congrArg (buf _) (Fin.ext (ramFieldOffset_successor _ _).symm)
    · simp [selected, active, port, decodeSlot, hv]

end PairSimulation.LeafSuccessorFields

end VPVNP
end Computability
end OAI
