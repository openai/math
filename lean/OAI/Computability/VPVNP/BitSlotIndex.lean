import OAI.Computability.VPVNP.SlotPacking
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Binary numbering of wire slots and tags

The shrinking step in Appendix C of *VP and VNP differ over every field*
uses a fixed coordinate block to label a power-of-two set of slots. The
first coordinate is the most significant bit. Encoding and decoding recurse
on the tail, so the same numbering works for both slot and tag blocks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

/-- Read a binary coordinate block in decreasing order of place value. -/
def bitWordFinEquiv : (n : ℕ) → BitWord n ≃ Fin (2 ^ n)
  | 0 => ⟨fun _ ↦ 0, fun _ i ↦ i.elim0, fun _ ↦ Subsingleton.elim _ _,
      fun _ ↦ @Subsingleton.elim (Fin 1) _ _ _⟩
  | n + 1 =>
    (Fin.consEquiv (fun _ : Fin (n + 1) ↦ ZMod 2)).symm.trans
      (((Equiv.refl (Fin 2)).prodCongr (bitWordFinEquiv n)).trans
        (finProdFinEquiv.trans (finCongr (pow_succ' 2 n).symm)))

/-- Encoding the head and tail as a single ordinary binary integer. -/
theorem bitWordFinEquiv_val (n : ℕ) (w : BitWord (n + 1)) :
    (bitWordFinEquiv (n + 1) w).val =
      (bitWordFinEquiv n (Fin.tail w)).val + 2 ^ n * (w 0).val := rfl

/-- Decoding the most significant coordinate divides by the tail's range. -/
theorem bitWordFinEquiv_symm_head (n : ℕ) (i : Fin (2 ^ (n + 1))) :
    ((bitWordFinEquiv (n + 1)).symm i 0).val = i.val / 2 ^ n := rfl

/-- The remaining coordinates decode the residue modulo the size of the tail. -/
theorem bitWordFinEquiv_symm_tail (n : ℕ) (i : Fin (2 ^ (n + 1))) :
    Fin.tail ((bitWordFinEquiv (n + 1)).symm i) =
      (bitWordFinEquiv n).symm ⟨i.val % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩ := rfl

end Compression

end VPVNP
end Computability
end OAI
