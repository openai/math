import OAI.Computability.NearSquareRoot.PhysicalWalshElementaryIndex
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeXorBits

/-! # Partial aligned XOR on the physical lane during the elementary sweep -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.ElementarySweep

open PhysicalWalsh
open ElementarySchedule (slotWidth)

def address {a : ℕ} (src dst : Fin (a+1)) (s : Shape) (j n : ℕ) :=
  let L := slotWidth (a+1) s
  XorBits.window (XorBits.offset L src) (XorBits.offset L dst) j (n/s.suff)*s.suff+n%s.suff

@[simp] theorem address_zero {a : ℕ} (src dst : Fin (a+1)) (s : Shape) (n : ℕ) :
    address src dst s 0 n = n := by simp [address,Nat.div_add_mod']

theorem address_full {a : ℕ} (src dst : Fin (a+1)) (ne : src ≠ dst) (s : Shape) (n : ℕ) :
    address src dst s (slotWidth (a+1) s) n = xorIndex a (dst,src) s n :=
  (XorBits.xorIndex_eq (dst,src) ne.symm s n).symm

theorem address_step {a : ℕ} (src dst : Fin (a+1)) (ne : src ≠ dst) (s : Shape)
    (j : Fin (slotWidth (a+1) s)) (n : ℕ) :
    address src dst s (j.val+1) n = address src dst s j
      (ElementaryGate.natAction (ElementarySchedule.gap src dst s j) (ElementarySchedule.suff src dst s j)
        (ElementaryIndex.rewire src dst) n) := by
  let L := slotWidth (a+1) s
  let d := XorBits.offset L dst
  let c := XorBits.offset L src
  let u := XorBits.single c d j (n/s.suff)
  rw [ElementaryIndex.natAction_bits src dst ne]
  change XorBits.window c d (j.val+1) (n/s.suff)*s.suff+n%s.suff =
    XorBits.window c d j ((u*s.suff+n%s.suff)/s.suff)*s.suff+(u*s.suff+n%s.suff)%s.suff
  rw [Nat.mul_comm u s.suff,Nat.mul_add_div s.suff_pos,Nat.div_eq_of_lt (Nat.mod_lt n s.suff_pos),
    Nat.add_zero,Nat.mul_add_mod,Nat.mod_mod]
  exact congrArg (fun z => z*s.suff+n%s.suff)
    (XorBits.window_single (XorBits.offset_apart ne L) j.isLt (n/s.suff)).symm

theorem slotWidth_le_scale (a : ℕ) (s : Shape) : slotWidth (a+1) s ≤ Header.scale (a+1) s := by
  have h := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (Nat.succ_pos a) (Nat.sub_le s.level 1))
  change slotWidth (a+1) s ≤ grow (a+1) s.level at h
  rw [Header.scale_exact]; omega

end PhysicalWalshNode.ElementarySweep

end NearSquareRoot
end Computability
end OAI
