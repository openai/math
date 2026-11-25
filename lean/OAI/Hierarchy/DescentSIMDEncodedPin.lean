import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Bit access at the native offset of an encoded SIMD cell -/
namespace Hierarchy.DescentSixParty.PackedCensus
open DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section

/-- Little-endian block encoding. All numeric offsets here are bounded
by one local occurrence description. -/
theorem encode_pin {a M : ℕ} (row : Fin M→Cell a) (i : Fin M) (j : Fin a) :
    (encode a M row).val.testBit (j.val+a*i.val)=(row i).val.testBit j.val := by
  have inside : j.val+a*i.val<a*(i.val+1) := by rw [Nat.mul_add,Nat.mul_one];omega
  have h:=congrArg (fun n : ℕ=>n.testBit j.val) (digit_encode row i)
  simpa [digit,Nat.testBit_div_two_pow,Nat.testBit_mod_two_pow,inside,Nat.add_comm] using h

end
end Hierarchy.DescentSixParty.PackedCensus

end OAI
