import OAI.Computability.NearSquareRoot.KernelComputableDyadic
import OAI.Computability.NearSquareRoot.KernelPass

/-! # Exact conversion between finite-validator and pass coefficients -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelComputableDyadic

def coefficient (x : Code) : KernelPass.Coefficient := ((x.1.1 : ℤ) - x.1.2, x.2)

def ofCoefficient (x : KernelPass.Coefficient) : Code := ((x.1.toNat, (-x.1).toNat), x.2)

@[simp] theorem coefficient_ofCoefficient (x : KernelPass.Coefficient) :
    coefficient (ofCoefficient x) = x := by
  obtain ⟨z,e⟩ := x
  apply Prod.ext
  · change (z.toNat : ℤ) - (-z).toNat = z
    omega
  · rfl

@[simp] theorem value_coefficient (x : Code) : KernelPass.value (coefficient x) = value x := by
  simp [KernelPass.value, coefficient, value]

@[simp] theorem value_ofCoefficient (x : KernelPass.Coefficient) :
    value (ofCoefficient x) = KernelPass.value x := by
  rw [← value_coefficient, coefficient_ofCoefficient]

/-- Read the actual natural number encoding of a pass coefficient. -/
def fromEncodedCoefficient (n : ℕ) : Code := fromSigned n.unpair.1 n.unpair.2

theorem primrec_fromEncodedCoefficient : Primrec fromEncodedCoefficient :=
  primrec_fromSigned.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)

theorem computable_fromEncodedCoefficient : Computable fromEncodedCoefficient :=
  primrec_fromEncodedCoefficient.to_comp

@[simp] theorem fromEncodedCoefficient_encode (x : KernelPass.Coefficient) :
    fromEncodedCoefficient (Encodable.encode x) = ofCoefficient x := by
  obtain ⟨z,e⟩ := x
  simp only [fromEncodedCoefficient, Encodable.encode_prod_val, Nat.unpair_pair]
  cases z with
  | ofNat k =>
    change fromSigned (2*k) e = _
    simp [fromSigned, ofCoefficient]
  | negSucc k =>
    change fromSigned (2*k+1) e = _
    simp [fromSigned, ofCoefficient, Nat.add_div]

end KernelComputableDyadic

end NearSquareRoot
end Computability
end OAI
