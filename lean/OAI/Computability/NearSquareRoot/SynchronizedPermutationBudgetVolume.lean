import OAI.Computability.NearSquareRoot.PhysicalWalshXorReserve

/-! # Charging packed row headers and setup to the full permutation stream

The high, middle, and low address fields have widths `A`, `n`, and `B`.
Packing the low field gives each leaf width `2^B * R`. The reserve is chosen
after the fixed program's polynomial degrees for setup and headers are known.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

/-- The low reserve pays the row-program degree, the setup degree, the original
header degree, and the linear cost of a row-address prefix. -/
def selectedRowDegree (degree overhead headerDegree : ℕ) : ℕ :=
  max 1 (max degree (max overhead headerDegree))

/-- A polynomial bound on the per-row time factor fits in the number of rows. -/
theorem rowFactor_le {factor f A k : ℕ} (hf : factor ≤ (k+1)^f)
    (high : payloadBits f k ≤ A) : factor ≤ 2^A := by
  have cap : (k+1)^f ≤ 2^(payloadBits f k) := by
    simpa using payload_capacity f k 1 (by decide)
  exact hf.trans (cap.trans (Nat.pow_le_pow_right (by decide) high))

/-- One additional high-reserve degree absorbs a fixed coefficient for all
address widths with `C ≤ k+1`. -/
theorem rowFactor_with_coefficient {factor C f A k : ℕ} (hf : factor ≤ C*(k+1)^f)
    (hC : C ≤ k+1) (high : payloadBits (f+1) k ≤ A) : factor ≤ 2^A := by
  apply rowFactor_le _ high
  rw [pow_succ']
  exact hf.trans (Nat.mul_le_mul_right _ hC)

open PhysicalWalsh.XorReserve in
/-- The exact setup and forest expressions in `boundedSelectedPrefixRows` fit
a constant multiple of the literal input volume. `C` is the header coefficient.
No dimension of the selected row family enters the multiplicative constant. -/
theorem selectedRows_reserved {A n B k R C header degree overhead H : ℕ}
    (split : A+n+B = k) (hR : 0 < R) (hheader : header ≤ C*(k+1)^H)
    (low : payloadBits (selectedRowDegree degree overhead H) k ≤ B) :
    let l := 2^B*R
    let V := (C+12)*(2^k*R)
    2^(payloadBits degree k)*R ≤ l ∧
    max (2^A) (2^n)*(k+1)^overhead ≤ V ∧
    2^A*(header + 2*A + 2^n*(2*l+2) + 5)+1 ≤ V := by
  let cap d (hd : d ≤ selectedRowDegree degree overhead H) : payloadBits d k ≤ B :=
    (Nat.mul_le_mul_right (Nat.clog 2 (k+1)) hd).trans low
  have scalar d (hd : d ≤ selectedRowDegree degree overhead H) : (k+1)^d ≤ pack B R :=
    polynomial_le_pack le_rfl hR (cap d hd)
  have head := hheader.trans (Nat.mul_le_mul_left C (scalar H (by simp [selectedRowDegree])))
  have lin := scalar 1 (by simp [selectedRowDegree])
  rw [pow_one] at lin
  have p : A ≤ pack B R := by omega
  have row : pack B R ≤ rowWidth n B R := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos n)
  have fits : header + 2*A ≤ (C+2)*rowWidth n B R := by
    rw [Nat.add_mul]
    exact Nat.add_le_add (head.trans (Nat.mul_le_mul_left C row)) (Nat.mul_le_mul_left 2 (p.trans row))
  have cert := packetBounds hR (cap degree (by simp [selectedRowDegree])) fits
    (metadata_le_volume le_rfl hR (cap overhead (by simp [selectedRowDegree])))
  refine ⟨cert.payload, ?_, ?_⟩
  · simpa only [volume, split, Nat.add_assoc] using cert.metadata
  · simpa only [volume, pack, split, Nat.add_assoc] using cert.headerArea

end Controlled

end NearSquareRoot
end Computability
end OAI
