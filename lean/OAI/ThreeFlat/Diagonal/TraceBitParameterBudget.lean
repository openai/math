import OAI.ThreeFlat.Diagonal.TraceDiagonalBudget
import OAI.ThreeFlat.Diagonal.TracePortCardinality
import OAI.ThreeFlat.RAM.FixedTraceImage

namespace OAI
/-! # Bit length of the fixed trace parameter image -/

namespace ThreeFlat.Diagonal.TraceStaticRow

/-- Absolute coefficient in the bit bound for eleven words per gate and port. -/
def bitParameterConstant : ℕ := 176 * (10^26 * 17^14 + 400 * 18^3)

variable {F : Type*} [CommRing F] [Fintype F] {u d : ℕ}

/-- The count includes the actual gate and incidence words of the fixed image.
Each of its words has exactly `16*u^10` bits. -/
theorem diagonal_bitParameterLength
    (hu : 128 ≤ u) (hq : Fintype.card F ≤ u) (hd : d ≤ 15*u^10)
    (hF : Fintype.card F ≤ 2^(16*u^10)) (hw : 3 ≤ 16*u^10+1) (hp : u ≤ 2^(16*u^10+1))
    (base f : ℕ) (st : Computability.VPVNP.BurstRAM.Word (16*u^10)) :
    16*u^10 * RAM.FixedTraceImage.count (gateTable hF hw hp base f st u u d) ≤
      bitParameterConstant * u^150 := by
  have cells := diagonal_gateTable hu hq hd hF hw hp base f st
  have ports : Fintype.card (Port (16*u^10) u u u d) ≤ (400*18^3)*u^140 := by
    rw [card_ports]
    exact (diagonal_ports_bound hu hd).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega : 0 < u) (by decide : 30 ≤ 140)))
  unfold RAM.FixedTraceImage.count
  calc
    _ ≤ (16*u^10) * (11 * ((10^26*17^14)*u^140 + (400*18^3)*u^140)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.add_le_add cells ports))
    _ = _ := by unfold bitParameterConstant; ring

/-- At the absolute coefficient threshold the fixed image occupies at most
`u^151` bits. Both estimates are uniform over the machine time and base address. -/
theorem diagonal_bitParameterLength_le_pow
    (hu : 128 ≤ u) (hq : Fintype.card F ≤ u) (hd : d ≤ 15*u^10)
    (hF : Fintype.card F ≤ 2^(16*u^10)) (hw : 3 ≤ 16*u^10+1) (hp : u ≤ 2^(16*u^10+1))
    (base f : ℕ) (st : Computability.VPVNP.BurstRAM.Word (16*u^10)) (large : bitParameterConstant ≤ u) :
    16*u^10 * RAM.FixedTraceImage.count (gateTable hF hw hp base f st u u d) ≤ u^151 := by
  exact (diagonal_bitParameterLength hu hq hd hF hw hp base f st).trans <| calc
    bitParameterConstant * u^150 ≤ u * u^150 := Nat.mul_le_mul_right _ large
    _ = _ := by ring

end ThreeFlat.Diagonal.TraceStaticRow

end OAI
