import OAI.Hierarchy.DescentTerminalBookBitPrice
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # Total padded shelves for terminal book lookups and printed weights -/
namespace Hierarchy.DescentTerminalLocalPortBook.Book
open DescentDyadicSpan
open scoped BigOperators
noncomputable section

/-- The independent count and primitive-port tables, the route request
table with both row coordinates, its two row-weight tables, and the six
physical mixed-radix weights in the printed declaration. -/
def lookupWords (V A W : ℕ) :=
  let M:=V*A
  let a:=tokenBits M
  let bytes:=Bytes 4 V M A a
  2*span bytes+span (W*(W*bytes))+2*span W+
    ∑ i : Fin 6,span (capacities 4 V M A a i)

theorem lookup_envelope (V A W n : ℕ) (node : V≤n) (incidence : V*A≤n)
    (operand : A≤n) (width : W≤n) (positive : 0<n) :
    lookupWords V A W ≤ 2^(128*(n*n)) := by
  let M:=V*A
  let a:=tokenBits M
  let bytes:=Bytes 4 V M A a
  have bits:=bytes_envelope V A n node incidence operand positive
  have live : 0<bytes := by dsimp only [bytes,Bytes];positivity
  have six : (∑ i : Fin 6,span (capacities 4 V M A a i))≤6*(2*bytes+1) := by
    calc
      _ ≤ ∑ _ : Fin 6,(2*bytes+1) := by
        apply Finset.sum_le_sum
        intro i _
        exact (span_le _).trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (capacity_fit 4 V M A a i)) _)
      _ = _ := by simp
  let area:=n*n*bytes
  have areaB : bytes≤area := Nat.le_mul_of_pos_left _ (Nat.mul_pos positive positive)
  have nn : n≤n*n:=Nat.le_mul_of_pos_right _ positive
  have areaW : W≤area:=width.trans (nn.trans (Nat.le_mul_of_pos_right _ live))
  have request : W*(W*bytes)≤area := by
    rw [←Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul width width)
  have one:=span_le bytes
  have req:=span_le (W*(W*bytes))
  have row:=span_le W
  have total : lookupWords V A W≤64*area := by
    change 2*span bytes+span (W*(W*bytes))+2*span W+
      (∑i : Fin 6,span (capacities 4 V M A a i))≤64*area
    omega
  calc
    _ ≤ 64*(n*n)*bytes := by simpa only [area,Nat.mul_assoc] using total
    _ ≤ 2^6*2^(n*n)*2^(60*(n*n)) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by decide : 64≤2^6) Nat.lt_two_pow_self.le) bits
    _ = 2^(6+n*n+60*(n*n)) := by rw [pow_add,pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith [Nat.mul_pos positive positive])

end
end Hierarchy.DescentTerminalLocalPortBook.Book

end OAI
