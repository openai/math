import OAI.Hierarchy.DescentPackedWalshStatePrice
import OAI.Hierarchy.DescentPackedWalshLiteralBill

namespace OAI
/-! # Separating the physical reset estimator's host words, short fields, and common controller -/
namespace Hierarchy.DescentPackedWalsh.EstimatorArena
open DescentPackedWalsh DescentPackedWalshReduction
variable (E : EstimatorArena)

/-- Number of native words billed per census row, including the global reduction's site scans. -/
def hostUnit (k K : ℕ) := K*(180*k+28+(k+1)*(94+6+2008)+2+6*k+2008)

/-- Total cost per census row and cube entry. Only its short precision appears here. -/
def fieldUnit (k b K : ℕ) :=
  K*(16*b*(180*k+28+(k+1)*94+2+6*k)+(k+1)*(96*b+25600*(b+1))+25600*(b+1))

section
local notation "k" => E.dim
local notation "N" => E.hosts
local notation "h" => E.payload
local notation "b" => E.precision

/-- Once per estimator, including the fixed decoder dictionaries, global solves, and widening
of the final few active rows of the dyadic reduction. -/
def commonBill (W K : ℕ) :=
  let rom:=2^(h/2)*W
  K*((8*k+12)*h)+4*W+
    (k+1)*(4*W+Plan.wordBill 0 k b W K+(4+2^k*60)*W)+4000*2^(5*k)*W+
    (2*K*h+2*rom)+
    (4*W+2008*W+25600*K*2^k*(b+1)+12800*K*2^k*(W+1)^2+2*E.plan.depth*rom)+
    (2*2^k*W+rom)+K*(6*k*h+(2*k+1)*2^(h/2)*h)

theorem priced_words (W K : ℕ) (width : W≤K*h) (hosts : N≤2^W) (digits : b≤W+1)
    (lanes : laneBits k h b=E.low) (small : 8*b≤h/2) (gain : E.gainBits≤b) :
    (E.clock+(E.staticEnd-E.origin))*W≤
      N*h*hostUnit k K+N*2^k*fieldUnit k b K+E.commonBill W K := by
  have clocks:=E.clock_bill W K width hosts digits lanes (small.trans (Nat.div_le_self ..))
  have rom:=E.static_bill W K width hosts digits lanes small gain
  rw [Nat.add_mul]
  apply (Nat.add_le_add clocks rom).trans
  let a:=(k+1)*(6+2008)+2008
  have factor : E.transformBill K+(4*W+(k+1)*E.depthBill W K)+4000*2^(5*k)*W+
      E.staticBill W K =
      N*h*(K*(180*k+28+(k+1)*94+2+6*k))+N*W*a+
      N*2^k*fieldUnit k b K+E.commonBill W K := by
    unfold transformBill depthBill staticBill fieldUnit commonBill Plan.wordBill a
    ring
  rw [factor]
  have wordPrice:=Nat.mul_le_mul_right a (Nat.mul_le_mul_left N width)
  unfold hostUnit a at *
  nlinarith only [wordPrice]

end

/-- Plain polynomial bounds are independent of the ambient radix, population, and word width. -/
theorem local_units (k b K : ℕ) :
    hostUnit k K ≤ 5000*(K+1)*(k+1) ∧
    fieldUnit k b K ≤ 100000*(K+1)*(k+1)*(b+1) := by
  constructor
  · unfold hostUnit
    nlinarith only [Nat.zero_le k,Nat.zero_le K,Nat.zero_le (K*k)]
  · unfold fieldUnit
    nlinarith only [Nat.zero_le k,Nat.zero_le b,Nat.zero_le K,Nat.zero_le (K*k),
      Nat.zero_le (K*b),Nat.zero_le (k*b),Nat.zero_le (K*k*b)]

end Hierarchy.DescentPackedWalsh.EstimatorArena

end OAI
