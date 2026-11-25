import OAI.Hierarchy.DescentSelectorWordScale
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # Uniform local rate of the sorted path decoder and its physical candidate scan -/
namespace Hierarchy.DescentDatedOperandReadPipeline.SortedInput
open DescentDatedOperandSelectionRun DescentArgumentWidthArithmetic
variable (g : Geometry)
local notation "P" => g.paths

def portWork (paths : ℕ) :=32+8*((paths+1)*(30+8*paths))

theorem factor (short U : ℕ) (bound : ∀i,g.coefficientInputs 32 short i≤U) :
    readFactor 1 2 P 32 (portWork P)*(g.jobs*1+1)≤U^22 :=by
  have high : 8192≤U:=bound 0
  have big : 2≤U:=by omega
  have pos : 0<U:=by omega
  have lit {n : ℕ} (small : n≤8192) : n≤U^1:=one (by omega)
  have p : P≤U^1:=one (bound 1)
  have jobs : g.jobs≤U^1:=one (bound 5)
  have work : portWork P≤U^7:=add big (lit (by decide)) (mul (lit (by decide))
    (mul (add big p (lit (by decide))) (add big (lit (by decide)) (mul (lit (by decide)) p))))
  have inner : 14+2*(32+11)+portWork P+22≤U^9:=add big (add big (lit (by decide)) work) (lit (by decide))
  have read_ : readWork P 2 32 (portWork P)≤U^11:=add big (lit (by decide)) (mul p inner)
  have ar : 2+1+P+1≤U^3:=add big (add big (lit (by decide)) p) (lit (by decide))
  have rate : readFactor 1 2 P 32 (portWork P)≤U^16:=
    mul (mul (lit (by decide)) ar) (add big read_ (lit (by decide)))
  rw [Nat.mul_one]
  exact raise pos (mul rate (add big jobs (lit (by decide)))) (by decide)

/-- The complete padded literal broadcast uses one row map, one cut map,
and one dictionary of repeated digits under the purchased width. -/
theorem broadcast_size (rows a M h : ℕ) (width : 0<a) (lanes : 0<M) (price : 18*a*M≤h/2) :
    2*2^(Nat.clog 2 rows)+2^(Nat.clog 2 ((M+1)*2^a))≤2*(2*rows+1)+2^(h/2) :=by
  have l : M≤a*M:=Nat.le_mul_of_pos_left _ width
  have b : a≤a*M:=Nat.le_mul_of_pos_right _ lanes
  have used : a+M≤h/2:=by rw [Nat.mul_assoc] at price;omega
  have words : (M+1)*2^a≤2^(h/2):=calc
    _ ≤ 2^M*2^a:=Nat.mul_le_mul_right _ (show M+1≤2^M from Nat.lt_two_pow_self)
    _ = 2^(a+M):=by rw [pow_add,Nat.mul_comm]
    _ ≤ _:=Nat.pow_le_pow_right (by decide) used
  exact Nat.add_le_add (Nat.mul_le_mul_left 2 (DescentDyadicSpan.span_le rows))
    (Nat.pow_le_pow_right (by decide) (Nat.clog_le_of_le_pow words))

end Hierarchy.DescentDatedOperandReadPipeline.SortedInput

end OAI
