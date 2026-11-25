import OAI.Hierarchy.DescentResetCandidateShape
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # Linear cost of a finite contact sweep with a shared packed dictionary -/
namespace Hierarchy.DescentContactCostUnit
open DescentResetCandidateDate DescentSIMDLookup
variable {T a b u v : ℕ}

theorem fixed (k : ℕ) (pos : 0<T) : k≤k*T := Nat.le_mul_of_pos_right _ pos

theorem sum (one : a≤u*T) (two : b≤v*T) : a+b≤(u+v)*T := by
  rw [Nat.add_mul];exact Nat.add_le_add one two

theorem left (k : ℕ) (one : a≤u*T) : k*a≤(k*u)*T := by
  rw [Nat.mul_assoc];exact Nat.mul_le_mul_left _ one

theorem right (k : ℕ) (one : a≤u*T) : a*k≤(u*k)*T := by
  simpa only [Nat.mul_comm k a,Nat.mul_comm k u] using left k one

/-- Round the actual row count up to a CPU bank size, allowing an empty row set. -/
theorem span (one : a≤u*T) (pos : 0<T) : 2^Nat.clog 2 a≤(2*u+1)*T :=
  (DescentDyadicSpan.span_le a).trans (sum (left 2 one) (fixed 1 pos))

def cells (N : ℕ) := (N*2+2)*3
def clock (N jobs limit : ℕ) := (4+10*cells N)+(4+jobs*(4+(2*limit+4)+(4+44)))
def names (N jobs limit : ℕ) := 15*(cells N+1)+(15+jobs*(102+4*limit))

theorem scan (A : Shape) (N b limit h T : ℕ) (rows : A.rows≤T) (lookup : 2^(h/2)≤T)
    (paid : (b*N+b)*A.lanes≤h/2) :
    A.costBound N b limit≤clock N A.jobs limit*T ∧ A.nameBound N b limit≤names N A.jobs limit*T := by
  have pos : 0<T := (Nat.two_pow_pos _).trans_le lookup
  have row : A.rows≤1*T:=by simpa using rows
  have rounded : 2^Nat.clog 2 A.rows≤3*T:=by simpa using span row pos
  have key : 2^((b*N+b)*A.lanes)≤3*T:=
    ((Nat.pow_le_pow_right (by decide) paid).trans lookup).trans (by omega)
  have width : 2^(A.width N b)≤3*T:=by
    unfold Shape.width Shape.rowBits
    rcases le_total ((b*N+b)*A.lanes) (Nat.clog 2 A.rows) with h|h
    · simpa only [max_eq_right h] using rounded
    · simpa only [max_eq_left h] using key
  have count : A.size N b≤cells N*T:=left (N*2+2) width
  constructor
  · have read:=sum (sum (fixed 4 pos) (right (2*limit+4) row)) (sum (fixed 4 pos) (left 44 row))
    have run:=sum (sum (fixed 4 pos) (left 10 count)) (sum (fixed 4 pos) (left A.jobs read))
    simpa only [Shape.costBound,clock,Nat.one_mul,Nat.mul_one] using run
  · exact sum (left 15 (sum count (fixed 1 pos)))
      (sum (fixed 15 pos) (left A.jobs (fixed (102+4*limit) pos)))

end Hierarchy.DescentContactCostUnit

end OAI
