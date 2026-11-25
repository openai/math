import OAI.Hierarchy.DescentTerminalChartScale
import OAI.Hierarchy.DescentTerminalFrozenSize

namespace OAI
/-! # Residual live fibres pay for real end-to-end ancestry replay -/
namespace Hierarchy.DescentCompiler.TerminalScale
open DescentTerminalFrozenRoster Filter
open scoped Topology
noncomputable section

/-- The original socket exponent precedes the residual exponent. The spare copy
coordinates pay for every ancestor visit of an entire frozen cohort. -/
theorem cohort_ancestors (J t a τ j k h s:ℕ) (two:2≤a) (reserve:2*a≤τ)
    (sockets:j≤a*(J+1)) (late:25600*(t+1)≤2^(J+1)) (packing:h≤32*((2^j)*s)) :
    800*((t+1)*J+1)*h≤s*2^(tail τ J+k) := by
  have age:(t+1)*J+1≤(t+1)*(J+1):=by rw [Nat.mul_add];omega
  have linear:J+1≤2^(J+1):=(Nat.lt_two_pow_self : J+1<2^(J+1)).le
  have expansion:25600*((t+1)*J+1)≤2^(2*(J+1)):=calc
    _ ≤ 25600*((t+1)*(J+1)) := Nat.mul_le_mul_left _ age
    _ = (25600*(t+1))*(J+1) := by ring
    _ ≤ 2^(J+1)*2^(J+1) := Nat.mul_le_mul late linear
    _ = _ := by rw [←pow_add];congr 1;omega
  have split:j+2*(J+1)≤tail τ J+k:=by
    have chosen:=Nat.mul_le_mul_right (J+1) reserve
    have residual:=Nat.mul_le_mul_right (J+1) two
    unfold tail
    rw [Nat.mul_assoc] at chosen
    omega
  calc
    _ ≤ 800*((t+1)*J+1)*(32*((2^j)*s)) := Nat.mul_le_mul_left _ packing
    _ = s*((2^j)*(25600*((t+1)*J+1))) := by ring
    _ ≤ s*((2^j)*2^(2*(J+1))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ expansion)
    _ ≤ _ := by rw [←pow_add];exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) split)

/-- The real frozen power and its bounded roster shift use the same bin clock as
the scalar circuit, including reset dates and the initial copy header. -/
theorem cohort_tables (t κ gain B:ℕ) (large:10≤B) :
    ∀ᶠ h:ℕ in atTop, let J:=Nat.log 2 h/(2*B); ∀k:ℕ,k≤κ*(J+1)→
      ((t+1)*J+1≤2^(h/2)) ∧
      (ROM.size (k*((t+1)*J)) (8+gain*((t+1)*J))≤3*2^(h/2)) := by
  have good:0<B:=by omega
  filter_upwards [eventually_home 0 0 5 B good (by omega),
    eventually_late (25600*(t+κ+gain+9)) B good] with h feasible late
  intro J k key
  let X:=2^(J+1)
  have nonzero:1≤X:=Nat.one_le_two_pow
  have x2 : 2 ≤ X := (Nat.pow_le_pow_right (n:=2) (by decide) (Nat.le_add_left 1 J) : 2^1 ≤ 2^(J+1))
  have lg:J+1≤X:=(Nat.lt_two_pow_self : J+1<2^(J+1)).le
  change 25600*(t+κ+gain+9)≤J at late
  have t_small:t+1≤X:=by omega
  have k_small:κ≤X:=by omega
  have gain_small:gain+8≤X:=by omega
  have cpu:32*(1*scale J 5)≤h:=feasible.2 0 1 (scale J 5) (by simp [tail]) (by simp) le_rfl
  have cube:1≤X^3:=Nat.one_le_pow 3 _ nonzero
  have fixed:(t+1)*J+1≤X^2:=calc
    _ ≤ (t+1)*(J+1) := by rw [Nat.mul_add];omega
    _ ≤ X^2 := by rw [pow_two];exact Nat.mul_le_mul t_small lg
  have grain:k≤X^2:=by rw [pow_two];exact key.trans (Nat.mul_le_mul k_small lg)
  have xle:X≤X^2:=by rw [pow_two];exact Nat.le_mul_of_pos_left _ (by omega)
  have parts:k+gain+8≤X^3:=calc
    _ ≤ 2*X^2 := by omega
    _ ≤ X*X^2 := Nat.mul_le_mul_right _ x2
    _ = _ := by ring
  have count:k*((t+1)*J)+(8+gain*((t+1)*J))≤X^5:=calc
    _ ≤ (k+gain+8)*((t+1)*J+1) := by ring_nf;omega
    _ ≤ X^3*X^2 := Nat.mul_le_mul parts fixed
    _ = _ := by ring
  have same:X^5=scale J 5:=by unfold scale X;rw [←pow_mul,Nat.mul_comm]
  have whole:X^5≤h/2:=by rw [same];omega
  have squares:X^2≤X^5:=by rw [show X^5=X^3*X^2 by ring];exact Nat.le_mul_of_pos_left _ cube
  have f:=count.trans whole
  constructor
  · exact (fixed.trans (squares.trans whole)).trans (Nat.lt_two_pow_self : h/2<2^(h/2)).le
  · unfold ROM.size
    rw [←pow_add, Nat.add_comm (8+gain*((t+1)*J)) (k*((t+1)*J))]
    have outer:=Nat.pow_le_pow_right (n:=2) (by decide) f
    have left:=Nat.pow_le_pow_right (n:=2) (by decide) (show k*((t+1)*J)≤h/2 by omega)
    have right:=Nat.pow_le_pow_right (n:=2) (by decide) (show 8+gain*((t+1)*J)≤h/2 by omega)
    omega
end
end Hierarchy.DescentCompiler.TerminalScale

end OAI
