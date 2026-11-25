import OAI.Hierarchy.DescentPackedWalshArena
import OAI.Hierarchy.DescentPackedWalshFullPrice
import OAI.Hierarchy.DescentGLPhysicalTrajectory
import OAI.Hierarchy.DescentWalshPrecision

namespace OAI
/-! # Address of the last word used by the entire reset estimator -/
namespace Hierarchy.DescentPackedWalsh.EstimatorArena
open Filter DescentGL DescentPackedWalshReduction
noncomputable section
variable (E : EstimatorArena)
local notation "k" => E.dim
local notation "Q" => 2^E.dim

/-- One past the genuine final public permutation column. -/
def endAddress := PhysicalTrajectory.outputBase k E.solveAt+Q

theorem endAddress_eq : E.endAddress=E.start+(2*k+2)*page E.hosts E.high+
    (k+1)*(E.dataWords+Q)+k*(3*Q+1)+2*Q := by
  unfold endAddress PhysicalTrajectory.outputBase RowStageRAM.placed solveAt scratch stride
    inputEnd numeratorAt location sqOffset dim
  dsimp only
  ring

private theorem page_extent : page E.hosts E.high≤2*((E.hosts+1)*Q) := by
  apply (page_le E.hosts E.high).trans
  apply Nat.mul_le_mul_left
  have large : 2^E.high≤Q:=Nat.pow_le_pow_right (by decide) (Nat.le_add_right ..)
  have rows:=Nat.mul_le_mul_left E.hosts large
  have keep:=Nat.two_pow_pos k
  rw [Nat.add_mul,Nat.one_mul]
  omega

theorem dataWords_extent : E.dataWords≤2*((2*E.hosts+1)*Q) := by
  have lim:=E.plan.data_extent 0
  simp only [Nat.zero_add] at lim
  change E.dataWords≤2*(E.plan.hosts 0*Q) at lim
  have count : E.plan.hosts 0≤2*E.hosts+1 := by
    simpa only [plan,reduction,Plan.hosts,Plan.depth,Nat.sub_zero] using
      DescentWalshDyadicBudget.padded_le E.hosts
  exact lim.trans (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right Q count))

/-- The bound includes both Walsh transforms, square, all depth tables with
their host-pair scratch, and all central row selections and permutation words.
The initial free gap enters as an actual address offset. -/
theorem mutable_extent : E.endAddress≤E.staticEnd+E.dataGap+12*(k+1)*(E.hosts+1)*Q := by
  rw [E.endAddress_eq]
  calc
    _ ≤ E.start+(2*k+2)*(2*((E.hosts+1)*Q))+
        (k+1)*(2*((2*E.hosts+1)*Q)+Q)+k*(3*Q+1)+2*Q := by
      gcongr
      · exact E.page_extent
      · exact E.dataWords_extent
    _ ≤ _ := by
      unfold start
      have kq : k≤k*Q := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
      nlinarith only [kq,Nat.zero_le (k*E.hosts*Q),Nat.zero_le (E.hosts*Q),
        Nat.zero_le (k*Q),Nat.zero_le Q]

/-- Separate bit budgets for the immutable prefix, extra offset, host
population and central dimension. -/
theorem end_room_bits (w e A K : ℕ) (address : e+2≤w)
    (prefixEnd : E.staticEnd≤2^e) (gap : E.dataGap≤2^e)
    (hosts : E.hosts≤2^A) (axis : k≤K) (panel : 5+A+2*K≤e) :
    E.endAddress<2^w := by
  have extra : E.hosts+1≤2*2^A := by have pos:=Nat.two_pow_pos A;omega
  have size : Q≤2^K:=Nat.pow_le_pow_right (by decide) axis
  have levels : k+1≤2^K:=Nat.lt_two_pow_self.trans_le size
  have work : 12*(k+1)*(E.hosts+1)*Q≤2^e := by
    calc
      _ ≤ 12*2^K*(2*2^A)*2^K := by gcongr
      _ ≤ 32*(2^A*2^K*2^K) := by nlinarith only [Nat.zero_le (2^A*2^K*2^K)]
      _ = 2^(5+A+2*K) := by
        rw [show 5+A+2*K=5+A+K+K by omega]
        simp only [pow_add]
        ring
      _ ≤ _ := Nat.pow_le_pow_right (by decide) panel
  have space:=Nat.pow_le_pow_right (by decide : 0<2) address
  rw [pow_add] at space
  have clear:=E.mutable_extent
  have pos:=Nat.two_pow_pos e
  omega

/-- The same cap handles the real allocated mutable bank for all physical
ages with exponentially many hosts and a quadratic-logarithmic local axis. -/
theorem eventually_end_room (A K : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀(E : EstimatorArena) (w : ℕ),
      E.staticEnd≤2^((A+2)*h) → E.dataGap≤2^((A+2)*h) →
      E.hosts≤2^(A*h) → E.dim≤K*(Nat.log 2 h+1)^2 → (A+4)*h≤w → E.endAddress<2^w := by
  filter_upwards [DescentWalshPrecision.eventually_log_square (2*K+5),eventually_ge_atTop 2] with h late high
  intro A₀ w earlier gap count axis word
  have area : 0<(Nat.log 2 h+1)^2:=by positivity
  have dial : (A+2)*h+2≤w := by
    rw [Nat.add_mul] at word ⊢
    omega
  have panel : 5+A*h+2*A₀.dim≤(A+2)*h := by
    rw [Nat.add_mul] at late ⊢
    nlinarith only [late,axis,area,Nat.zero_le h]
  exact A₀.end_room_bits w ((A+2)*h) (A*h) A₀.dim dial earlier gap count le_rfl panel

theorem room_of_end {w : ℕ} (fit : E.endAddress<2^w) : PhysicalTrajectory.Room w k E.solveAt E.bank :=
  ⟨fun j=>E.includes_bank j.val j.isLt,fit⟩

end
end Hierarchy.DescentPackedWalsh.EstimatorArena

end OAI
