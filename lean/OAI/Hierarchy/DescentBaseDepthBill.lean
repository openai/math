import OAI.Hierarchy.DescentBaseDepthLayout
import OAI.Hierarchy.DescentColonyCandidateHardware

namespace OAI
/-! # Clock and ROM bounds for the actual native depth algorithm -/
namespace Hierarchy.DescentBaseProfile.DepthRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentColonies.CandidateRAM
open ThreeFlat.RAM PhysicalProcedure
theorem Batch.stored (B : Batch) (w n : ℕ) : Bounded (B.text w n) (B.ticks n) := by
  induction n with
  | zero=>exact ⟨@scan_cheap _ _ _ _,by change 15≤4*4;decide⟩
  | succ n ih=>exact seq_bound ih (scan_bound w _ 1 (B.expr n) (by decide))

theorem tournament_work (f : ℕ→Expr) (s i U : ℕ) (work : ∀q,(f q).work≤U) :
    (tournament f s i).work+1≤(U+1)*4^s := by
  induction s generalizing i with
  | zero=>simpa [tournament] using Nat.succ_le_succ (work i)
  | succ s ih=>
    have a:=ih i;have b:=ih (i+2^s)
    simp only [tournament,maximum,Expr.work,pow_succ] at *
    rw [←Nat.mul_assoc]
    omega

namespace Layout
variable (L : Layout)
def stepBill := 4+L.H*(8+2*(13+2*(37*4^L.degreeBits)))
def baseBill := (4+L.H*(8+2*(1+7*L.N)))+(4+L.H*(8+2*(1+9*L.M)))

theorem step_time (s : ℕ) : (L.step s).ticks L.H≤L.stepBill := by
  apply Batch.time
  intro v _
  have bound (q : ℕ) : (L.peer s v q).work≤36 := by
    unfold peer
    split <;> simp only [neighbor, decrease, Expr.work, cell_work] <;> decide
  have ht:=tournament_work (L.peer s v) L.degreeBits 0 36 bound
  simp only [step,maximum,Expr.work,cell_work]
  omega

theorem time (w s : ℕ) : L.clocks w s≤L.baseBill+s*L.stepBill := by
  induction s with
  | zero=>
    have a:=L.sums.time L.H (1+7*L.N) (fun i _=>(rowSum_bounds _ _).1.le)
    have b:=(L.seed w).time L.H (1+9*L.M) (fun i _=>(probe_bounds ..).1)
    simpa [clocks,baseBill] using Nat.add_le_add a b
  | succ s ih=>
    have := L.step_time s
    simp only [clocks,Nat.succ_mul]
    omega

theorem hardware (w s : ℕ) : Bounded (L.cpu w s) (L.clocks w s) := by
  induction s with
  | zero=>exact seq_bound (L.sums.stored ..) ((L.seed w).stored ..)
  | succ s ih=>exact seq_bound ih ((L.step s).stored ..)

end Layout
end Hierarchy.DescentBaseProfile.DepthRAM

end OAI
