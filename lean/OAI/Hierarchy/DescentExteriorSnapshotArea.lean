import OAI.Hierarchy.DescentExteriorHopSnapshots
import OAI.Hierarchy.DescentExteriorHopTariff
import OAI.Hierarchy.DescentTerminalCohortArena

namespace OAI
/-! # The final ancestry tape is the original source of the cohort sorter -/
namespace Hierarchy.DescentExteriorReplay.Snapshots
open ProtocolRAM
variable {k : ℕ} (A : Snapshots k)
def scratchAt (base f age : ℕ) := A.start base f age
def freshAt (base f n age : ℕ) := A.scratchAt base f age+(age+1)*stride n
def lastAt (base f n age : ℕ) := page (A.scratchAt base f age) n age

theorem last_fits {w : ℕ} (base f n age : ℕ) (fit : A.freshAt base f n age<2^w) :
    (A.lastAt base f n age).Fits w (A.freshAt base f n age) := by
  have inc : stride n ≤ (age+1)*stride n := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  unfold freshAt at fit
  change 0<stride n ∧ stride n<2^w ∧
    A.scratchAt base f age+age*stride n+stride n≤A.scratchAt base f age+(age+1)*stride n
  exact ⟨Nat.two_pow_pos _,by omega,by rw [Nat.succ_mul,Nat.add_assoc]⟩

theorem fresh_bound (base f n age H rom : ℕ)
    (literal : A.start base f age≤base+2*H+3*rom) :
    A.freshAt base f n age≤base+2*H+3*rom+2*(age+1)*(n+2) := by
  have width : stride n≤2*(n+2) := DescentTerminalCohortArena.period_le (n+1)
  calc
    _ ≤ (base+2*H+3*rom)+(age+1)*(2*(n+2)) := Nat.add_le_add literal (Nat.mul_le_mul_left _ width)
    _ = _ := by ring


end Hierarchy.DescentExteriorReplay.Snapshots

end OAI
