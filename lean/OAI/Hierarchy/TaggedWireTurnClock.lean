import OAI.Hierarchy.TaggedWireSocketWork
import OAI.Hierarchy.TaggedWireOldBoardNative

namespace OAI
/-! # Native execution time for all eleven signed turn columns -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
open ProtocolRAM Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM PrivateRAM

def turnColumnPrice (n : ℕ) := 8*(8*(4*n+18)+5)+4
def rawColumnPrice (n : ℕ) := 2*(67+(4*n+18))+4
def turnRate (before finish : ℕ) := 56+4*turnColumnPrice before+3*rawColumnPrice before+4*turnColumnPrice finish

private theorem charge (fixed l r x y : ℕ) :
    fixed+x*l+y*r≤(fixed+l+r)*(x+y+1) := by
  have m : 1≤x+y+1 := by omega
  have a : fixed≤(x+y+1)*fixed := by simpa using Nat.mul_le_mul_right fixed m
  have b := Nat.mul_le_mul_right l (show x≤x+y+1 by omega)
  have c := Nat.mul_le_mul_right r (show y≤x+y+1 by omega)
  calc
    _ ≤ (x+y+1)*fixed+(x+y+1)*l+(x+y+1)*r := by omega
    _ = _ := by ring

theorem Board.turn_clock (b : Board) (stockStart : ℕ) (paid active reserved used : Bank)
    {n m : ℕ} (first : ∀s,(b.before s).Work n) (last : ∀s,(b.finish s).Work m) :
    b.extendedTime (Inventory.ofOriginal stockStart b.old paid active reserved used)≤turnRate n m*(b.old+b.edges+1) := by
  let I:=Inventory.ofOriginal stockStart b.old paid active reserved used
  have width : I.width.work=67 := rfl
  have one := ticks_bound b.chart b.before first b.base b.old false
  have two := ticks_bound b.chart b.finish last b.newBase b.edges true
  have source (e : Expr) (he : e∈List.ofFn (b.rawFields I)) : e.work≤67+(4*n+18) := by
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he
    fin_cases j
    · exact (socket_work b.chart _ (first false)).1.trans (Nat.le_add_left _ _)
    · exact (socket_work b.chart _ (first true)).1.trans (Nat.le_add_left _ _)
    · change I.width.work≤_
      rw [width];omega
  have tail := columns_clock b.old b.endAt (67+(4*n+18)) (List.ofFn (b.rawFields I)) source
  rw [List.length_ofFn] at tail
  change ticks b.base b.old b.chart b.before false+ticks b.newBase b.edges b.chart b.finish true+
    clock (columns b.old b.endAt (List.ofFn (b.rawFields I)))≤_
  calc
    _ ≤ (4+4*(4+b.old*turnColumnPrice n))+(4+4*(4+b.edges*turnColumnPrice m))+
      (4+3*(4+b.old*rawColumnPrice n)) := Nat.add_le_add (Nat.add_le_add one two) tail
    _ = 56+b.old*(4*turnColumnPrice n+3*rawColumnPrice n)+b.edges*(4*turnColumnPrice m) := by ring
    _ ≤ turnRate n m*(b.old+b.edges+1) := by
      simpa only [turnRate,Nat.add_assoc] using
        charge 56 (4*turnColumnPrice n+3*rawColumnPrice n) (4*turnColumnPrice m) b.old b.edges

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram

end
end OAI
