import OAI.Hierarchy.DescentTerminalBinPackCheap
import OAI.Hierarchy.DescentTerminalExecUnique

namespace OAI
/-! # Bounded forward writes always run, even when proposed indirect addresses are malformed -/
namespace Hierarchy.DescentTerminalUniversalWrite
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure DescriptorExpr ProtocolRAM
open scoped Fin.CommRing
noncomputable section
variable {w : ℕ}
def entry (e : SumScores.T w) (out : ℕ) (m : Memory w) (i : ℕ) : Word w :=
  e.eval Fin.elim0
    (fun a=>if _live:out≤a ∧ a-out < i then entry e out m (a-out) else m a)
    (fun _=>((out+i:ℕ):Word w))
termination_by i
decreasing_by exact _live.2

def image (e : SumScores.T w) (out n : ℕ) (m : Memory w) :=
  fillSegment out n (fun a=>entry e out m (a-out)) m

theorem run (e : SumScores.T w) (out n : ℕ) (m : Memory w) (fits : out+n<2^w) :
    (PhysicalInputPhases.writing e Fin.elim0 out n).Exec m (image e out n m) (4+n*(2*e.binds+4)) := by
  intro P R K M pc reg pub exit installed data conf orig begin h
  subst orig
  apply SumScores.writing_prefix e out n fits (·=m) (fun _ a=>entry e out m (a-out)) ?_ M pc reg pub exit installed data conf m begin rfl
  intro x eqn a lo hi
  subst x
  rw [entry]
  have address : ((out+(a.val-out):ℕ):Word w)=a:=by rw [Nat.add_sub_of_le lo,Fin.cast_val_eq_self]
  rw [address]
  congr 1
  funext v
  by_cases h:out≤v
  · have rule : v<out+(a.val-out) ↔ v-out<a.val-out := by omega
    simp [fillSegment,h,rule]
  · simp [fillSegment,h]

theorem safe {S : ℕ} (src table out : ℕ) (m : Memory w) (fits : out+S<2^w) :
    (DescentTerminalBinPackCheap.program w src table out S).Exec m
      (image (DescentTerminalBinPackCheap.step w src table out) out S m) (4+102*S) ∧
      CheapCode (DescentTerminalBinPackCheap.program w src table out S) := by
  constructor
  · have ticks : 102*S=S*(2*(DescentTerminalBinPackCheap.step w src table out).binds+4) := by
      rw [DescentTerminalBinPackCheap.cost]
      omega
    rw [ticks]
    intro P R K M pc reg pub exit installed data conf orig begin h
    exact @run w (DescentTerminalBinPackCheap.step w src table out) out S m fits
      P R K M pc reg pub exit installed data conf orig begin h
  · exact @DescentTerminalBinPackCheap.cheap w src table out S

end
end Hierarchy.DescentTerminalUniversalWrite

end OAI
