import OAI.Hierarchy.TraceReceiverOwnerPairs
import OAI.ThreeFlat.Diagonal.NavigationScalar
import OAI.ThreeFlat.Diagonal.TickScratchRegion
import OAI.ThreeFlat.RAM.HistoryNodeReverseCode

namespace OAI
/-! # Mounting the receiver-local decoded tick and chronological owner directory -/
namespace Hierarchy.TraceReceiverOwnerMount
open ThreeFlat Diagonal RAM RAM.PhysicalProcedure
open RAM.HistoryNodeDirectory Diagonal.TickWorkspace Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
variable {W : ℕ}

abbrev desc (age : ℕ) := base age 11+3*(stride age/4)
abbrev pairs (age : ℕ) := base age 11+1*(stride age/4)

def header (W age firstFinal rootCount target : ℕ) : Procedure W :=
  ((((NavigationPass.start (desc age) firstFinal).seq
    (NavigationPass.start ((desc age+1:ℕ):Word W) (base age 44))).seq
    (NavigationPass.start ((base age 6+1:ℕ):Word W) rootCount)).seq
    (NavigationPass.start (base age 1) 0)).seq (PhysicalInputPhases.copying W target 1 (base age 1+3))

def reverse (W age : ℕ) : Procedure W :=
  ⟨23,9,3,Reverse.block W,fun i=>(![desc age,base age 6+1,base age 45] i:ℕ)⟩

def procedure (W age firstFinal rootCount owners target : ℕ) : Procedure W :=
  ((header W age firstFinal rootCount target).seq
    (TraceReceiverOwnerPairs.procedure W owners (pairs age) rootCount)).seq (reverse W age)

def ticks (firstFinal rootCount : ℕ) := 39+56*rootCount+11*(firstFinal+rootCount)

theorem dimensions (W age firstFinal rootCount owners target : ℕ) :
    let p:=procedure W age firstFinal rootCount owners target
    p.labels=88 ∧ p.registers=38 ∧ p.slots=6 := by
  have a:=TraceReceiverOwnerPairs.hardware W owners (pairs age) rootCount
  dsimp only [procedure,header,reverse,Procedure.seq,NavigationPass.start,PhysicalInputPhases.copying]
  rw [a.1,a.2.1,a.2.2]
  decide

theorem hardware (W age firstFinal rootCount owners target : ℕ) :
    let p:=procedure W age firstFinal rootCount owners target
    p.labels+p.registers+p.slots ≤ 1000 := by
  have d:=dimensions W age firstFinal rootCount owners target
  dsimp only
  rw [d.1,d.2.1,d.2.2]
  decide

theorem ticks_le (firstFinal rootCount : ℕ) :
    ticks firstFinal rootCount ≤ 1000*(1+firstFinal+rootCount) := by unfold ticks;omega

/-- The complete reverse owner scan fits the receiver's startup allowance
at the total-node bound supplied by the selected archive. -/
theorem ticks_directory {w first roots : ℕ} (large : 80 ≤ w) (count : first+roots ≤ 2^(3*w/5)) :
    ticks first roots ≤ 2^(7*w/10) := by
  have positive : 0 < 2^(3*w/5):=Nat.two_pow_pos _
  calc
    ticks first roots ≤ 128*2^(3*w/5) := by unfold ticks;omega
    _ = 2^(7+3*w/5) := (pow_add 2 7 (3*w/5)).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

end Hierarchy.TraceReceiverOwnerMount

end OAI
