import OAI.Hierarchy.TraceFactorWork
import OAI.Hierarchy.GridChosenReceiverTariff

namespace OAI
/-! # Actual registered work gives the terminal forest's padding and native clock -/
noncomputable section
namespace Hierarchy.TraceFactorReceiver.Gather
open ThreeFlat Diagonal.HistoryContraction RAM
open TraceDistribution
open scoped BigOperators

/-- Each compiled leaf contributes one site tariff before any terminal
copies. This row and bit capacity estimate needs no extra height assumption. -/
theorem forest_tariff {F : Type*} {k depth setup maps W : ℕ} (T : Tree F k)
    (registered : (10025+1016*depth+setup+maps)*T.resources≤W) :
    10000*(T.compile.cells+T.compile.internal)≤W := by
  rw [Tree.compiled_rows,Tree.compiled_bits]
  exact (Nat.mul_le_mul (show 10000≤10025+1016*depth+setup+maps by omega)
    (show T.rows+T.bits≤T.resources by unfold Tree.resources Stage.treeWork;omega)).trans registered

theorem tree_slot_clock {F : Type} [Field F] [Fintype F] {k n clk setup inside depth base maps : ℕ}
    {arity : Fin n→ℕ} (T : ∀ j,Tree F (arity j)) (wires : ∀ i,Fin (arity i)→Fin k)
    (cost : Fin n→ℕ) (resource : ∀ i,(10025+1016*depth+base+maps)*(T i).resources≤cost i)
    (perTick : GridChosenReceiver.reserve*(∑ i,cost i)≤clk)
    (startRoom : 4*setup≤clk) (field : 4*fieldCost F≤clk)
    (bill : inside≤ setup+65536*(∑ i,cost i)) :
    let N:=forest (fun i=>(T i).compile) wires
    let H:=clk/40000
    let J:=2*H
    let pad:=H-N.internal
    let fill:=J-(N.cells+pad)
    N.internal≤H ∧ N.cells+pad≤J ∧
      inside+TickTerminalPadding.budget F pad fill+evalCost F H J≤clk := by
  exact GridChosenReceiver.slot_clock (fun i=>(T i).compile) wires cost
    (fun i=>forest_tariff (T i) (resource i)) perTick startRoom field bill

end Hierarchy.TraceFactorReceiver.Gather
end

end OAI
