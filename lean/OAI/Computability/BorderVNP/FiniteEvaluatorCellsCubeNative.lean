import OAI.Computability.BorderVNP.FiniteEvaluatorCellsCube
import OAI.Computability.BorderVNP.FiniteEvaluatorCellsNative

/-! # Charged field path sum of the sparse-cell and cube evaluator

The cube continuation consumes the true post-cell RAM image. The full wide
startup and positive dispatch retain their native cost and read both private
routines at the program counters of the assembled table.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CellsCube

open VPVNP.BurstRAM RoutingISA RoutingISA.Pins TeamContraction FiniteDiagonal
open scoped BigOperators Classical

variable {w dim b h K d : ℕ} {F : Type*} [Field F] [Fintype F]
variable (X : Cells.Inputs F) (Y : CubePacket.Inputs dim b h K d F) (pub : Arg → Word w)

/-- All real charged returns of the consecutive validator, report and cube stages
have total field value equal to the three corresponding products. -/
theorem bounded_prepared_for (codec : Cells.Codec) (bank : Bank w) (mem : Memory w) (n ticks burst clock : ℕ)
    (cells : Cells.Prepared X pub mem n codec) (cube : CubePacket.Prepared Y pub (X.post mem))
    (wide : 2*Fintype.card F<w) (fuel : 2*Fintype.card F<CompactMachine.nativeClock n)
    (oneWord : 1≤TeamScales.width n (1/2))
    (time : X.validatorCost pub mem+X.scalarCost+Y.cost ≤ ticks)
    (words : TeamScales.width n (1/2) ≤ burst) (choices : n^25 ≤ clock) :
    let f := CellDispatch.Frame.ofMemory pub mem
    boundedWeight pub (Cells.library F codec) (Cells.terminals F codec) (CompactMachine.nativeClock n) code bank mem ticks burst clock =
      ((((f.ownedRows mem 0 f.count).map (fun i => (X.cells i).weight)).prod : ℤ) : F) * X.outputs.prod * ∏ i, Y.scalar i := by
  obtain ⟨paths,accept,limits,val⟩ := prepared_value_for X Y codec pub bank mem n cells cube wide fuel oneWord
  apply Eq.trans (boundedWeight_eq_history_sum pub _ _ _ paths (by decide) accept _) val
  intro es he
  have q := limits es he
  exact ⟨q.cost.trans time,fun e hh => (q.length e hh).trans words,fun e hh => (q.choices e hh).trans choices⟩

/-- All real charged returns of the consecutive validator, report and cube stages
have total field value equal to the three corresponding products. -/
theorem bounded_prepared (bank : Bank w) (mem : Memory w) (n ticks burst clock : ℕ)
    (cells : Cells.Prepared X pub mem n) (cube : CubePacket.Prepared Y pub (X.post mem))
    (wide : 2*Fintype.card F<w) (fuel : 2*Fintype.card F<CompactMachine.nativeClock n)
    (oneWord : 1≤TeamScales.width n (1/2))
    (time : X.validatorCost pub mem+X.scalarCost+Y.cost ≤ ticks)
    (words : TeamScales.width n (1/2) ≤ burst) (choices : n^25 ≤ clock) :
    let f := CellDispatch.Frame.ofMemory pub mem
    boundedWeight pub (Cells.library F) (Cells.terminals F) (CompactMachine.nativeClock n) code bank mem ticks burst clock =
      ((((f.ownedRows mem 0 f.count).map (fun i => (X.cells i).weight)).prod : ℤ) : F) * X.outputs.prod * ∏ i, Y.scalar i :=
  bounded_prepared_for X Y pub .dense bank mem n ticks burst clock cells cube wide fuel oneWord time words choices

/-- Execute wide startup and the positive tag before the combined local evaluator.
The total tick limit charges the actual startup, broadcast, selector, sparse
validation, scalar readback and cube lookup. -/
theorem wide_prepared (n : ℕ) {L : Pins.Layout} (fields : ProcessorFields L) (f : BroadcastFrame)
    (bank : Bank w) {pre post after hs loaded mb}
    (startup : Runs pub (TeamSiteEvents.macros (Cells.library F) (CompactMachine.nativeClock n)) wideStartup bank
      (Evaluator.processorMemory fields w) pre post after)
    (header : Runs pub (TeamSiteEvents.macros (Cells.library F) (CompactMachine.nativeClock n)) readBroadcast post after hs loaded mb)
    (stable : f.Stable (readings loaded)) (positive : (mb f.dst).val ≠ 0)
    (ticks burst clock : ℕ) (cells : Cells.Prepared X pub mb n) (cube : CubePacket.Prepared Y pub (X.post mb))
    (wide : 2*Fintype.card F<w) (fuel : 2*Fintype.card F<CompactMachine.nativeClock n)
    (oneWord : 1≤TeamScales.width n (1/2))
    (time : pre.length+hs.length+2 + (X.validatorCost pub mb+X.scalarCost+Y.cost) ≤ ticks)
    (words : TeamScales.width n (1/2) ≤ burst) (choices : n^25 ≤ clock) :
    let M := Evaluator.processorMachine (dispatchTable wideStartup code) pub
      (TeamSiteEvents.macros (Cells.library F) (CompactMachine.nativeClock n)) bank fields
    letI := Fintype.ofFinite (NativePath M ticks burst clock)
    let localFrame := CellDispatch.Frame.ofMemory pub mb
    (∑ p : NativePath M ticks burst clock,
      weight pub (Cells.library F) (Cells.terminals F) (CompactMachine.nativeClock n) (dispatchTable wideStartup code) bank p.val) =
      ((((localFrame.ownedRows mb 0 localFrame.count).map (fun i => (X.cells i).weight)).prod : ℤ) : F) * X.outputs.prod * ∏ i, Y.scalar i :=
  (positive_native_sum pub _ _ _ code fields f bank startup header stable positive (by decide) _ _ _ (by omega)).trans
    (bounded_prepared X Y pub _ mb n _ _ _ cells cube wide fuel oneWord (by omega) words choices)

end FiniteEvaluator.CellsCube

end BorderVNP
end Computability
end OAI
