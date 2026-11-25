import OAI.Computability.NearSquareRoot.InterchangeROMOuterRulersCommand
import OAI.Computability.NearSquareRoot.InterchangeROMOuterRulersBuffers
import OAI.Computability.NearSquareRoot.InterchangeROMBankNative
import OAI.Computability.NearSquareRoot.InterchangeROMBankMain

/-! # Banking and unbanking the exact exposed native rows -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMOuter

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Loom
  InterchangeAddress InterchangeAddress.Request InterchangeROMExpose InterchangeROMRecursion
  InterchangeSpectralFibre

private theorem header_eq (i : Input) (k : ℕ) :
    InterchangeROMBank.nativeRuler (b:=i.b) (ord i) (axisP i) (axisG i) (axisB i) (axisF i) k () =
      send (InterchangeROMBankRulers.cutTriple i k) := by
  rw [InterchangeROMBank.nativeRuler_eq]
  exact congrArg (fun n => send (tally (room i.req.before),tally k,tally n))
    (InterchangeROMBankRulers.tailFactor_eq i).symm

/-- Before the cubic core, the original center header is parked outside a
packet of grouped rows with their corrected header. The return adapter uses
the same original header and restores the permuted native row order. -/
theorem native_wires : ∃ k C K : ℕ, ∀ {a m b : ℕ} (q : Request b) (hb : 2 ≤ b)
    (hn : 0 < a+m+a) (hw : a+m+a < q.width) (ok : q.Admissible) (W cell : ℕ)
    (_ : 3 ≤ W) (_ : W ≤ b) (_ : ∀ j, (q.contents j).count ≤ cell*(q.recordWidth+1)),
    let i := InterchangeROMStars.frame a m q hb hn hw ok
    let tag := send (centerHeader i)
    let head := send (groupedHeader i W)
    let op : key i W → key i W := swapMain (OuterReserves.main a m)
    let price := wireCost K C k W b i.n (bufferCost W cell)*(localMass q k+1)
    ∀ parent, At parent (entry W b i.n) (job b) [] [] (.fork tag (centerPayload i))
      (.fork tag (.fork head (stream i W id))) price 0 0 ∧
      At parent (leave W b i.n) (job b) [] [] (.fork tag (.fork head (stream i W op)))
        (.fork tag (InterchangeROMStars.afterMain a m q hb hn hw ok)) price 0 0 := by
  obtain ⟨k,C,K,checked⟩ := priced_wires
  refine ⟨k,C,K,?_⟩
  intro a m b q hb hn hw ok W cell hW hWb small i tag head op price
  have hp : 0 < (BatchFrame.outer (axisP i) ()).count := by
    rw [BatchFrame.outer,space]
    exact wide _ (InterchangeROMBankRulers.prefix_solid i)
  have ht : 0 < (BatchFrame.tail (b:=i.b) (ord i) (axisG i) (axisB i) (axisF i) ()).count := by
    rw [← InterchangeROMBankRulers.tailFactor_eq i]
    exact wide _ (InterchangeROMBankRulers.tailFactors_solid i)
  let hb' := (show 0 < i.b from by have := i.radix; omega)
  let hW' := (show 0 < W from by omega)
  have split := InterchangeROMBank.bank_run (b:=i.b) (W:=W) (ord i) (axisP i) (axisG i)
    (axisB i) (axisF i) () hp ht hb' hW' (fun _ => centerValues i)
  have merge := InterchangeROMBank.unbank_run (b:=i.b) (W:=W) (ord i) (axisP i) (axisG i)
    (axisB i) (axisF i) () hp ht hb' hW' (fun u _ => paddedRow i u ∘ op)
  rw [header_eq] at split merge
  rw [gather_main q hb hn hw ok hW'] at merge
  obtain ⟨f,g⟩ := buffers i W k cell hW hWb small
  exact checked i W (bufferCost W cell) (centerPayload i) (stream i W id) (stream i W op)
    (InterchangeROMStars.afterMain a m q hb hn hw ok) (f id) (g id) (g op)
    (f (swapMain (OuterReserves.main a m))) split merge

end InterchangeROMOuter

end NearSquareRoot
end Computability
end OAI
