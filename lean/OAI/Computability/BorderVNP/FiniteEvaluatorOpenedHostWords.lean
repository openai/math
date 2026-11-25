import OAI.Computability.BorderVNP.FiniteEvaluatorOpenBoxDelivery
import OAI.Computability.BorderVNP.CubeHostScatterPhysicalReadback

/-! # Real post-host supplied words across the remaining finite opening passes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM RoutingISA.Evaluator FiniteEvaluator Packing BorderVNP.Cube
open private host_order from OAI.Computability.BorderVNP.FiniteEvaluatorCubeHostFits

/-- The true bundle and control writer preserve each word from the host
scatter inside the selected cell deck, including both crossing endpoints
and the original free-port operands. -/
theorem Layout.opened_host_word (a : Layout) {w : ℕ} {pub : Arg → Word w} {entry : Memory w}
    {regs : Bank w} {mac : TeamOpcode.Macros w 8} (H : OpenSuffix.Inputs)
    (ready : OpenSuffix.Ready H (pub 0).val (readings entry) w)
    (placed : OpenSuffix.Placement H a.cube a.before (pub 0).val (readings entry))
    (first : (pub 0).val+112 ≤ a.cube.header.header)
    (opened : Returns OpenSuffix.code pub mac regs entry) (c : Fin a.cube.cells)
    (j : Fin a.cube.cellStride) :
    let k := a.cube.cellBank+c.val*a.cube.cellStride+j.val
    readings opened.val.2.2 k=OpenSuffix.hostImage (pub 0).val (readings entry) k := by
  intro k
  have past : a.cube.stop ≤ a.before.start := by
    apply le_trans _ a.constants_le_before
    unfold CubeConstants.arenaEnd CubeConstants.idBase
    omega
  have deck := OpenSuffix.afterDeck_of_allocation H a.before past placed.ranges placed.bundles placed.four placed.six
  have below : k<a.cube.stop := by
    have limit := Nat.mul_le_mul_right a.cube.cellStride c.isLt
    rw [Nat.succ_mul] at limit
    change a.cube.cellBank+c.val*a.cube.cellStride+j.val<a.cube.cellBank+a.cube.cells*a.cube.cellStride
    have := j.isLt
    omega
  apply HostScatter.read_host_after_controls H ready opened.property k
  · exact Or.inl (below.trans_le deck.ranges)
  · exact Or.inl (below.trans_le deck.bundles)
  · have start := first.trans (host_order a.cube).1
    have four := deck.four
    have six := deck.six
    simp only [CellControlRows.Layout.outputs,ready.controlBase]
    dsimp only [k] at *
    omega

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
