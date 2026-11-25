import OAI.Hierarchy.TraceReceiverMapProgram
import OAI.ThreeFlat.RAM.TickTerminalRoot

namespace OAI
/-! # Charge of one emitted terminal-root map -/
namespace Hierarchy.TraceReceiverTasks
open ThreeFlat RAM DescriptorExpr DescriptorScan
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure
open scoped Classical Fin.CommRing
open RAM.TickTerminalRoot

private theorem priced (seed native pins charge rate coefficient portRate : ℕ)
    (positive : 1 ≤ charge) (work : native ≤ rate*(coefficient*charge))
    (ports : pins ≤ portRate*charge) :
    seed+native+(13+22*pins)+7 ≤ (rate*coefficient+22*portRate+seed+20)*charge := by
  rw [← Nat.mul_assoc] at work
  have pinCharge := Nat.mul_le_mul_left 22 ports
  rw [← Nat.mul_assoc] at pinCharge
  have fixed := Nat.mul_le_mul_left (seed+20) positive
  rw [Nat.mul_one, Nat.add_mul] at fixed
  rw [Nat.add_mul,Nat.add_mul,Nat.add_mul]
  omega

/-- The priced loop uses the same S13 root and the same per-node charge as the
selected cache publisher; the linear map copy adds a charge per actual pin. -/
theorem root_time (W : ℕ) (A : Arena) (head tasks : ℕ)
    (T : RAM.HistoryTerminalTape.Root) (raw : ℕ → ℕ)
    {degreeCap pairs charge rowRate portRate : ℕ}
    (degree : T.halves ≤ degreeCap) (paired : T.ext ≤ 2*pairs)
    (mass : 1+(∑ j : Fin T.halves,(RAM.HistoryTerminalTape.half T raw j.val).width)+pairs ≤ charge)
    (rows : T.rows ≤ rowRate*charge) (ports : T.localPins ≤ portRate*charge) :
    let seed := 4+3*(2*(TraceReceiverMapSave.seedWord W head tasks A.control).binds+4)
    seed+oneCost W A T raw+(13+22*T.localPins)+7
      ≤ (rootFactor*(degreeCap+4*rowRate+3)+22*portRate+
        (4+3*(2*(TraceReceiverMapSave.seedWord 1 0 0 0).binds+4))+20)*charge := by
  have work := (work_bound W A T raw).trans (Nat.mul_le_mul_left rootFactor
    (charge_covers T raw degree paired mass rows))
  have seedEq : (TraceReceiverMapSave.seedWord W head tasks A.control).binds =
      (TraceReceiverMapSave.seedWord 1 0 0 0).binds := by
    simp only [TraceReceiverMapSave.seedWord,Term.select,Term.load,Term.binary,Term.literal,
      Term.binds_letThen,Term.binds_rename,Term.binds]
  dsimp only
  rw [seedEq]
  exact priced _ _ _ _ _ _ _ (by omega) work ports

end Hierarchy.TraceReceiverTasks

end OAI
