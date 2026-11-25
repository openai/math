import OAI.Hierarchy.DescentTerminalScanFacts

namespace OAI
/-! Reading a bank at an in-range natural address recovers its physical memory word. -/
namespace Hierarchy.DescentTerminalDenseHeaderRAM
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing
variable {bits : ℕ}

theorem bank_nat {b : Bank} {out a : ℕ} (m : Memory bits) (fit : b.Fits bits out) (lt : a<b.size) :
    b.read m (a:Word bits)=m (b.base+a) := by
  simp [Bank.read,Fin.val_cast_of_lt (lt.trans fit.2.1),Nat.mod_eq_of_lt lt]

end Hierarchy.DescentTerminalDenseHeaderRAM

end OAI
