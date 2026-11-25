import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # Reading an actual dense bank at a bounded natural address -/
namespace Hierarchy.DescentIssuedTerminalId
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
variable {w : ℕ}
theorem lookup_nat (b : Bank) (m : Memory w) (r : Word w) (a : Expr) (x : ℕ)
    (read : a.eval m r=(x:Word w)) (fits : x<b.size) (wide : b.size<2^w) :
    (Expr.lookup b a).eval m r=m (b.base+x) := by
  change b.read m (a.eval m r)=_
  simp only [read,Bank.read,Fin.val_cast_of_lt (fits.trans wide),Nat.mod_eq_of_lt fits]

end Hierarchy.DescentIssuedTerminalId

end OAI
