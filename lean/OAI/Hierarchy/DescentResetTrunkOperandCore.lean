import OAI.Hierarchy.DescentResetStemHeaders
import OAI.Hierarchy.DescentResetTrunkGather
import OAI.Hierarchy.DescentResetTrunkIssue

namespace OAI
/-! # Native lookup and cost of a signed trunk descriptor -/
namespace Hierarchy.DescentResetTrunkOperand
open DescentSIMDLookup ProtocolRAM
noncomputable section

def batch (half rows out x j : ℕ) : Bank :=
  ⟨out+(j+half+2*half*x)*rows,Nat.clog 2 rows⟩

def issue (H G M b half base rowBase out scalar hdr x : ℕ) : Expr :=
  let n:=H*chunks G M
  DescentResetTrunkIssue.issue base b M (DescentResetStemHeaders.body H G M (b*7) scalar hdr 0)
    (fun j : Fin half=>DescentResetTrunkGather.issue n rowBase (batch half n out x j.val))

theorem price (H G M b half base rowBase out scalar hdr x : ℕ) :
    (issue H G M b half base rowBase out scalar hdr x).work≤37+28*half:=by
  have measured:=DescentResetTrunkIssue.issue_work base b M (DescentResetStemHeaders.body H G M (b*7) scalar hdr 0)
    (fun j : Fin half=>DescentResetTrunkGather.issue (H*chunks G M) rowBase (batch half (H*chunks G M) out x j.val))
    22 (fun _=>le_rfl)
  change _≤25+(1+half*28)+11 at measured
  rw [Nat.mul_comm half 28] at measured
  exact measured.trans (by omega)


end
end Hierarchy.DescentResetTrunkOperand

end OAI
