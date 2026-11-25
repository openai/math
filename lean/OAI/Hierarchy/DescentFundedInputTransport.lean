import OAI.Hierarchy.DescentFundedJobCalendar
import OAI.Hierarchy.DescentFundedSetup

namespace OAI
/-! Numerical funding registers across a proved equality of two setup records. -/
namespace Hierarchy.DescentFundedCensus.Setup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {w : ℕ} {a b : Setup} (match_ : a=b)
def oldAt (old : Fin a.blocks→Bank) (j : Fin b.blocks) :=old (j.cast (congrArg Setup.blocks match_).symm)
def signAt (signal : Fin (2*a.capacity)→Expr) (j : Fin (2*b.capacity)) :=
  signal (j.cast (congrArg (fun t:Setup=>2*t.capacity) match_).symm)

include match_ in
theorem roof_at (start : ℕ) : a.roof start=b.roof start:=congrArg (fun x : Setup => x.roof start) match_
include match_ in
theorem primary_at (start : ℕ) : a.primary start=b.primary start:=congrArg (fun x : Setup => x.primary start) match_
theorem secondary_at (start : ℕ) (signal : Fin (2*a.capacity)→Expr) :
    a.secondary start signal=b.secondary start (signAt match_ signal):=by subst b;rfl
theorem read_at (start : ℕ) (old : Fin a.blocks→Bank) (key : Bank) (m : Memory w) :
    a.memory start old key m=b.memory start (oldAt match_ old) key m:=by subst b;rfl

end
end Hierarchy.DescentFundedCensus.Setup

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentFundedCensus
theorem funded_registers {r n k m : ℕ} (d : r=k) (size : n=m) (io : Ports k m) :
    (fundedPorts d size io).old=io.old ∧ (fundedPorts d size io).relay=io.relay ∧
    (fundedPorts d size io).stencil=io.stencil:=by subst k;subst m;exact ⟨rfl,rfl,rfl⟩
theorem funded_bank_all {r n k m : ℕ} (d : r=k) (size : n=m) (io : Ports k m)
    (Q : ProtocolRAM.Expr→Prop) (got : ∀s t,Q (io.bank s t)) :
    ∀s t,Q ((fundedPorts d size io).bank s t):=by subst k;subst m;exact got
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
