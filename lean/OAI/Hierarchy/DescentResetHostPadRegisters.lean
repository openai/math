import OAI.Hierarchy.DescentResetPriorHostPad
import OAI.Hierarchy.DescentPriorResetArchive
import OAI.Hierarchy.DescentResetPriorRegisterRoom

namespace OAI
/-! # Source and destination addresses of the reset's initial host-alignment passes -/
namespace Hierarchy
open DescentSixParty.Chronology DescentResetPriorHostPad DescentResetRetainedSetup
open DescentDatedAddressBook DescentDatedPriorOperand DescentDatedNodeMetadata DescentOperandStateBanks
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
noncomputable section

def DescentSixParty.Chronology.DatePorts.padded (p : DatePorts) (s : Shape) (base : ℕ) : DatePorts:=
  {p with archive:=s.history base p.archive,operandHosts:=s.newHosts}

namespace DescentResetRetainedSetup.Layout
variable (v : DescentResetRetainedSetup.Layout)

def inputShape (p : DatePorts) : Shape :=
  ⟨p.operandHosts,v.hosts,v.groups,v.blocks,v.previousArgs,v.previousLanes,p.roleLanes⟩

def inputSources (p : DatePorts) : Fin (v.inputShape p).dataRect.pages→Bank :=
  p.archive.prior {v with hosts:=p.operandHosts}
def inputRoles (p : DatePorts) (x : Fin v.blocks) : Bank :=p.archive.roles.bank x.val

theorem padded_role (p : DatePorts) (base : ℕ) (x : Fin v.blocks) :
    (p.padded (v.inputShape p) base).archive.roles.bank x.val=(v.inputShape p).roleBank base x:=rfl

/-- Flattening the two front metadata pages followed by the seven argument pages
uses precisely the address of the corresponding host-padded scan. -/
theorem padded_operand (p : DatePorts) (base : ℕ) (j : Fin v.sources) :
    (p.padded (v.inputShape p) base).archive.prior v j=(v.inputShape p).operandBank base j:=by
  obtain ⟨⟨f,x⟩,rfl⟩:=(finProdFinEquiv : (Fin v.fields × Fin v.blocks) ≃ Fin v.sources).surjective j
  change v.seedPrior base (base+(2*v.blocks)*v.previousLayout.rows) (finProdFinEquiv (f,x))=_
  unfold seedPrior priorBanks directory
  simp only [Equiv.symm_apply_apply]
  split
  · simp only [Chart.seedBank,Chart.slot,previousChart,Shape.operandBank,
      Shape.dataRect,DescentOrdinaryHostPad.Rect.bank,DescentOrdinaryHostPad.Rect.placedBank,
      DescentOrdinaryHostPad.Rect.rows,inputShape,Chart.rows,finProdFinEquiv_apply_val]
    rfl
  · rename_i absent
    apply congrArg (fun u : ℕ=>Bank.mk u (Nat.clog 2 (v.previousLayout.rows+1)))
    change base+(2*v.blocks)*v.previousLayout.rows+(f.val-2)*(v.blocks*v.previousLayout.rows)+
      x.val*v.previousLayout.rows=base+(finProdFinEquiv (f,x)).val*v.previousLayout.rows
    rw [finProdFinEquiv_apply_val]
    have decomp : f.val-2+2=f.val:=Nat.sub_add_cancel (by omega)
    calc
      _ = base+((f.val-2+2)*v.blocks+x.val)*v.previousLayout.rows:=by ring
      _ = _:=by rw [decomp]; ring

theorem normalized_registers {w : ℕ} (p : DatePorts) (base : ℕ)
    (room : (v.inputShape p).endAddress base<2^w) :
    (∀j,((p.padded (v.inputShape p) base).archive.prior v j).Fits w ((v.inputShape p).endAddress base)) ∧
      ∀x : Fin v.blocks,((p.padded (v.inputShape p) base).archive.roles.bank x.val).Fits w ((v.inputShape p).endAddress base):=by
  constructor
  · intro j;rw [v.padded_operand];exact ((v.inputShape p).operand_fit base room j).1
  · intro x;rw [v.padded_role];exact ((v.inputShape p).role_fit base room x).1

theorem normalized_limits (p : DatePorts) (base : ℕ) :
    let s:=v.inputShape p
    let z:=p.padded s base
    v.priorMetaLimit z.archive.seed z.archive.nodeBase≤ s.endAddress base ∧
      v.priorOperandLimit z.archive.arguments≤ s.endAddress base:=by
  intro s z
  have role:=s.cuts base
  have rows : v.previousLayout.rows=s.dataRect.rows:=rfl
  change base+(2*v.blocks)*s.dataRect.rows+2^Nat.clog 2 (s.dataRect.rows+1)≤ s.endAddress base ∧
    base+(2*v.blocks)*s.dataRect.rows+(7*v.previousArgs)*(v.blocks*v.previousLayout.rows)+2^Nat.clog 2 (v.previousLayout.rows+1)≤ s.endAddress base
  rw [rows]
  have end₁ : s.roleStart base=base+(((2+7*v.previousArgs)*v.blocks+1)*s.dataRect.rows)+2^Nat.clog 2 (s.dataRect.rows+1):=rfl
  constructor <;> apply le_trans _ role.2 <;> rw [end₁] <;> ring_nf <;> omega

end DescentResetRetainedSetup.Layout
end
end Hierarchy

end OAI
