import OAI.Hierarchy.TaggedWireHistorySockets
import OAI.Hierarchy.TaggedWireRoleSemantics
import OAI.Hierarchy.TaggedWireRoleIndices

namespace OAI
/-! # The original role and its normalized native endpoint word -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
open scoped Classical
variable {h W k attempts edges : ℕ} (S : PurchaseSampler)

def publicRoleFor (π : Equiv.Perm (Fin (2^h))) (pay : Fin edges→Bool→Public S h W k attempts)
    (x : Old h W k edges) (s : Bool) : Public S h W k attempts :=
  match x with
  | .inl e=>
    let choose:=if name (site S (pay e false))<name (site S (pay e true)) then s else !s
    pay e choose
  | .inr (.inl g)=>.inr (.inl (goods π (g,s)))
  | .inr (.inr c)=>.inr (.inr (c,s))

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram

namespace Hierarchy.ProtocolRAMTurnOperands
open ProbeStage CoreBoard HistoryRoles RoleProgram
variable {h W k attempts : ℕ} (S : PurchaseSampler)

def printed (age : Bool) (p : Bool → Public S h W k attempts) (right siteID : Bool) : ℕ :=
  let z := p (if name (site S (p false)) < name (site S (p true)) then right else !right)
  if siteID then (name (site S z)).val else labelled S age z

end Hierarchy.ProtocolRAMTurnOperands
end

end OAI
