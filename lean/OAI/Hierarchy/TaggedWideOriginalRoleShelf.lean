import OAI.Hierarchy.TaggedWireRoleTableROM

namespace OAI
/-! # Packed site and incident-role ordinal of each dated socket -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles
open AdaptiveProbe ReportSockets ProtocolRAM
open scoped Classical
variable {h W k attempts : ℕ} (S : PurchaseSampler)

def stride (k degree attempts : ℕ) := Incident.room k degree attempts+(1+2*k)+1

/-- The same contiguous role directory is present at every public date.
This encoding is independent of the private paths and terminal stocks. -/
def shelfSlot : Public S h W k attempts ↪ Fin ((siteLast h (2^W) k+1)*stride k S.degree attempts) where
  toFun p := finProdFinEquiv (name (site S p),⟨code S p,code_bound S p⟩)
  inj' := by
    intro a b eqn
    obtain ⟨siteEq,numEq⟩ := Prod.mk.inj (finProdFinEquiv.injective eqn)
    have ab := name.injective siteEq
    exact congrArg Subtype.val ((code_unique S (site S b) ⟨a,ab⟩ ⟨b,rfl⟩).mp (congrArg Fin.val numEq))

theorem shelf_index (p : Public S h W k attempts) :
    (shelfSlot S p).val=(name (site S p)).val*stride k S.degree attempts+code S p := by
  change (finProdFinEquiv
    (name (site S p), (⟨code S p, code_bound S p⟩ : Fin (stride k S.degree attempts)))).val = _
  simp [finProdFinEquiv_apply_val, Nat.mul_comm, Nat.add_comm]

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles

end
end OAI
