import OAI.Hierarchy.TaggedWireTurnBoardNative
import OAI.Hierarchy.TaggedWireRoleSemantics
import OAI.Hierarchy.TaggedWireRoleROM
import OAI.Hierarchy.ProtocolRAMTurnItinerary
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # The complete role and site tables consumed by the signed-turn itinerary -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram
open AdaptiveProbe ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing

namespace Board
variable (b : Board) {w : ℕ}

/-- Slots of the TurnPrefix.edge/starts outputs remain the same. -/
def itinerary (edge starts : Bank) : ProtocolRAMTurnItinerary.Banks where
  oldSource := b.oldRole false
  oldTarget := b.oldRole true
  edge := edge
  tailSite := b.newSite false
  tailRole := b.newRole false
  headRole := b.newRole true
  starts := starts

private theorem bank_at (base n : ℕ) (m : Memory w) (i : Fin n) (room : n≤2^w) :
    (RoleROM.bank base n).read m (i.val:Word w)=m (base+i.val) := by
  rw [Bank.read,Fin.val_cast_of_lt (i.isLt.trans_le room)]
  change m (base+i.val%ProtocolRAMPurchaseSampler.span n)=m (base+i.val)
  rw [Nat.mod_eq_of_lt (i.isLt.trans (ProtocolRAMPurchaseSampler.lt_span _))]

variable {h W k attempts : ℕ} (S : PurchaseSampler)

theorem old_observed (m : Memory w) (ready : b.Ready w) (i : Fin b.old)
    (p : Bool→Public S h W k attempts) (seen : ∀s,Resolved S b.chart (b.before s) m (i.val:Word w) (p s))
    (fit : siteLast h (2^W) k+1≤2^w) (right : Bool) :
    (b.oldSite right).read (b.final m) (i.val:Word w)=actual S false p right true ∧
    (b.oldRole right).read (b.final m) (i.val:Word w)=actual S false p right false := by
  have all:=fields S b.chart m (i.val:Word w) b.before p false seen fit
  have obs:=(b.output m ready).2.1
  have h:=ready.room
  unfold endAt newBase at h
  have room : b.old≤2^w := by omega
  have atWord (j : Fin 4) := obs j i
  have atSite0 := (atWord 0).trans all.1
  have atSite1 := (atWord 1).trans all.2.1
  have atRole0 := (atWord 2).trans all.2.2.1
  have atRole1 := (atWord 3).trans all.2.2.2
  change b.final m (b.base + 0 * b.old + i.val) = _ at atSite0
  change b.final m (b.base + 1 * b.old + i.val) = _ at atSite1
  change b.final m (b.base + 2 * b.old + i.val) = _ at atRole0
  change b.final m (b.base + 3 * b.old + i.val) = _ at atRole1
  cases right
  · simpa [oldSite, oldRole, bank_at _ _ _ i room] using And.intro atSite0 atRole0
  · simpa [oldSite, oldRole, bank_at _ _ _ i room] using And.intro atSite1 atRole1

theorem new_observed (m : Memory w) (ready : b.Ready w) (i : Fin b.edges)
    (p : Bool→Public S h W k attempts) (seen : ∀s,Resolved S b.chart (b.finish s) m (i.val:Word w) (p s))
    (fit : siteLast h (2^W) k+1≤2^w) (right : Bool) :
    (b.newSite right).read (b.final m) (i.val:Word w)=actual S true p right true ∧
    (b.newRole right).read (b.final m) (i.val:Word w)=actual S true p right false := by
  have all:=fields S b.chart m (i.val:Word w) b.finish p true seen fit
  have obs:=(b.output m ready).2.2.1
  have h:=ready.room
  unfold endAt at h
  have room : b.edges≤2^w := by omega
  have atWord (j : Fin 4) := obs j i
  have atSite0 := (atWord 0).trans all.1
  have atSite1 := (atWord 1).trans all.2.1
  have atRole0 := (atWord 2).trans all.2.2.1
  have atRole1 := (atWord 3).trans all.2.2.2
  change b.final m (b.newBase + 0 * b.edges + i.val) = _ at atSite0
  change b.final m (b.newBase + 1 * b.edges + i.val) = _ at atSite1
  change b.final m (b.newBase + 2 * b.edges + i.val) = _ at atRole0
  change b.final m (b.newBase + 3 * b.edges + i.val) = _ at atRole1
  cases right
  · simpa [newSite, newRole, bank_at _ _ _ i room] using And.intro atSite0 atRole0
  · simpa [newSite, newRole, bank_at _ _ _ i room] using And.intro atSite1 atRole1

end Board
end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.RoleProgram

end
end OAI
