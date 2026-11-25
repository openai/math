import OAI.Hierarchy.ProtocolRAMStripSlabData
import OAI.Hierarchy.ProbeShapeMenus
import OAI.Hierarchy.ProtocolRAMPurchaseFrozenCount
import OAI.Hierarchy.ProtocolRAMCoreRouteOrder
import OAI.Hierarchy.ProtocolRAMCatalystLayoutTypes
import OAI.Hierarchy.ProtocolRAMCatalystArchiveRank

namespace OAI
/-! # Six immutable terminal banks allocated ahead of the event arena -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart.Slab
open Hierarchy.ProbeStage.CoreBoard
open Hierarchy.ProtocolRAM.CatalystArchive
open Hierarchy.ProtocolRAM.StripDirectory
open Hierarchy.ProtocolRAM.Calendar.CoreRoute
open scoped Classical
/-- Width of the original signed rectangle at each real attempt. It is fixed
before the boards, monetary history, terminal scratch or permutation are chosen. -/
def signedWidth (z d k degree depth : ℕ) :=
  PurchaseFrozen.count z d k*PurchaseFrozen.paths z degree depth*
    max (Fintype.card (PayloadRole (Stages z d) k)) (Fintype.card (PurchasedRole depth k))

def publicRows (c : Mesh) (z d k degree depth : ℕ) (a : Attempt) : ℕ :=
  if Event.attempt a∈events c then signedWidth z d k degree depth else 0

def publicEntries (c : Mesh) (z d k degree depth : ℕ) :=
  rowOnlyCount c (publicRows c z d k degree depth)

/-- The quotient and parity native read each have one word for every
member of the interleaved original route tape. -/
def pairOwners (base r : ℕ) : Bank := ⟨base,(2*r).log2+1⟩
def pairParity (base r : ℕ) : Bank := ⟨base+(pairOwners base r).size,(2*r).log2+1⟩
def staticStart (base r : ℕ) := (pairParity base r).base+(pairParity base r).size

theorem staticStart_le (base r : ℕ) : staticStart base r≤base+8*r+4 := by
  have round : 2^((2*r).log2+1)≤2*(2*r)+2 := by
    by_cases zero : 2*r=0
    · simp [zero]
    · have h:=Nat.log2_self_le zero
      rw [pow_succ]
      omega
  change base + 2^((2*r).log2+1) + 2^((2*r).log2+1) ≤ base+8*r+4
  omega

def terminalOwnerPage (prior : Slab) (c : Mesh) (z d k degree depth rows : ℕ) :=
  sinkBank (staticStart prior.headerEnd (Fintype.card (Slots z d k))) (publicEntries c z d k degree depth) (Fintype.card (Slots z d k)) rows

/-- The complete earlier paid header, including its score read padding, is
followed by the two pointers, three route pages, and the sink owner page. -/
def withTerminal (prior : Slab) (c : Mesh) (z d k degree depth rows : ℕ) : Slab :=
  let owner:=terminalOwnerPage prior c z d k degree depth rows
  {prior with headerEnd:=owner.base+owner.size}

theorem staticStart_before (prior : Slab) (c : Mesh) (z d k degree depth rows : ℕ) :
    staticStart prior.headerEnd (Fintype.card (Slots z d k))≤(withTerminal prior c z d k degree depth rows).headerEnd := by
  unfold withTerminal terminalOwnerPage sinkBank routeBanks
  exact (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans
    ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))

theorem prior_le (prior : Slab) (c : Mesh) (z d k degree depth rows : ℕ) :
    prior.headerEnd≤(withTerminal prior c z d k degree depth rows).headerEnd := by
  unfold withTerminal terminalOwnerPage sinkBank routeBanks staticStart pairParity pairOwners
  dsimp
  omega

end Hierarchy.ProtocolRAM.Calendar.StripChart.Slab
end

end OAI
