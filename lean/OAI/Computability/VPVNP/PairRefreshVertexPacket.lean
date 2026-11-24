import OAI.Computability.VPVNP.CompressorRefreshMapOperands
import OAI.Computability.VPVNP.PairSimulationNodeFieldSpace
import OAI.Computability.VPVNP.PairNodeChildPackets
import OAI.Computability.VPVNP.PairVertexControl

/-!
# Resident refresh arguments after guessing the unique child

The one packet of the refresh placement is stored in its old-node frame.
The newer parent frame and the DFS geometry cells retain their values.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshVertexPacket

open BurstRAM BurstRAM.PrivateRAM Compression NodeArguments LocalHistory CompressorRecords.RefreshMapOperands
open NodeArguments.ChildScan
open scoped Fin.CommRing

variable {bits a g b l : ℕ} (X : State a g) (site : X.network.Site) (old : X.network.Half site)
  (A : Arena) (older cap : ℕ) (priv : Word bits → Word bits)

local notation "child" => childNode X older cap site
local notation "bitsList" => packed X site old
local notation "afterChild" => storePackets A [Child.packet X older cap (Child.ofHalf X site old)] priv

theorem stored : afterChild = PrivateFields.storeBits (A.base child) bitsList priv := by
  change PrivateFields.storeBits (A.base child) ((Child.ofHalf X site old).payload X) priv = _
  rw [Child.payload_ofHalf]

theorem fields (fit : A.base child+(bitsList).length ≤ 2^bits) :
    NodeFields A child X site old afterChild := by
  rw [stored]
  exact nodeFields_store A child X site old priv fit

theorem outside (fit : A.base child+(bitsList).length ≤ 2^bits) (q : Word bits)
    (sep : q.val < A.base child ∨ A.base child+(bitsList).length ≤ q.val) : afterChild q = priv q := by
  rw [stored]
  exact PrivateFields.storeBits_outside _ _ _ q fit sep

/-- A child preceding its parent cannot overwrite any of the parent's bits. -/
theorem parent_fields (Y : State b l) (u : Y.network.Site) (new : Y.network.Half u) (parent : ℕ)
    (before : child < parent) (width : (bitsList).length ≤ A.stride)
    (fit : A.base parent + (packed Y u new).length ≤ 2^bits)
    (held : NodeFields A parent Y u new priv) : NodeFields A parent Y u new afterChild := by
  have endBefore := (Nat.add_le_add_left width _).trans (A.before before)
  have childFit := endBefore.trans ((Nat.le_add_right ..).trans fit)
  intro dir j i
  let pos := A.fieldAddress Y u parent dir j + i.val
  have within : pos < 2^bits := (Nat.add_lt_add_left i.isLt _).trans_le ((field_end_le Y u new A parent dir j).trans fit)
  have starts : A.base parent ≤ pos := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have word : (pos : Word bits).val = pos := Nat.mod_eq_of_lt within
  exact (outside X site old A older cap priv childFit _ (Or.inr (word ▸ endBefore.trans starts))).trans (held dir j i)

/-- The retained stack-end pointer lies below the packet; both geometry slots
lie above it. The predicate therefore holds after the native child stores. -/
theorem geometry {endAddr : ℕ} (G offset hist : Word bits)
    (resident : VertexImage.ResidentGeometry (DFS.scratch endAddr priv) G offset hist)
    (early : endAddr < A.base child) (role : A.base child+(bitsList).length ≤ (G+10).val)
    (histogram : A.base child+(bitsList).length ≤ (G+11).val) :
    VertexImage.ResidentGeometry (DFS.scratch endAddr afterChild) G offset hist := by
  have fit := role.trans (G+10).isLt.le
  have endVal : (endAddr : Word bits).val = endAddr := Nat.mod_eq_of_lt resident.endFit
  have keep (q : Word bits) (atEnd : endAddr ≤ q.val) (sep : q.val < A.base child ∨ A.base child+(bitsList).length ≤ q.val) :
      rawScratch (DFS.scratch endAddr afterChild) q = rawScratch (DFS.scratch endAddr priv) q := by
    simpa only [rawScratch,dite_eq_left atEnd,DFS.scratch] using outside X site old A older cap priv fit q sep
  exact ⟨resident.endFit,resident.roleAbove,resident.histAbove,
    (keep _ endVal.ge (Or.inl (endVal.trans_lt early))).trans resident.pointer,
    (keep _ resident.roleAbove (Or.inr role)).trans resident.role,
    (keep _ resident.histAbove (Or.inr histogram)).trans resident.histogram⟩

end PairSimulation.RefreshVertexPacket

end VPVNP
end Computability
end OAI
