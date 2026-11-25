import OAI.Hierarchy.ProbeStripDirectoryCore
import OAI.Hierarchy.ProtocolRAMStoredBoughtLocations

namespace OAI
/-! # The column ROM and the stock chart use the same affirmative DFS ordinal -/

noncomputable section
namespace Hierarchy.ProtocolRAM.StripDirectory
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseFrozen
open scoped Classical Fin.CommRing

variable {z d k : ℕ} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^z))} {depth : ℕ}
local notation "W" => wordBits z d copies

/-- Read the stock key at the same canonical DFS row used by the column ROM. -/
theorem relative_stock_at (sh : Shelf) (start : ℕ)
    (marked : StageAt z d → Fin k × Bool → Finset (Fin (2^z)))
    (p : LiveChains S π depth marked) (m : Shelf.Mem z d)
    (tiles : ProtocolRAMPurchaseGateColumns.TileRows
      (sh.L S depth (BoughtLocation.keyOf p)).source (Shelf.pathRows S π depth (BoughtLocation.keyOf p)) m)
    (headers : (stratumHeader z d k S.degree depth start).Loaded m)
    (keys : count z d k ≤ 2^W) (room : (depth+1)*paths z S.degree depth ≤ 2^W)
    (u : ChainStrip.Axes depth k) :
    let head := stratumHeader z d k S.degree depth start
    (allChainSlot (z:=z) (d:=d) sh S depth head u).eval m ((BoughtLocation.relative p).val:Word W) =
      (PurchaseInventory.slot (stripAddress S π depth marked p u):Word W) := by
  intro head
  let i := BoughtLocation.keyOf p
  let r := BoughtLocation.localRow p
  have decoded := header_pair head m headers i r
  have fit := i.isLt.trans_le keys
  have cols := allChainSlot_read sh S depth head u m ((head.enum ⟨i,r⟩).val:Word W) i (r.val:Word W)
    keys (by rw [decoded.1,Fin.val_cast_of_lt fit]) decoded.2
  apply cols.trans
  have tile := congrArg Fin.val (BoughtLocation.rows p u.1)
  have value := keySlot_tiles sh S π depth i m tiles room (BoughtLocation.localIndex p) u
    (liveRow S π depth marked p u.1) tile
  simpa only [stripAddress,i,r,BoughtLocation.keyOf,BoughtLocation.localRow,stage_key] using value

theorem relative_stock (sh : Shelf) (start : ℕ)
    (marked : StageAt z d → Fin k × Bool → Finset (Fin (2^z)))
    (p : LiveChains S π depth marked) (m : Shelf.Mem z d)
    (tiles : ∀ i : Key z d k, ProtocolRAMPurchaseGateColumns.TileRows
      (sh.L S depth i).source (Shelf.pathRows S π depth i) m)
    (headers : (stratumHeader z d k S.degree depth start).Loaded m)
    (keys : count z d k ≤ 2^W) (room : (depth+1)*paths z S.degree depth ≤ 2^W)
    (u : ChainStrip.Axes depth k) :
    let head := stratumHeader z d k S.degree depth start
    (allChainSlot (z:=z) (d:=d) sh S depth head u).eval m ((BoughtLocation.relative p).val:Word W) =
      (PurchaseInventory.slot (stripAddress S π depth marked p u):Word W) :=
  relative_stock_at sh start marked p m (tiles (BoughtLocation.keyOf p)) headers keys room u

/-- On each original nonzero flag, the purchased stock equivalence identifies
the very same row used by the immutable column directory. -/
theorem liveBoardEquiv_relative (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (depth start : ℕ) (_hk : 0<k) (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen m : Shelf.Mem z d)
    (tiles : ∀ i : Key z d k, ProtocolRAMPurchaseGateColumns.TileRows
      (sh.L S depth i).source (Shelf.pathRows S π depth i) m)
    (flags : ∀ (i : Key z d k) (r : Fin (paths z S.degree depth)),
      m (sh.flagsBase S z d k depth+i.val*paths z S.degree depth+r.val) =
        MarkTape.encode W ((sh.decisions S π depth phase T kind frozen i)[r.val]'(by simp)))
    (headers : (stratumHeader z d k S.degree depth start).Loaded m)
    (keys : count z d k ≤ 2^W) (room : (depth+1)*paths z S.degree depth ≤ 2^W)
    (whole : count z d k*paths z S.degree depth ≤ 2^W) (_wide : 0<W)
    (_stock : PurchaseInventory.footprint z (permutationFabric z d).shapes.length k ≤ 2^W) :
    let head := stratumHeader z d k S.degree depth start
    let marks := actualMarks sh phase T kind frozen (k:=k)
    let Active := {i : Fin head.count // (flagBank sh S z d k depth).read m (i.val:Word W) ≠ 0}
    ∃ board : Active ≃ LiveChains S π depth marks,
      (∀ i, BoughtLocation.relative (board i) = i.val) ∧ ∀ i u,
        (allChainSlot (z:=z) (d:=d) sh S depth head u).eval m (i.val.val:Word W) =
          (PurchaseInventory.slot (stripAddress S π depth marks (board i) u):Word W) := by
  intro head marks Active
  let packed := BoughtLocation.packedEquiv (S:=S) (π:=π) (depth:=depth) sh phase T kind frozen m flags
  let bank := flagBank sh S z d k depth
  have read (i : Fin head.count) :
      bank.read m (i.val:Word W) = m (sh.flagsBase S z d k depth+i.val) := by
    change m (sh.flagsBase S z d k depth+((i.val:Word W).val%bank.size)) = _
    have inBank : i.val < bank.size :=
      i.isLt.trans (show head.count < bank.size from ProtocolRAMPurchaseSampler.lt_span _)
    rw [Fin.val_cast_of_lt (i.isLt.trans_le whole),Nat.mod_eq_of_lt inBank]
  let flag : Active ≃ BoughtLocation.Yes head.count (sh.flagsBase S z d k depth) m :=
    Equiv.subtypeEquivRight (fun i => by
      change bank.read m (i.val:Word W)≠0 ↔ m (sh.flagsBase S z d k depth+i.val)≠0
      rw [read i])
  let board := flag.trans packed.symm
  have ordinal (i : Active) : BoughtLocation.relative (board i) = i.val := by
    change (packed (packed.symm (flag i))).val=(flag i).val
    exact congrArg (fun u : BoughtLocation.Yes head.count (sh.flagsBase S z d k depth) m=>u.val)
      (packed.apply_symm_apply (flag i))
  refine ⟨board,ordinal,?_⟩
  intro i u
  have fetched := relative_stock sh start marks (board i) m tiles headers keys room u
  rw [ordinal i] at fetched
  exact fetched

end Hierarchy.ProtocolRAM.StripDirectory
end

end OAI
