import OAI.Hierarchy.ProbePurchasedBoardEquiv
import OAI.Hierarchy.ProbePayloadAccounts
import OAI.Hierarchy.ProtocolRAMRepairCommodity

namespace OAI
/-! # Injectivity of the real payload and purchased inventory operands -/

noncomputable section
namespace Hierarchy.ProtocolRAM.StripDirectory
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage PurchaseFrozen
open scoped Classical Fin.CommRing
variable {z d k N w : ℕ}
local notation "W" => Native.wordBits z d Native.copies

/-- Restricting a joint incidence embedding to a subset of rows preserves its
actual target coordinate. -/
def restrictPorts {X Y A G : Type*} (row : X ↪ Y) (place : Y × A ↪ G) : X × A ↪ G where
  toFun v := place (row v.1,v.2)
  inj' := by
    rintro ⟨i,a⟩ ⟨j,b⟩ h
    obtain ⟨same,rfl⟩ := Prod.mk.inj (place.injective h)
    exact congrArg (fun p => (p,a)) (row.injective same)

/-- Payload reads range over an explicit equivalence with all physical bank slots.
The result also applies when only a proper subset passes the repair check. -/
theorem payload_slot_embedding {R : Type*} (row : R ↪ Fin (2^z)) (m : Memory w)
    (room : PurchaseInventory.footprint z N k ≤ 2^w) :
    ∃ place : R × PayloadStrip.Quotes N k ↪ Fin (PurchaseInventory.footprint z N k),
      ∀ r a,((payloadSlot z a).eval m ((row r).val:Word w)).val=(place (r,a)).val := by
  let e := PayloadStrip.allAddresses (P:=Fin (2^z)) (N:=N) (k:=k)
  refine ⟨restrictPorts row (e.trans (PurchaseInventory.slotEquiv z N k)).toEmbedding,?_⟩
  intro r a
  rw [payloadSlot_read]
  exact Fin.val_cast_of_lt ((PurchaseInventory.slot_lt _).trans_le room)

/-- The replayed physical flags recover disjoint selected paths. Their actual
word operands name different global commodity slots, including when two rows
come from different signed threshold strata. -/
theorem purchased_slot_embedding (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (depth start : ℕ) (hk : 0<k) (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen m : Shelf.Mem z d)
    (tiles : ∀ key : Key z d k,ProtocolRAMPurchaseGateColumns.TileRows (sh.L S depth key).source
      (Shelf.pathRows S π depth key) m)
    (flags : StoredFlags sh S π depth phase T kind frozen m k)
    (loaded : (stratumHeader z d k S.degree depth start).Loaded m)
    (keys : count z d k ≤ 2^W) (room : (depth+1)*paths z S.degree depth ≤ 2^W)
    (whole : count z d k*paths z S.degree depth ≤ 2^W) (wide : 0<W)
    (stock : PurchaseInventory.footprint z (permutationFabric z d).shapes.length k ≤ 2^W) :
    let header := stratumHeader z d k S.degree depth start
    let Active := {i : Fin header.count // (flagBank sh S z d k depth).read m (i.val:Word W) ≠ 0}
    ∃ place : Active × ChainStrip.Axes depth k ↪ Fin (PurchaseInventory.footprint z (permutationFabric z d).shapes.length k),
      ∀ r a,((allChainSlot (z:=z) (d:=d) sh S depth header a).eval m (r.val.val:Word W)).val =
        (place (r,a)).val := by
  intro header Active
  let marked := actualMarks sh phase T kind frozen (k:=k)
  obtain ⟨board,reads⟩ := liveBoardEquiv sh S π depth start hk phase T kind frozen m tiles flags loaded
    keys room whole wide stock
  let slots := allSignedAddresses S π depth marked (actualMarks_unique sh phase T kind frozen)
  let ord := PurchaseInventory.slotEquiv z (permutationFabric z d).shapes.length k
  refine ⟨restrictPorts board.toEmbedding (slots.trans ord.toEmbedding),?_⟩
  intro r a
  rw [reads]
  exact Fin.val_cast_of_lt ((PurchaseInventory.slot_lt _).trans_le stock)

end Hierarchy.ProtocolRAM.StripDirectory
end

end OAI
