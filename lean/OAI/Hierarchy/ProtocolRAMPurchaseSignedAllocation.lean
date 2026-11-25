import OAI.Hierarchy.ProtocolRAMPurchaseAllocation
import OAI.Hierarchy.ProtocolRAMPurchaseSigned
import OAI.Hierarchy.ProtocolRAMPurchaseDispatch

namespace OAI
/-! # The signed marks and gate interpreter on a consecutive stage allocation -/

namespace Hierarchy.ProtocolRAMPurchaseAllocation.Layout
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing

variable {w k : ℕ}

/-- Threshold and stock columns come from the live configuration. Their single
derived mark column occupies the reserved bank before the owner table. -/
def signedInputs (L : ProtocolRAMPurchaseAllocation.Layout) (threshold : Bank)
    (stock : Fin (2*k) → Bank) : PurchaseTape.Signed k := ⟨stock,threshold,L.signed⟩

theorem signedFits (L : ProtocolRAMPurchaseAllocation.Layout) (ct : CT) (threshold : Bank)
    (stock : Fin (2*k) → Bank) (directions : 2*k<2^w)
    (tbl : threshold.Fits w L.signed.base) (hs : ∀ j,(stock j).Fits w L.signed.base)
    (room : L.endAddress<2^w) :
    PurchaseTape.SignedFits (L.plan ct) (L.signedInputs threshold stock) w L.rows := by
  obtain ⟨_,_,h2,h3,h4,h5,_,_,_⟩ := L.regions
  exact ⟨directions,tbl,hs,L.signed_capacity,L.signed_fits room,.inr (by
    change L.signed.base+L.signed.size≤L.gates.base
    omega)⟩

theorem signedFits_of_prefix (L : ProtocolRAMPurchaseAllocation.Layout) (ct : CT) (threshold : Bank)
    (stock : Fin (2*k) → Bank) (directions : 2*k<2^w) (tbl : threshold.Fits w L.start)
    (hs : ∀ j,(stock j).Fits w L.start) (room : L.endAddress<2^w) :
    PurchaseTape.SignedFits (L.plan ct) (L.signedInputs threshold stock) w L.rows := by
  have order : L.start≤L.signed.base := by
    have a := L.regions.start
    have b := L.regions.ids
    omega
  exact L.signedFits ct threshold stock directions ⟨tbl.1,tbl.2.1,tbl.2.2.trans order⟩
    (fun j => ⟨(hs j).1,(hs j).2.1,(hs j).2.2.trans order⟩) room

theorem threshold_loaded (L : ProtocolRAMPurchaseAllocation.Layout)
    (next : Fin L.sockets → List (Fin L.sockets)) (back : Fin L.sockets → Fin L.degree → Fin L.degree)
    (mem : Memory w) (phase : PhasePrice) (T : ℝ) (kind : ℕ) (table : Bank) (ht : table.Fits w L.start)
    (input : PurchaseMarks.Table phase T k kind table mem) :
    PurchaseMarks.Table phase T k kind table (L.data next back mem) :=
  fun r => (L.read_prefix next back mem table ht r).trans (input r)

theorem stratum_loaded (L : ProtocolRAMPurchaseAllocation.Layout)
    (next : Fin L.sockets → List (Fin L.sockets)) (back : Fin L.sockets → Fin L.degree → Fin L.degree)
    (mem : Memory w) (phase : PhasePrice) (T : ℝ) (kind : ℕ) (table : Bank) (stock : Fin (2*k)→Bank)
    (hs : ∀ j,(stock j).Fits w L.start) (j : Fin (2*k)) :
    PurchaseMarks.stratum (n:=L.rows) phase T kind table stock (L.data next back mem) j =
      PurchaseMarks.stratum phase T kind table stock mem j := by
  have eq (r : Word w) : PurchaseMarks.tested phase T kind table stock (L.data next back mem) r =
      PurchaseMarks.tested phase T kind table stock mem r := by
    funext t
    simp only [PurchaseMarks.tested,L.read_prefix next back mem (stock t) (hs t)]
  simp only [PurchaseMarks.stratum,eq]

def dispatchLayout (L : ProtocolRAMPurchaseAllocation.Layout) : PurchaseStage.Dispatch :=
  ⟨L.candidates,L.height+1,L.rows+1,L.first,L.packed,L.work,L.source,L.gates,L.signed⟩

theorem dispatchReady (L : ProtocolRAMPurchaseAllocation.Layout) (ct : CT) (c : L.CTFits ct w)
    (wide : 0<w) (degree : L.degree≤2^w) (room : L.endAddress<2^w) :
    PurchaseStage.DispatchReady L.dispatchLayout w := by
  have size := L.fits ct c wide degree room
  have mark := L.signed_fits room
  obtain ⟨_,_,h2,h3,h4,h5,h6,h7,h8⟩ := L.regions
  have mr : L.signed.Fits w L.packed :=
    ⟨mark.1,mark.2.1,by have hi := mark.2.2; omega⟩
  exact ⟨wide,size.sourceCapacity,size.sourceFit,size.gateFit,mr,h7.le,room⟩

end Hierarchy.ProtocolRAMPurchaseAllocation.Layout

end OAI
