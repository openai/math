import OAI.Hierarchy.ProtocolRAMCalendarPaidSlices
import OAI.Hierarchy.ProtocolRAMPaidPairDirectory
import OAI.Hierarchy.ProtocolRAMPaidSliceFits

namespace OAI
/-! # Actual row directories of every sparse paid event on the original calendar tape -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.PaidEventDirectory
open Computability.VPVNP.BurstRAM PrivateRAM RepairHistogram
open scoped Classical Fin.CommRing
variable {W z d k q goods r edges : ℕ}

def Rows (occ parity : Bank) (m : Memory W) (n : ℕ) : Prop :=
  PairDirectory ⟨occ,parity,.row,.row,.row⟩ m n

theorem of_loaded (h : StockCommit.PortHeader) (m : Memory W) (loaded : h.Loaded m) :
    Rows h.owner h.parity m h.count := loaded.pair

theorem of_reads (occ parity : Bank) (m : Memory W) (cap : ℕ) (read : PaidPairDirectory.Reads occ parity cap m)
    (size : 2*cap≤2^W) (owners : 2*cap≤occ.size) (tags : 2*cap≤parity.size) (w : 0<W) :
    Rows occ parity m cap := by
  let s : PaidWidths.Slice := ⟨cap,occ,parity,.row,.row⟩
  have dir := PaidPairDirectory.directory read size owners tags w s occ 0 rfl rfl (le_refl cap)
  exact ⟨dir.first,dir.second,dir.firstRow,dir.secondRow⟩

theorem all_shapes (mesh : Mesh) (format : Attempt→Format z d k q goods) (feeds : Boundary→List CommodityColumn)
    (sink : Sink r edges) (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr)
    (tree core : Attempt→Traversals) (boundary : Boundary → CommodityColumn→Traversals) (maxBits : ℕ)
    (shape : Bank→Bank→ℕ→Prop)
    (ordinary : ∀a,Event.attempt a∈events mesh→shape (format a).stockSource.owner (format a).stockSource.parity
      (format a).pricedArea.occurrences)
    (forest : ∀a,Event.attempt a∈events mesh→shape (tree a).owner (tree a).parity (tree a).positions)
    (route : ∀a,Event.attempt a∈events mesh→shape (core a).owner (core a).parity (core a).positions)
    (feed : ∀b,Event.feed b∈events mesh→∀c∈feeds b,shape (boundary b c).owner (boundary b c).parity (boundary b c).positions) :
    ∀s∈paidSlices mesh format feeds sink idBase role ids tree core boundary maxBits,shape s.owner s.parity s.count := by
  intro s hs
  obtain ⟨e,he,entry⟩ := List.mem_flatMap.mp hs
  cases e with
  | feed b =>
    obtain ⟨c,active,rfl⟩ := List.mem_map.mp entry
    exact feed b he c active
  | attempt a =>
    cases mate : (tree a).catalystMate with
    | none =>
      simp [eventSlices,Format.paidSlices,Format.mateSlices,mate] at entry
      rcases entry with rfl|rfl|rfl
      · exact ordinary a he
      · exact forest a he
      · exact route a he
    | some t =>
      simp [eventSlices,Format.paidSlices,Format.mateSlices,mate] at entry
      rcases entry with rfl|rfl|rfl|rfl
      · exact ordinary a he
      · exact ordinary a he
      · exact forest a he
      · exact route a he

theorem all_rows (mesh : Mesh) (format : Attempt→Format z d k q goods) (feeds : Boundary→List CommodityColumn)
    (sink : Sink r edges) (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr)
    (tree core : Attempt→Traversals) (boundary : Boundary → CommodityColumn→Traversals) (maxBits : ℕ)
    (m : Memory W)
    (ordinary : ∀a,Event.attempt a∈events mesh→Rows (format a).stockSource.owner (format a).stockSource.parity m
      (format a).pricedArea.occurrences)
    (forest : ∀a,Event.attempt a∈events mesh→Rows (tree a).owner (tree a).parity m (tree a).positions)
    (route : ∀a,Event.attempt a∈events mesh→Rows (core a).owner (core a).parity m (core a).positions)
    (feed : ∀b,Event.feed b∈events mesh→∀c∈feeds b,Rows (boundary b c).owner (boundary b c).parity m (boundary b c).positions) :
    ∀s∈paidSlices mesh format feeds sink idBase role ids tree core boundary maxBits,Rows s.owner s.parity m s.count :=
  all_shapes mesh format feeds sink idBase role ids tree core boundary maxBits (fun own tag n=>Rows own tag m n)
    ordinary forest route feed

theorem mounted {m : Memory W} {bank : Bank} {src : ℕ} {ss : List PaidWidths.Slice}
    (fields : ∀s∈ss,s.Fits bank edges src W) (directories : ∀s∈ss,Rows s.owner s.parity m s.count) :
    PaidWidths.Mounted bank edges src ss m := by
  intro s hs
  have dir := directories s hs
  exact ⟨fields s hs,⟨dir.first,dir.second,dir.firstRow,dir.secondRow⟩⟩


end Hierarchy.ProtocolRAM.Calendar.PaidEventDirectory

end
end OAI
