import OAI.Hierarchy.ProtocolRAMCatalogueRows
import OAI.Hierarchy.ProbeReportedGeometry

namespace OAI
/-! # Genuine paid catalogue rows realize the global physical board for pruning -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.ReportSockets CoreBoard AdaptiveProbe ProtocolRAMEmit
open scoped Classical Fin.CommRing
variable {w h W k attempts r : ℕ}

/-- Reading the original source's three non-sorted words. Physical CT and
stored selected-path endpoints determine these values before the common final
serializer orders the ordinals. -/
structure Located (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marked : Marks h W k attempts) (M : ℕ) (v : View) (e : Catalogue S π depth marked) : Prop where
  left : v.left=(siteNumber h (2^W) k (actualEnds S π depth marked e).1).val
  right : v.right=(siteNumber h (2^W) k (actualEnds S π depth marked e).2).val
  metric : v.lengthCode=lenCode S π depth marked M e

theorem Located.sorted {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))} {depth M : ℕ}
    {marked : Marks h W k attempts} {v : View} {e : Catalogue S π depth marked}
    {row : Row} {id : ℕ} (atSite : Located S π depth marked M v e) (native : Reads row v id) :
    ∃ flip : Bool,let ends:=actualEnds S π depth marked e
      row.endpoint=(siteNumber h (2^W) k (if flip then ends.2 else ends.1)).val ∧
      row.opposite=(siteNumber h (2^W) k (if flip then ends.1 else ends.2)).val ∧
      row.lengthCode=lenCode S π depth marked M e := by
  by_cases order : v.left≤v.right
  · exact ⟨false,(native.leftField.trans (min_eq_left order)).trans atSite.left,
      (native.rightField.trans (max_eq_right order)).trans atSite.right,native.lengthField.trans atSite.metric⟩
  · have rev := le_of_lt (lt_of_not_ge order)
    exact ⟨true,(native.leftField.trans (min_eq_right rev)).trans atSite.right,
      (native.rightField.trans (max_eq_left rev)).trans atSite.left,native.lengthField.trans atSite.metric⟩

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Every core ordinal has fixed meaning. Only an acquired slot with positive
*terminal native width* needs a witnessed purchased chain, so padding requires
no fictitious chain. Both branches use the seven-field runtime serializer. -/
def Board.pruning (b : Board) (banks : RouteSettlement.Banks) (source table destination : ℕ)
    (owners : Bank) (m : Memory w) {core : I→List (Fin b.rows)} {center : J→List (Fin b.rows)}
    (enum : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ)
    (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marked : Marks h W k attempts) (payload R M : ℕ)
    (room : b.idBase+b.rows<2^w) (wide : 1<2^w)
    (fits : ∀f : Fin 7,f≠4→(b.geometry f).Fits w banks.width.base) (space : banks.width.base+b.rows≤ source)
    (fixed : Fin b.coreRows→Edges S h (2^W) k)
    (coreAt : ∀j,Located S π depth marked M (b.core.view m (j.val:Word w)) (.inl (fixed j)))
    (boughtAt : ∀j : Fin b.boughtRows,
      0<((b.sink r banks source table destination owners).terminalRows m enum ci cj (b.boughtIndex j)).width→
      ∃chain : Bought S π depth marked,Located S π depth marked M (b.bought.view m (j.val:Word w)) (.inr chain)) :
    Geometry (boardLayout h (2^W) k payload R) M 1
      ((b.sink r banks source table destination owners).terminalRows m enum ci cj) := by
  let rows := (b.sink r banks source table destination owners).terminalRows m enum ci cj
  have named (i : ActiveRows rows) : ∃ e : Catalogue S π depth marked,∃ flip : Bool,
      let z:=actualEnds S π depth marked e
      (rows i.val).endpoint=(siteNumber h (2^W) k (if flip then z.2 else z.1)).val ∧
      (rows i.val).opposite=(siteNumber h (2^W) k (if flip then z.1 else z.2)).val ∧
      (rows i.val).lengthCode=lenCode S π depth marked M e := by
    rcases b.split_index i.val with ⟨j,hj⟩|⟨j,hj⟩
    · refine ⟨.inl (fixed j),?_⟩
      rw [←hj]
      exact (coreAt j).sorted (b.core_reads banks source table destination owners m enum ci cj j room fits space)
    · have used : 0<(rows (b.boughtIndex j)).width := by rw [hj];exact i.property
      obtain ⟨chain,got⟩ := boughtAt j used
      refine ⟨.inr chain,?_⟩
      rw [←hj]
      exact got.sorted (b.bought_reads banks source table destination owners m enum ci cj j room wide fits space)
  choose e flip receipt using named
  exact CoreBoard.pruning S π depth marked payload R M rows e flip
    (fun i=>⟨(receipt i).1,(receipt i).2.1⟩) (fun i=>(receipt i).2.2)

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
