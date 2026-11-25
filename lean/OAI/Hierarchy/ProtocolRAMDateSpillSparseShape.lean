import OAI.Hierarchy.ProtocolRAMDateSpillPaidOrder
import OAI.Hierarchy.TaggedWireArchiveAperture
import OAI.Hierarchy.TaggedWireStockOrdinals
import OAI.Hierarchy.TaggedWireFeedRebase

namespace OAI
/-! # Both sparse spill-role sheets have the measured physical chord widths. -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets
open AdaptiveProbe ProbeStage ProbeStage.CoreBoard ProbeStage.CoreBoard.HistoryRoles
open WireTelescope NamedAperture Tagged.PassiveWindow Computability.VPVNP.BurstRAM PrivateRAM
open LinearAlgebra.SpectralBooks ChordGraph
open scoped BigOperators Classical
variable {h W k attempts axes native : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marks : ReportSockets.Marks h W k attempts) (b : CatalogueRows.Board) (order : Fin b.coreRows ≃ Edges S h (2^W) k)
    (sized : attempts*(PurchaseFrozen.count h (2^W) k*PurchaseFrozen.paths h S.degree depth)=b.boughtRows)
    (axis : Catalysts h W k≃Fin axes) (m : Memory native)
local notation "d" => 2^W
local notation "N" => Stages h d
local notation "G" => Goods h W k
local notation "Cat" => Catalogue S π depth marks
local notation "names" => timeRows S π depth marks b order sized axis
local notation "sites" => siteLast h d k+1
local notation "ord" => b.ordinal S π depth marks order sized
local notation "B" => b.coreMount π (siteNumber h d k) order m

local notation "whereAt" => sorted S π depth marks ∘ names
local notation "before" => (fun (f : G → ℕ) => (Sum.elim (fun _ : Cat=>0) (Sum.elim f (fun _ : Catalysts h W k=>0))) ∘ names)
local notation "after" => (fun (f : Fin b.rows → ℕ) => (Sum.elim (fun c : Cat=>f (ord c)) (fun _ : G⊕Catalysts h W k=>0)) ∘ names)
local notation "D₀" => paidGraph S π depth marks
open LinearAlgebra.SpectralBooks ChordGraph

theorem old_sparse_shape (spill : G→ℕ) :
    installedWidths whereAt (before spill)=(commodityGraph π (siteNumber h d k)).chordWidths spill := by
  have receipt:=HistoryRoles.shape S π depth marks names (fun _=>0) spill (fun _=>0)
  simpa only [HistoryRoles.amount, HistoryRoles.name, chordWidths_empty, zero_add, add_zero]
    using receipt

private theorem zero_width {a : ℕ} {I : Type} [Fintype I] (G₀ : PortGraph (Fin a) I) (i : I) : G₀.chordWidth i 0=0 := by
  unfold PortGraph.chordWidth
  split_ifs <;> simp

theorem new_sparse_shape (spill : G→ℕ) :
    let mass:=routeLoad (B).ordinary spill
    installedWidths whereAt (after mass)=(B).actual.chordWidths mass := by
  intro mass
  have receipt:=HistoryRoles.shape S π depth marks names (fun c=>mass (ord c)) (fun _=>0) (fun _=>0)
  have numbered : (after mass) = HistoryRoles.amount S π depth marks (fun c=>mass (ord c))
      (fun _=>0) (fun _=>0) ∘ names:=by
    funext i
    change Sum.elim _ _ (names i)=Sum.elim _ (Sum.elim _ _) (names i)
    rcases names i with c | (g|t) <;> rfl
  have priced : installedWidths whereAt (after mass)=(D₀).chordWidths (fun c=>mass (ord c)):= by
    rw [numbered]
    simpa only [chordWidths_empty,add_zero] using receipt
  rw [priced]
  let cell (f : Fin b.rows):=(B).actual.chordWidth f (mass f)
  have observed (c : Cat) : (D₀).chordWidth c (mass (ord c))=cell (ord c):=by
    by_cases live : 0< mass (ord c)
    · obtain ⟨e,found⟩:=core_only S π b order m spill (ord c) live
      have recorded : Sum.inl e=c:=(ord).injective found
      subst c
      change (D₀).chordWidth (.inl e) (mass ((B).row e)) =
        (B).actual.chordWidth ((B).row e) (mass ((B).row e))
      simp only [PortGraph.chordWidth,(B).tail,(B).head]; rfl
    · rw [Nat.eq_zero_of_not_pos live,zero_width]
      exact (by simpa only [cell,Nat.eq_zero_of_not_pos live] using (zero_width (B).actual (ord c)).symm)
  unfold PortGraph.chordWidths
  calc
    _ = ∑c : Cat,cell (ord c) := Finset.sum_congr rfl (fun c _=>observed c)
    _ = ∑ f ∈ Finset.univ.map ord,cell f := (Finset.sum_map ..).symm
    _ = ∑f:Fin b.rows,cell f := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro f _ absent
      have zero : mass f=0:=by
        by_contra! positive
        obtain ⟨e,equation⟩:=core_only S π b order m spill f (Nat.pos_of_ne_zero positive)
        exact absent (Finset.mem_map.mpr ⟨.inl e,Finset.mem_univ _,equation⟩)
      exact (by simpa only [cell,zero] using zero_width (B).actual f)
    _ = _ := rfl

/-- Spill visits only mounted core rows. Its paid tensor is therefore identical in
any two genuine chronological snapshots, including traces where dormant purchased
records have unrelated geometry. -/
theorem spill_across_mounts (earlier : Memory native) (spill : G→ℕ) :
    let old:=b.coreMount π (siteNumber h d k) order earlier
    old.actual.chordWidths (routeLoad old.ordinary spill)=(B).actual.chordWidths (routeLoad (B).ordinary spill) := by
  intro old
  have same : old.ordinary=(B).ordinary:=by
    funext i
    simp only [old,CatalogueRows.Board.coreMount_ordinary]
  rw [same]
  apply FeedTransfer.paid_geometry
  intro i used
  obtain ⟨e,equation⟩:=core_only S π b order m spill i used
  subst i
  exact ⟨(old.tail e).trans ((B).tail e).symm,(old.head e).trans ((B).head e).symm⟩

end Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets
end

end OAI
