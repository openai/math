import OAI.Computability.BorderVNP.DiagonalOriginalRowOuter
import OAI.Computability.BorderVNP.DiagonalExternalSewStoredRow
import OAI.Computability.BorderVNP.DiagonalExternalGridBlockHosts
import OAI.Computability.BorderVNP.ShortenPublicBottomCapacity

/-! # History-independent numeric site names in the exterior field writer

The team selects a bottom group by division by the copy count. The block number
is the original row in that group's deck enumeration. Each enclosing public
epoch adds the fixed offsets of its child rectangles. Encoding that sum with
the original site column gives the pointer bits of the actual sewn fields.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.RowTrace

open Cover Crossing Shortening Adaptive Packing Packing.PhysicalEpochs Packing.DeckGrid
open PackedHistoryCircuit Epoch Epoch.Round CellEntries PublicCapacity TeamContraction
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m}
    {S : Normalized.SiteSchedule e} (program : Factory.Dense.Programs S)
    {R r t pins link inner n : ℕ} {Edge : Type} (G : Wiring R r t pins link inner n Edge)
    (axes gridDepth : ℕ)
    (order : Fin (GridHosts.tileCount axes gridDepth) ≃ (Fin axes → Deck (gridDepth+2)))
    (position : (Fin axes → Deck (gridDepth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {start T copies : ℕ}
    (deep : (Factory.ofDenseSchedule program).floor+1+(Factory.ofDenseSchedule program).drop*T ≤ start)
    (count : (Factory.ofDenseSchedule program).fan^T*copies = R+1)

/-- The fixed reserved rectangles of the actual grouped deck grid. -/
noncomputable abbrev bottomShape (axes gridDepth : ℕ) :=
  gridShape (GridHosts.tileCount axes gridDepth) (Fintype.card (Direction axes))

/-- The actual grouped bottom grid uses the supplied tile order for its site
names and the tile/direction product for its cable names. -/
noncomputable def groupedGridRows (copies : ℕ) :
    Rows (bottomShape axes gridDepth) ((wiredGrid G axes gridDepth order position).groupedRepeat
      (fun _ : Fin (GridHosts.tileCount axes gridDepth) => GridHosts.inputBlockWidth r n axes gridDepth) order copies) where
  site := order.symm.toEmbedding
  edge := ((Equiv.prodCongr order.symm (Fintype.equivFin (Direction axes))).trans finProdFinEquiv).toEmbedding

variable (bottom : (Factory.ofDenseSchedule program).State
    (fun _ : Fin (GridHosts.tileCount axes gridDepth) => copies*GridHosts.inputBlockWidth r n axes gridDepth) start 0)
    (installed : bottom.pack.layout = (wiredGrid G axes gridDepth order position).groupedRepeat
      (fun _ : Fin (GridHosts.tileCount axes gridDepth) => GridHosts.inputBlockWidth r n axes gridDepth) order copies)

/-- The initial public row of a supplied tile is exactly its tile ordinal. -/
theorem bottom_row (i : Fin (GridHosts.tileCount axes gridDepth)) :
    (sameRows installed.symm (groupedGridRows G axes gridDepth order position copies)).site (bottom.pack.layout.attach i) = i :=
  (sameRows_attach installed.symm _ i).trans (order.symm_apply_apply i)

/-- The complete final site and cable row embeddings on a selected branch
above the actual installed deck grid. -/
noncomputable def gridDirectory (q : ((Factory.ofDenseSchedule program).histories deep bottom T).Index) :=
  outerDirectory program deep (bottomShape axes gridDepth) bottom
    (sameRows installed.symm (groupedGridRows G axes gridDepth order position copies)) T le_rfl q

/-- The concrete block-host map used by the normalized factory's sewn term. -/
noncomputable def gridHosts (q : ((Factory.ofDenseSchedule program).histories deep bottom T).Index) :=
  let F := Factory.ofDenseSchedule program
  let L := (flattenPack T ((F.histories deep bottom T).term q).pack).layout
  let retained := (Retains.parallel fun _ : Fin (F.fan^T) => Retains.ofEq installed.symm).trans
    (denseOuterHosts program deep bottom q)
  GridHosts.blockHosts G axes gridDepth order position (F.fan^T) copies count L retained

/-- The numeric row of every true original block host is computed from
the initial block ordinal and the fixed outer child digits, independently
of the selected motions and histograms. -/
theorem grid_host_row (q : ((Factory.ofDenseSchedule program).histories deep bottom T).Index)
    (u : Fin (R+1)) (i : Fin (GridHosts.tileCount axes gridDepth)) :
    ((gridDirectory program G axes gridDepth order position deep bottom installed q).site
      ((gridHosts program G axes gridDepth order position deep count bottom installed q).host (u,i.val))).val =
      flatOffset (outerOffset S start (bottomShape axes gridDepth)) T
        (GridHosts.teamBlocks ((Factory.ofDenseSchedule program).fan^T) copies count u).1 + i.val := by
  let F := Factory.ofDenseSchedule program
  let group := (GridHosts.teamBlocks (F.fan^T) copies count u).1
  let base := sameRows installed.symm (groupedGridRows G axes gridDepth order position copies)
  let ret := Retains.ofEq installed.symm
  let final := denseOuterHosts program deep bottom q
  let code := (gridDirectory program G axes gridDepth order position deep bottom installed q).site
  have hb : ret.site (GridHosts.baseHost (S := Fin axes → Deck (gridDepth+2)) order i.val) = bottom.pack.layout.attach i :=
    (congrArg ret.site (GridHosts.baseHost_val order i)).trans (ret.attach i).symm
  refine (congrArg (fun v => (code (final.site ⟨group,v⟩)).val) hb).trans ?_
  exact (retained_name program deep (bottomShape axes gridDepth) bottom base q group i).trans
    (congrArg (_ + ·) (congrArg Fin.val (bottom_row program G axes gridDepth order position bottom installed i)))

/-- The public integer code used by the exterior pointer columns. It has
no history argument. Indices beyond the address rectangles receive zero. -/
noncomputable def originalNumericName (S : Normalized.SiteSchedule e) (start T copies : ℕ)
    (initial : Shape) {d : ℕ} (codes : Fin (outerShape S start initial T).sites ↪ Fin (2^d))
    (team block : ℕ) : ℕ :=
  if hu : team/copies < (S.fanIn^S.rounds)^T then
    let row := flatOffset (outerOffset S start initial) T ⟨team/copies,hu⟩ + block
    if hr : row < (outerShape S start initial T).sites then (codes ⟨row,hr⟩).val else 0
  else 0

/-- Exact host-name agreement required by the Boolean sewn-field representation
on every original team and block. The site code table is fixed in advance. -/
theorem originalNumericName_host {d : ℕ} (codes :
    Fin (outerShape S start (bottomShape axes gridDepth) T).sites ↪ Fin (2^d))
    (q : ((Factory.ofDenseSchedule program).histories deep bottom T).Index)
    (u : Fin (R+1)) (i : ℕ) (hi : i < GridHosts.tileCount axes gridDepth) :
    originalNumericName S start T copies (bottomShape axes gridDepth) codes u.val i =
      (codes ((gridDirectory program G axes gridDepth order position deep bottom installed q).site
        ((gridHosts program G axes gridDepth order position deep count bottom installed q).host (u,i)))).val := by
  let F := Factory.ofDenseSchedule program
  let group := (GridHosts.teamBlocks (F.fan^T) copies count u).1
  let initial := bottomShape axes gridDepth
  let v := (gridDirectory program G axes gridDepth order position deep bottom installed q).site
    ((gridHosts program G axes gridDepth order position deep count bottom installed q).host (u,i))
  have hv : v.val = flatOffset (outerOffset S start initial) T group + i :=
    grid_host_row program G axes gridDepth order position deep count bottom installed q u ⟨i,hi⟩
  have hu : u.val/copies < (S.fanIn^S.rounds)^T := group.isLt
  have hr : flatOffset (outerOffset S start initial) T group+i < (outerShape S start initial T).sites :=
    hv ▸ v.isLt
  unfold originalNumericName
  rw [dite_eq_left hu]
  change (if h : flatOffset (outerOffset S start initial) T group+i < _ then
    (codes ⟨flatOffset (outerOffset S start initial) T group+i,h⟩).val else 0) = (codes v).val
  rw [dite_eq_left hr]
  exact congrArg (fun z => (codes z).val) (Fin.ext hv.symm)

end Diagonal.ExternalSew.RowTrace

end BorderVNP
end Computability
end OAI
