import OAI.Computability.BorderVNP.CellTeamReportCharge
import OAI.Computability.BorderVNP.PackedBottomReportBundle
import OAI.Computability.BorderVNP.PackedSeedCoreChoices
import OAI.Computability.BorderVNP.RoutingISASignedPhysicalRoomReportRows
import OAI.Computability.BorderVNP.RoutingISASignedPrepReportRows
import OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputsDirectory

/-! # The native binding scan on arbitrary reports for the original retained sites

The scalar writer walks the immutable marked positions in stable source order. Its
private-use cursor starts after the supplied bank and the count digits and advances
by the actual expanded multiplicity of each source. Thus the native record stream
is the same ordered supplemental directory even on unsuccessful report guesses.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open CellSparse Packing.BottomReports

/-- The native writer at a single immutable source emits its original stage ties and
zero padding, using the public stride and the current private-use cursor. -/
theorem physicalBundle_rows (b : Bundle) (body : List Factor) (bank : ℕ → Bool) (q : LocalReportCursor)
    (stride : b.header.stride = bottomStride b.header.orig b.header.cap) :
    (physicalBundle b.header body b.factors bank).rows q =
      reportRows b.header.boxBase b.header.orig b.header.cap b.header.copies q.privateUse b.factors := by
  let f := b.header.writer q.packed q.privateUse q.supplement q.previousRows
  let native := physicalBundle b.header body b.factors bank
  change f.rows native.relative (positions b.header.orig b.factors).length ++
    [f.zeroRow (positions b.header.orig b.factors).length] = _
  rw [positions_length]
  apply writer_reportRows f b.factors native.relative stride
  intro i
  have hi : i.val < (positions b.header.orig b.factors).length := i.isLt
  simp only [ReportBundle.relative,native,physicalBundle,List.getElem?_eq_getElem hi,
    Option.map_some,Option.getD_some]
  rfl


/-- The native cell traversal uses exactly the cumulative marked-copy offsets of
the mathematical supplement for the listed sources, in their given order. -/
theorem bindingRows_physical {J : Type*} (origins : List J) (b : J → Bundle)
    (body : J → List Factor) (bank : J → ℕ → Bool) (q : LocalReportCursor)
    (stride : ∀ j ∈ origins, (b j).header.stride = bottomStride (b j).header.orig (b j).header.cap) :
    bindingRows (origins.map fun j => physicalBundle (b j).header (body j) (b j).factors (bank j)) q =
      supplements q.privateUse (origins.map b) := by
  induction origins generalizing q with
  | nil => rfl
  | cons j js ih =>
    simp only [List.map_cons,bindingRows,supplements]
    rw [physicalBundle_rows _ _ _ q (stride j List.mem_cons_self),
      ih _ (fun u hu => stride u (.tail _ hu))]
    simp only [LocalReportCursor.advance,ReportBundle.useCount,physicalBundle,positions_length,Bundle.useBits]

/-- Count and use choices do not occur in the native strided binding records or
in the updates of the binding cursor. -/
theorem bindingRows_tapeBundles (a : ℕ → Bool) (p : ℕ) (bs : List ReportBundle) (q : LocalReportCursor) :
    bindingRows (tapeBundles a p bs) q = bindingRows bs q := by
  induction bs generalizing p q with
  | nil => rfl
  | cons b bs ih =>
    simp only [tapeBundles,bindingRows,ih]
    rfl

/-- The individual assigned cell is the original owned cell with a slice of the
single finite native tape. Its slice starts after precisely the preceding cells. -/
private theorem tapeCells_get {l : ReportLayout} (a : ℕ → Bool) (p : ℕ) (cs : List (ReportCell l))
    (i : Fin cs.length) :
    (tapeCells a p cs)[i.val]'(by simp) =
      cs[i.val].withTape a (p+((cs.take i.val).map ReportCell.tailWidth).sum) := by
  induction cs generalizing p with
  | nil => exact i.elim0
  | cons c cs ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [tapeCells]
    · simpa only [Fin.val_succ,tapeCells,List.getElem_cons_succ,List.take_succ_cons,
        List.map_cons,List.sum_cons,Nat.add_assoc] using ih (p+c.tailWidth) j

theorem ReportAssignments.length {l : ReportLayout} {cs : List (ReportCell l)} (rows : ReportAssignments cs) :
    rows.val.length = cs.length := by
  simpa only [eraseReportBits,tapeCells_length] using congrArg List.length rows.property

/-- The assigned row keeps every geometric field of the original. The reconstructed
tape contains its actual guessed bits, regardless of whether any checker accepts. -/
theorem ReportAssignments.row_eq {l : ReportLayout} {cs : List (ReportCell l)}
    (rows : ReportAssignments cs) (i : Fin cs.length) :
    let tape := (reportAssignmentEquiv cs).symm rows
    let a (k : ℕ) := if h : k < (reportBits cs).length then tape ⟨k,h⟩ else false
    rows.val[i.val]'(i.isLt.trans_eq rows.length.symm) =
      cs[i.val].withTape a ((cs.take i.val).map ReportCell.tailWidth).sum := by
  intro tape a
  have eq : cellsOfTape cs tape = rows.val :=
    congrArg Subtype.val ((reportAssignmentEquiv cs).apply_symm_apply rows)
  have spec := tapeCells_get a 0 cs i
  simp only [Nat.zero_add] at spec
  change (cellsOfTape cs tape)[i.val]'_ = _ at spec
  simpa only [eq] using spec

/-- Arbitrary sampled counts and use bits on a genuine ordered input leave its
native binding stream at this row unchanged. -/
theorem assigned_bindingRows {l : ReportLayout} {cs : List (ReportCell l)}
    (rows : ReportAssignments cs) (i : Fin cs.length) (q : ReportCursor) :
    let r := rows.val[i.val]'(i.isLt.trans_eq rows.length.symm)
    bindingRows r.bundles (r.localStart q) = bindingRows cs[i.val].bundles (cs[i.val].localStart q) := by
  dsimp only
  rw [rows.row_eq i]
  apply bindingRows_tapeBundles

/-- The actual rows of any assigned cell are the original mathematical
supplement starting after its complete private bank, supply and gadget counts. -/
theorem assigned_physical_supplements {l : ReportLayout} {cs : List (ReportCell l)}
    (rows : ReportAssignments cs) (i : Fin cs.length) (q : ReportCursor)
    {J : Type*} (origins : List J) (b : J → Bundle) (body : J → List Factor) (bank : J → ℕ → Bool)
    (ordered : cs[i.val].bundles = origins.map fun j => physicalBundle (b j).header (body j) (b j).factors (bank j))
    (stride : ∀ j ∈ origins, (b j).header.stride = bottomStride (b j).header.orig (b j).header.cap) :
    let r := rows.val[i.val]'(i.isLt.trans_eq rows.length.symm)
    bindingRows r.bundles (r.localStart q) =
      supplements (cs[i.val].privateWires + cs[i.val].supplied + l.gadgets*l.countWidth) (origins.map b) := by
  intro r
  rw [assigned_bindingRows,ordered]
  exact bindingRows_physical origins b body bank _ stride

end DiagonalTallyCellReports

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse GridBoxes BottomReports Cover TeamContraction GridPlacement
open Diagonal.CellEntries Diagonal.ExternalSew DiagonalTallyCellReports RoutingISA
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open scoped Classical

variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (layout : BundleDirectory.Layout) (control : CellControlRows.Layout) (l : ReportLayout)
    {leaves copies : ℕ} (wits : Fin leaves → WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (origin : Fin layout.bundles ≃ Fin leaves × (Fin q → Deck (depth+2)))
    (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ)
    {s m p qe qa : ℕ} (sites : ∀ i, ((wits i).routedFine position).Site ↪ Fin s)
    (edges : ∀ i, ((wits i).routedFine position).Edge ↪ Fin m)
    (ports : (Fin r × Fin (publicWidth G)) ↪ Fin p)
    (channels : ((Fin q → Deck (depth+2)) × Direction q) ↪ Fin qe)
    (groups : Fin (GridHosts.tileCount q depth) ↪ Fin qa) (slot base : Fin layout.bundles → ℕ)
    (bank : Fin layout.bundles → ℕ → Bool) (owner : Fin layout.bundles → Fin layout.cells)
    (mem : ℕ → ℕ) (counts : ℕ → Fin l.gadgets → Fin l.countWidth → Bool)

local notation "source" => physicalReportRow (copies := copies) wits position origin code sites edges
  ports channels groups slot base bank
local notation "cs" => ReportDirectory.directoryCells layout control l owner source mem counts
local notation3 "original" => fun (j : Fin layout.bundles) => seedCoreBundle (wits (origin j).1) position code (sites _) (edges _)
  ports (origin j).2 (slot j) (base j) copies

/-- At an owned directory ordinal the native scan produces exactly the supplemental
records of the routed seed factors in that cell's stable source order. The private
and supplied widths come from the same live geometry columns as the received row.
This statement applies to the complete report-assignment fiber. -/
theorem assigned_seed_supplements (rows : ReportAssignments cs) (i : Fin (cs).length) (q₀ : ReportCursor) :
    let c := TypedTaskBuilder.globalCell control.toLayout mem i.val
    let r₀ := rows.val[i.val]'(i.isLt.trans_eq rows.length.symm)
    bindingRows r₀.bundles (r₀.localStart q₀) =
      supplements (mem (control.live+2*control.ports+c) + mem (control.offsets+2*control.cables+c) +
        l.gadgets*l.countWidth) ((BundleDirectory.sourceRows owner c).map original) := by
  intro c r₀
  let body (j : Fin layout.bundles) := (wits (origin j).1).seedStored position code (sites _) (edges _)
    ports channels groups (origin j).2
  have atCell : cs[i.val] = ReportDirectory.directoryCell layout control l owner source mem counts c := by
    simp only [ReportDirectory.directoryCells,List.getElem_ofFn,c]
  have native := assigned_physical_supplements rows i q₀ (BundleDirectory.sourceRows owner c) original body bank
    (by rw [atCell]; rfl) (fun _ _ => rfl)
  simpa only [atCell,ReportDirectory.directoryCell] using native

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
