import OAI.Computability.BorderVNP.PackedReportWriter
import OAI.Computability.BorderVNP.PrivatePlacementImage
import OAI.Computability.BorderVNP.PackedCellAddressOutputs
import OAI.Computability.BorderVNP.DiagonalExternalSewAncestry

/-! # Physical geometry operands for the bottom-bundle sidecar scanner

The delivered metadata address comes from the completed private placement and
the destination cell's receive-bank pointer. The work base comes from the
canonical allocation at the retained original vertex. These addresses have
different origins and both enter the weighted-source scan.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports

open Crossing CellAddresses RoutingISA Diagonal.ExternalSew

/-- The six public scalar fields consumed once per original site and bottom bundle. -/
structure BundleHeader where
  /-- Absolute RAM address of the delivered opaque private metadata. -/
  siteSlot : ℕ
  /-- Number of copies represented by this one-copy private description. -/
  copies : ℕ
  /-- Cell-local bank address of the first bit in the original box. -/
  boxBase : ℕ
  /-- Distance between the starts of consecutive copies. -/
  stride : ℕ
  /-- Reserved report lanes per copy. -/
  cap : ℕ
  /-- First report lane relative to the start of a copy. -/
  orig : ℕ
  deriving DecidableEq

/-- The actual six-word row, prior to stable grouping by its final owner. -/
def BundleHeader.words (r : BundleHeader) : List ℕ :=
  [r.siteSlot,r.copies,r.boxBase,r.stride,r.cap,r.orig]

/-- The native report writer's input frame for this bundle. Only the decoded
sidecar buffer and the current output cursors are supplied by the caller. -/
def BundleHeader.writer (r : BundleHeader) (side useStart dst previousRows : ℕ) : Writer.Frame :=
  ⟨r.orig,side,r.copies,useStart,r.boxBase,r.stride,r.cap,dst,previousRows⟩

/-- Fields obtained by loading the completed private placement table and receive-bank
directory. The original box starts at offset zero in its retained site's work prefix. -/
def rawHeader (mem : ℕ → ℕ) (raw receive j copies siteBase capFine incoming capReport : ℕ) : BundleHeader :=
  let owner := mem (raw+2*j)
  let recvBase := mem (receive+2*owner+1)
  let orig := capFine+incoming
  ⟨recvBase+mem (raw+2*j+1),copies,siteBase,bottomStride orig capReport,capReport,orig⟩

/-- The slot read by the outer program is the true byte address of this delivered
site, after all supplied bits, reserved report capacity, and preceding descriptions. -/
theorem raw_slot (l : PrivatePlacement.Layout) {w : ℕ} (before after : ℕ → ℕ)
    (img : l.Image before l.entries after) (fit : l.Fits w before) (receive : ℕ) (j : Fin l.entries)
    (b base capFine incoming capReport : ℕ) :
    (rawHeader after l.raw receive j.val b base capFine incoming capReport).siteSlot =
      after (receive+2*l.owner before j.val+1) +
        (before (l.supplied+l.owner before j.val)+l.gap+
          PrivatePlacement.prefixCounts (l.owner before) l.desc j.val (l.owner before j.val)) := by
  unfold rawHeader
  rw [img.owner_eq fit j.isLt,img.slots j.val j.isLt]

open ParseBatchSort CellAddressCircuit CellAddressPhysical CellAddressViews
variable {D s m n C d k w : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
variable {N M : Network D P bits} (retain : Retains N M)
variable (cell : M.Site → Fin C) (aux : M.Site → ℕ)
variable (siteID : M.Site ↪ Fin s) (edgeID : M.Edge ↪ Fin m) (portID : P ↪ Fin n)
variable {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ) {x : σ → Bool}

/-- Direct six-word source for an original host in a genuine retained-site history.
The source takes its staging base from the computed final allocation column. -/
noncomputable def geometryHeader (l : PrivatePlacement.Layout) (after : ℕ → ℕ) (receive : ℕ)
    (origin : Fin l.entries → N.Site) (j : Fin l.entries) (b capFine incoming capReport : ℕ) :
    BundleHeader :=
  rawHeader after l.raw receive j.val b
    (value fun k => (CellAddressViews.frame F).eval x (.inr (.inl (siteID (retain.site (origin j)))),k))
    capFine incoming capReport

/-- The geometry source binds the one-copy box to its precise retained site's
canonical local offset in the owning final cell. -/
theorem geometry_base (h : CellAddressPhysical.Represents M cell aux siteID edgeID portID F x)
    (fit : ∀ c, guessedSize M cell c + siteSize M cell c aux + suppliedSize M cell c < 2^w)
    (l : PrivatePlacement.Layout) (after : ℕ → ℕ) (receive : ℕ) (origin : Fin l.entries → N.Site)
    (j : Fin l.entries) (b capFine incoming capReport : ℕ) :
    (geometryHeader retain siteID F (x := x) l after receive origin j b capFine incoming capReport).boxBase =
      siteBase M cell (cell (retain.site (origin j))) siteID aux ⟨retain.site (origin j),rfl⟩ :=
  CellAddressViews.site_value M cell aux siteID edgeID portID F h fit _

end Packing.BottomReports

end BorderVNP
end Computability
end OAI
