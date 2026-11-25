import OAI.Computability.BorderVNP.RoutingISASignedSelectedRoom
import OAI.Computability.BorderVNP.RoutingISASignedPhysicalRoomStride
import OAI.Computability.BorderVNP.DiagonalTallyReportOwnedAllocation

/-! # Length-only parameters for the physical signed-task allocation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open BorderVNP.Cube.Tally DiagonalTallyAllocation
open private small_width from OAI.Computability.BorderVNP.RoutingISATypedPrivateClock

/-- Addresses and lengths supplied by the public geometry compiler for its
primary descriptor sort and marked bottom-bundle sort. -/
structure GeometryDirectories where
  /-- Absolute start of the physically sorted primary descriptor words. -/
  sorted : ℕ
  /-- Padded length preceding the primary inverse-ordinal directory. -/
  padded : ℕ
  /-- First raw ordinal of the exclusive cell stop markers. -/
  stops : ℕ
  /-- Absolute word bank of the secondary marked-bundle sort. -/
  bundlePayload : ℕ
  /-- Absolute bank of the secondary inverse row ordinals. -/
  bundleInverse : ℕ

/-- Report arrays are sized from the global original bundle roster, its
single-copy site bound, the exact source power-slot count and the actual
candidate vertex directory. -/
noncomputable def reportBounds (cube : CubeArena.Layout) (bundles marked params expBits gadgets w : ℕ) : Bounds :=
  ⟨cube.cells,bundles,marked,cube.teams*(params*expBits),gadgets,w,cube.vertexCap,
    argumentWidth cube.n cube.b cube.h cube.K cube.s,bundles*(9*marked+6)⟩

/-- Control values for the real fixed descriptor layout. The reserved
quadratic gap precedes the opaque descriptions in each supplied bank. -/
noncomputable def physicalParameters (cube : CubeArena.Layout) (g : GeometryDirectories)
    (n bundles marked params expBits gadgets w header body : ℕ) : Parameters where
  report := reportBounds cube bundles marked params expBits gadgets w
  sorted := g.sorted
  padded := g.padded
  stops := g.stops
  bundlePayload := g.bundlePayload
  bundleInverse := g.bundleInverse
  privateGap := n^2
  scratchStride := scratchWindow n
  burstStride := burstWindow n
  siteWidth := header
  bodyCap := body
  parameters := params

/-- The directory bound covers all real supplemental records of an assigned
cell, including the length-six base record for each retained bundle. -/
theorem report_supplement (cube : CubeArena.Layout) (bundles marked params expBits gadgets w : ℕ)
    {C : ℕ} (owner : Fin bundles → Fin C) (cell : Fin C) (source : Fin bundles → DiagonalTallyCellReports.ReportBundle)
    (room : ∀ i, (source i).positions.length ≤ marked) :
    DiagonalTallyCellReports.supplementWords ((Packing.BundleDirectory.sourceRows owner cell.val).map source) ≤
      (reportBounds cube bundles marked params expBits gadgets w).supplementStride := by
  apply (DiagonalTallyCellReports.supplementWords_le _ marked ?_).trans
  · apply Nat.mul_le_mul_right
    simpa only [List.length_map,List.length_finRange,Packing.BundleDirectory.sourceRows] using
      (List.length_filter_le (l:=List.finRange bundles) (p:=fun i => decide ((owner i).val=cell.val)))
  · intro r hr
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
    exact room i

/-- Genuine per-cell exterior extent certified by the private parser fits
the allocated gap for its report and use tail. -/
theorem report_tail_in_gap {n ext : ℕ} (f : SparseExterior.Field) (hn : 1≤n)
    (room : f.width+f.tail.length≤ext) (small : ext≤TeamScales.width n (1/4)) : f.tail.length ≤ n^2 := by
  exact ((Nat.le_add_left ..).trans (room.trans (small.trans (small_width hn (1/4) (by norm_num))))).trans
    (Nat.le_self_pow (by decide) _)

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
