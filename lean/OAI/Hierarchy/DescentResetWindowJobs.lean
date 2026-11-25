import OAI.Hierarchy.DescentRootWindowRun
import OAI.Hierarchy.DescentPrivateInstalledPhase

namespace OAI
/-! # Literal finite-window kernels in the chronological reset schedule -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentPacking.PackedMatch.Local.Gather
open DescentSIMDLookup DescentPackedZip DescentSharedBookScan DescentPackedFallbackTree.Image
open DescentFallbackPeriod DescentFallbackRankRAM ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w H G M D L cap n r Ht : ℕ}

namespace Shelf
/-- Fallback per-terminal dictionary plus per-root matrix fields. This is the
three real native passes from GroupStage.issued_fallback evaluated in sequence. -/
def fallback (chart : Chart) (tables : Fin (inputCount D L cap n r)→Tables)
    (loads : Fin (inputCount D L cap n r)→Expr) (menu : Banks) (target mid out : ℕ)
    (source : (record chart H D (2^Ht) (Ht+2)).Fits w target)
    (sSpace : target+H*DescentSharedBookScan.width r (2^n) D<2^w)
    (load : (assembly tables loads).Fits w mid) (page : (lookup menu).Fits w out)
    (mSpace : mid+H*chunks G M<2^w) (oSpace : out+H*chunks G M<2^w) : Shelf w :=
  (ofScan target (H*DescentSharedBookScan.width r (2^n) D) _ source sSpace).seq
    (window tables loads menu mid out load page mSpace oSpace)

theorem fallback_image (chart : Chart) (tables : Fin (inputCount D L cap n r)→Tables)
    (loads : Fin (inputCount D L cap n r)→Expr) (menu : Banks) (target mid out : ℕ)
    (source : (record chart H D (2^Ht) (Ht+2)).Fits w target)
    (sSpace : target+H*DescentSharedBookScan.width r (2^n) D<2^w)
    (load : (assembly tables loads).Fits w mid) (page : (lookup menu).Fits w out)
    (a : mid+H*chunks G M<2^w) (b : out+H*chunks G M<2^w) (m : Memory w) :
    (fallback chart tables loads menu target mid out source sSpace load page a b).image m=
      (installedPhase chart tables loads menu w H G M Ht target mid out).image m := rfl

theorem fallback_read (chart : Chart) (tables : Fin (inputCount D L cap n r)→Tables)
    (loads : Fin (inputCount D L cap n r)→Expr) (menu : Banks) (target mid out : ℕ)
    (source : (record chart H D (2^Ht) (Ht+2)).Fits w target)
    (sSpace : target+H*DescentSharedBookScan.width r (2^n) D<2^w)
    (load : (assembly tables loads).Fits w mid) (page : (lookup menu).Fits w out)
    (a : mid+H*chunks G M<2^w) (b : out+H*chunks G M<2^w)
    (list : List (Shelf w)) (order : list.Pairwise (fun early later=>later.limit≤early.first))
    (has : fallback chart tables loads menu target mid out source sSpace load page a b∈list)
    (mem : Memory w) (i : Fin (H*chunks G M)) :
    (series list).image mem (out+i.val)=
      (installedPhase chart tables loads menu w H G M Ht target mid out).image mem (out+i.val) := by
  apply read_series list order mem has
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (Nat.le_add_right _ _))
  · exact (Nat.add_lt_add_left i.isLt _).trans_le ((le_max_right _ _).trans (le_max_right _ _))

end Shelf
end
end Hierarchy.DescentSixParty.Chronology

end OAI
