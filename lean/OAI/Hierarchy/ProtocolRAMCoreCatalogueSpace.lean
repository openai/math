import OAI.Hierarchy.ProtocolRAMCoreCatalogueRowBudget
import OAI.Hierarchy.ProtocolRAMCoreCatalogueNative
import OAI.Hierarchy.ProtocolRAMCoreCatalogueFrame
import OAI.Hierarchy.ProbeCoreFootprint

namespace OAI
/-! # Physical footprint for the permutation-to-core-catalogue decoder -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreCatalogue
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard ReportSockets TaggedShorterSupergroups
open scoped Classical Fin.CommRing

def pointBits (h W : ℕ) := ProtocolRAMPurchaseSampler.bits (superStart h W)

/-- Includes the complete padded regions used by native total indexed reads. -/
def top (h W K G H R : ℕ) :=
  max (2^pointBits h W) (max (headBase h W K G H+headerWords R)
    (max (siteBase h W K+ProtocolRAMPurchaseSampler.span G)
      (siteBase h W K+G+ProtocolRAMPurchaseSampler.span (G*H))))

theorem top_fits (h W k attempts R K G H w out : ℕ) (before : top h W K G H R≤ out)
    (room : out<2^w) : Fits (sourceAt h W k attempts R K G H (pointBits h W)) w out := by
  unfold top at before
  simp only [max_le_iff] at before
  obtain ⟨point,rows,offsets,sites⟩ := before
  have start : superStart h W+2*ProtocolRAMSupergroupDirectory.span K=siteBase h W K := rfl
  exact source_fits _ _ _ _ _ _ _ _ _ _ out room rows point (by omega) offsets sites

/-- Storage is linear in the physical subdivision, original group count, packed
socket count, and core row count. -/
theorem top_bound (h W K G H R budget : ℕ) (positive : 0< H) (packing : G*H≤ budget) :
    top h W K G H R≤2*(superStart h W+1)+4*(K+1)+3*budget+20*(R+1)+2 := by
  have old := ProtocolRAMSupergroupDirectory.space K
  have ptr : 2^pointBits h W≤2*(superStart h W+1) := ProtocolRAMPurchaseSampler.span_le _
  have bound : headBase h W K G H≤ superStart h W+4*(K+1)+2*budget := SiteROM.storage _ positive packing
  have header := headerWords_linear R
  have offsets := ProtocolRAMPurchaseSampler.span_le G
  have sites := ProtocolRAMPurchaseSampler.span_le (G*H)
  have perGroup : G≤ G*H := by simpa using Nat.mul_le_mul_left G positive
  have groups := perGroup.trans packing
  unfold top siteBase
  simp only [max_le_iff]
  omega

/-- A single common address-space bound gives all of the numerical fits
required for a real permutation execution. -/
theorem rooms_of_top {h W K G H R w : ℕ} (stages : 0< (permutationFabric h (2^W)).shapes.length)
    (fits : top h W K G H R<2^w) :
    R≤2^w ∧ K≤2^w ∧ G≤2^w ∧ G*H≤2^w ∧ ReportGroupROM.stride h (2^W)≤2^w ∧
      superStart h W≤2^pointBits h W ∧ 2^pointBits h W≤2^w := by
  have cap := fits.le
  unfold top at cap
  simp only [max_le_iff] at cap
  obtain ⟨pointer,headers,offsets,sites⟩ := cap
  have ptr : superStart h W<2^pointBits h W := ProtocolRAMPurchaseSampler.lt_span _
  have rowSpace : R< stride R := ProtocolRAMSupergroupDirectory.slotFits R
  have groupSpace := ProtocolRAMSupergroupDirectory.slotFits K
  have old : superStart h W+2*ProtocolRAMSupergroupDirectory.span K=siteBase h W K := rfl
  have g := ProtocolRAMPurchaseSampler.lt_span G
  have gh := ProtocolRAMPurchaseSampler.lt_span (G*H)
  have remap : ReportGroupROM.stride h (2^W)≤ ReportGroupROM.words h (2^W) :=
    by simpa only [ReportGroupROM.words,Nat.one_mul] using
      Nat.mul_le_mul_right (ReportGroupROM.stride h (2^W)) stages
  have groupEnd : groupStart h W+ReportGroupROM.words h (2^W)=superStart h W := rfl
  unfold headerWords at headers
  omega

end Hierarchy.ProtocolRAM.Calendar.CoreCatalogue
end

end OAI
