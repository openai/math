import OAI.Hierarchy.ProtocolRAMCoreRouteBounds
import OAI.Hierarchy.ProtocolRAMCoreRouteImage

namespace OAI
/-! # One public size comparison certifies all four settlement hop readers -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreRoute
open ProbeStage ReportSockets BoughtSockets

/-- The core endpoint bounds the column words and all three index pages used to
resolve a reported column owner. The same pages are also read by settlement. -/
theorem column_bounds (S : PurchaseSampler) (z W k attempts depth K G H R out : ℕ)
    (floor : stop S z W k attempts depth K G H R≤out) :
    CoreCatalogue.top z W K G H R+ColumnROM.words z (2^W) k≤out ∧
      ColumnROM.Cover z W (CoreCatalogue.groupStart z W) (CoreCatalogue.siteBase z W K)
        (CoreCatalogue.superStart z W) K G H out := by
  let columns := CoreCatalogue.top z W K G H R
  have dir : directoryBase S z W k attempts depth K G H R≤ out := (Nat.le_add_right ..).trans floor
  have ⟨keys,outer⟩ := Public.borders S columns z W k attempts depth
  have after : columns+ColumnROM.words z (2^W) k≤ out := keys.trans (outer.trans dir)
  have cap : CoreCatalogue.top z W K G H R≤ out := (Nat.le_add_right ..).trans after
  unfold CoreCatalogue.top at cap
  simp only [max_le_iff] at cap
  obtain ⟨_,_,offsets,sites⟩ := cap
  have start : CoreCatalogue.superStart z W+2*ProtocolRAMSupergroupDirectory.span K=CoreCatalogue.siteBase z W K := rfl
  have names : CoreCatalogue.groupStart z W+ReportGroupROM.words z (2^W)=CoreCatalogue.superStart z W := rfl
  have heap : Native.heapEnd z (2^W) Native.copies≤ CoreCatalogue.groupStart z W := le_max_left ..
  have cover : ColumnROM.Cover z W (CoreCatalogue.groupStart z W) (CoreCatalogue.siteBase z W K)
      (CoreCatalogue.superStart z W) K G H out :=
    ⟨by omega,by omega,by omega,offsets,sites⟩
  exact ⟨after,cover⟩

theorem source_safe (S : PurchaseSampler) (z W k attempts depth K G H R w out : ℕ)
    (floor : stop S z W k attempts depth K G H R≤ out) (word : out<2^w) :
    Safe (source S z W k attempts depth K G H R) S z W k attempts w out := by
  obtain ⟨after,cover⟩:=column_bounds S z W k attempts depth K G H R out floor
  exact ⟨word,floor,fun c=>ColumnROM.payload_fits_cols (CoreCatalogue.top z W K G H R) _ _ _ K G H out c word after cover⟩

end Hierarchy.ProtocolRAM.Calendar.CoreRoute
end

end OAI
