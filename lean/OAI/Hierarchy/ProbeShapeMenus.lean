import OAI.Hierarchy.ProbeStripMenu
import OAI.Hierarchy.ProbeChainStrip
import OAI.Hierarchy.ProbePayloadStrip
import OAI.Hierarchy.ProtocolRAMCalendarMesh

namespace OAI
/-! # The two fixed shapes, their packet menus and selector trees -/

noncomputable section

namespace Hierarchy.AdaptiveProbe.Strip

abbrev TreeColumn (n : ℕ) := TestColumns (steps n) 0 n
abbrev TreeSite (n k : ℕ) := ColumnSite (TreeColumn n) k
/-- The center path and all of its radial leaves. No commodity, catalyst
shortcut or purchased probe is used to carry the selector. -/
abbrev TreeLink (n k : ℕ) := Fin n ⊕ (TreeColumn n × (Fin k × Bool))

end Hierarchy.AdaptiveProbe.Strip

namespace Hierarchy.ProtocolRAM.StripDirectory
open AdaptiveProbe
open scoped Classical

abbrev PayloadRole (N k : ℕ) := ColumnWires.Role (PayloadStrip.Columns N)
  (Fin (PayloadStrip.edgeCount N)) (PayloadStrip.Quotes N k ⊕ Empty) k

abbrev PurchasedRole (depth k : ℕ) := ColumnWires.Role (ChainStrip.Columns depth)
  (Fin (ChainStrip.edgeCount depth)) (ChainStrip.Axes depth k ⊕ Unit) k

/-- The one immutable menu for all payload-strip rows of this local shape. -/
def payloadMenu (F : Type*) [Field F] (stages k : ℕ)
    [SiteNaming (ColumnSite (PayloadStrip.Columns stages) k)] (hk : 0<k) (M : ℝ) (hM : 0≤M)
    (ε : ℝ) (he : 0<ε) (tree : ℝ) (ht : 0≤tree) (minimum : ℕ) :=
  Strip.formatMenu (F:=F) hk (PayloadStrip.commodity stages k) (PayloadStrip.noProbe stages)
    M hM (PayloadStrip.length stages) (fun e => by unfold PayloadStrip.length; split <;> norm_num)
    (PayloadStrip.ceiling stages k M) he tree ht minimum

/-- The same finite purchased-strip menu is reused at every retained candidate. -/
def purchasedMenu (F : Type*) [Field F] (depth k : ℕ)
    [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)] (hk : 0<k) (M : ℝ) (hM : 0≤M)
    (ε : ℝ) (he : 0<ε) (tree : ℝ) (ht : 0≤tree) (minimum : ℕ) :=
  Strip.formatMenu (F:=F) hk (ChainStrip.commodity depth k) (ChainStrip.probe depth)
    M hM (ChainStrip.length depth) (fun e => by unfold ChainStrip.length; split <;> norm_num)
    (fun _ => M+1) he tree ht minimum

end Hierarchy.ProtocolRAM.StripDirectory

namespace Hierarchy.ProtocolRAM.Calendar.StripChart

structure TreeCosts where
  payload : ℝ
  purchase : ℝ
  payload_nonneg : 0≤payload
  purchase_nonneg : 0≤purchase

def TreeCosts.atAttempt (cost : TreeCosts) : Attempt → ℝ
  | .outer .. => cost.payload
  | .inner .. => cost.purchase

theorem TreeCosts.nonneg (cost : TreeCosts) (a : Attempt) : 0≤cost.atAttempt a := by
  cases a
  · exact cost.payload_nonneg
  · exact cost.purchase_nonneg

end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI
