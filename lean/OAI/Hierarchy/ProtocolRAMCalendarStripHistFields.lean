import OAI.Hierarchy.ProtocolRAMCalendarStripOrigin
import OAI.Hierarchy.ProtocolRAMBoughtCatalogue

namespace OAI
/-! # Pre-settlement historical rows use real CT sites and the same occurrence IDs -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseStage PurchaseFrozen
open StripDirectory CatalogueRows BoughtSockets CoreBoard
open scoped Fin.CommRing Classical
variable {z W k letters depth : ℕ}
local notation "N" => List.length (Fabric.shapes (permutationFabric z (2^W)))
variable (s : Boards z (2^W) k letters depth) (c : Mesh) (b : CatalogueRows.Board)
  (G : PortBanks ((c.inject+c.cool)*c.outerFuel))

/-- The joint archive stores a copy of each original candidate row.
The two native CT endpoint expressions are those used by the later physical
catalogue. Their local ID interval is the actual signed candidate block. -/
def purchaseHeader (p a : ℕ) : Link :=
  let before:=birth c p a
  let n:=PurchaseFrozen.count z (2^W) k*PurchaseFrozen.paths z s.sampler.degree depth
  let place:=b.idBase+b.coreRows+before*n
  if h : before<(c.inject+c.cool)*c.outerFuel then
    let i:Fin ((c.inject+c.cool)*c.outerFuel):=⟨before,h⟩
    let f:=fun side=>BoughtSockets.event G.directory.remapBase (s.stratumHeader p a)
      (s.outer p a).market.shelf s.sampler z (2^W) k depth i side
    let site:=fun side=>ReportSockets.SiteROM.atPort G.directory.sitesBase G.bins G.height G.directory.superBase
      G.oldGroups (ReportSockets.copies k ((c.inject+c.cool)*c.outerFuel))
      (f side).group (f side).port (f side).tag
    ⟨.lookup (ProtocolRAMSupergroupDirectory.groupBank G.directory.superBase G.oldGroups) (f false).group,
      site false,site true,place,.lit 1⟩
  else ⟨.lit 0,.lit 0,.lit 0,place,.lit 1⟩

def purchaseKey (p a : ℕ) : Expr :=
  let h:=stratumHeader z (2^W) k s.sampler.degree depth (s.stratumHeader p a)
  .op .add (.lit 1) h.ballTerm

/-- Every local repair row records the geometrical channels of its designated
first catalyst role, as well as the selected packet ID. All other role
occurrences use the chronological sparse archive. -/
def diagnosticLink (edge : Expr) (idBase : ℕ) : Link :=
  let l:=b.core.left.atRow edge
  let r:=b.core.right.atRow edge
  ⟨b.core.group.atRow edge,CatalogueRows.low l r,CatalogueRows.high l r,idBase,b.core.lengthCode.atRow edge⟩

def withPurchaseFields : Boards z (2^W) k letters depth :=
  let outerRole:PayloadRole N k:=.catalyst (PayloadStrip.first N 0) ⟨0,s.positive⟩
  let innerRole:PurchasedRole depth k:=.catalyst (ChainStrip.inlet depth 0) ⟨0,s.positive⟩
  let oi:=Fintype.equivFin (PayloadRole N k) outerRole
  let ii:=Fintype.equivFin (PurchasedRole depth k) innerRole
  {s with
    outer:=fun p a=>
      let state:=s.outer p a
      let buy:=purchaseHeader s c b G p a
      {state with
        report := .lit oi.val
        repair := {state.repair with
          purchaseLink := buy
          purchaseMenu := purchaseKey s p a
          link := diagnosticLink b (s.payloadEdge p a oi) buy.idBase}}
    inner:=fun p a j t=>
      let state:=s.inner p a j t
      let buy:=purchaseHeader s c b G p a
      {state with
        report := .lit ii.val
        repair := {state.repair with
          purchaseLink := buy
          purchaseMenu := purchaseKey s p a
          link := diagnosticLink b (s.purchaseEdge p a j t ii) buy.idBase}}}

theorem origin_fields (p a : ℕ) :
    ((withPurchaseFields s c b G).outer p a).repair.purchaseLink=purchaseHeader s c b G p a ∧
    ((withPurchaseFields s c b G).outer p a).repair.purchaseMenu=purchaseKey s p a := ⟨rfl,rfl⟩

end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI
