import OAI.Hierarchy.ProtocolRAMStripNativeFits
import OAI.Hierarchy.ProtocolRAMCalendarStripHistFields
import OAI.Hierarchy.ProtocolRAMCatalogueRowBounds

namespace OAI
/-! # Address bounds for the four fields of the original catalyst diagnostic -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard PurchaseFrozen
open StripDirectory BoughtSockets CatalogueRows
open scoped Classical Fin.CommRing
variable {w bound z W k depth q : ℕ}
local notation "N" => Stages z (2^W)

def LinkOperands (L : Link) (w bound : ℕ) : Prop :=
  L.group.Fits w bound ∧ L.endpoint.Fits w bound ∧ L.opposite.Fits w bound ∧ L.lengthCode.Fits w bound

theorem diagnostic_fits (b : CatalogueRows.Board) (x : Expr) (idBase : ℕ)
    (core : b.core.All (Expr.Fits w bound)) (pos : x.Fits w bound) :
    LinkOperands (diagnosticLink b x idBase) w bound := by
  obtain ⟨grp,left,right,len,_⟩:=core
  have l:=fits_atRow _ _ left pos
  have r:=fits_atRow _ _ right pos
  exact ⟨fits_atRow _ _ grp pos,⟨l,r,l,r⟩,⟨l,r,r,l⟩,fits_atRow _ _ len pos⟩

variable (s : Boards z (2^W) k q depth) (c : Mesh) (b : CatalogueRows.Board)
  (G : PortBanks ((c.inject+c.cool)*c.outerFuel))
local notation "d" => G.directory
local notation "bs" => withPorts s c b G
local notation "past" => withPurchaseFields bs c b G

/-- The outer diagnostic uses its real exterior payload column and the
designated first sign's original core record, before any purchase. -/
theorem payload_diagnostic_fits (p a : ℕ) (space : bound<2^w) (geo : b.core.All (Expr.Fits w bound))
    (orig : G.core+CoreLookup.words s.sampler z (2^W) k≤bound)
    (tab : G.column+ColumnROM.words z (2^W) k≤bound)
    (cover : ColumnROM.Cover z W (d).remapBase (d).sitesBase (d).superBase G.oldGroups G.bins G.height bound) :
    LinkOperands (((past).outer p a).repair.link) w bound := by
  let ports:=payloadPortsAt s c G
  let col:=PayloadStrip.first N 0
  let j:Fin k:=⟨0,s.positive⟩
  let role:PayloadRole N k:=.catalyst col j
  apply diagnostic_fits b _ _ geo
  change (ports.primary b ((Fintype.equivFin _).symm ((Fintype.equivFin _) role))).Fits w bound
  rw [Equiv.symm_apply_apply]
  have cell : (ports.column col).Fits w bound:=
    ColumnROM.payload_fits_cols (attempts:=(c.inject+c.cool)*c.outerFuel) G.column
      (d).remapBase (d).sitesBase (d).superBase G.oldGroups G.bins G.height bound
      (payloadChoice z W col) space tab cover
  have radius : (ports.radiusAt col j false).Fits w bound:=⟨core_bank_fits _ _ space orig,cell⟩
  exact ⟨radius,trivial,radius,trivial⟩

/-- On a nested repair only the earlier parent acquisition contributes a
shelf address. The computational bound for its true strip role uses that
one original table and the protected global directories. -/
theorem purchased_diagnostic_source_fits (p a t h : ℕ) (space : bound<2^w) (geo : b.core.All (Expr.Fits w bound))
    (orig : G.core+CoreLookup.words s.sampler z (2^W) k≤bound)
    (tab : G.column+ColumnROM.words z (2^W) k≤bound)
    (cover : ColumnROM.Cover z W (d).remapBase (d).sitesBase (d).superBase G.oldGroups G.bins G.height bound)
    (head : (stratumHeader z (2^W) k s.sampler.degree depth (d).keysBase).stop≤bound)
    (sources : ∀i : Key z (2^W) k,let L:=(s.outer p a).market.shelf.L s.sampler depth i
      L.source.base+L.source.size≤bound) :
    LinkOperands (((past).inner p a t h).repair.link) w bound := by
  let ports:=boughtPortsAt s c b G p a
  let c₀:=ChainStrip.inlet depth 0
  let j:Fin k:=⟨0,s.positive⟩
  let role:PurchasedRole depth k:=.catalyst c₀ j
  apply diagnostic_fits b _ _ geo
  change (ports.primary b ((Fintype.equivFin _).symm ((Fintype.equivFin _) role))).Fits w bound
  rw [Equiv.symm_apply_apply]
  have cell : (ports.column c₀).Fits w bound:=by
    apply select_fits _ _ space head
    intro i
    apply ColumnROM.stage_fits_cols G.column (d).remapBase (d).sitesBase (d).superBase G.oldGroups G.bins G.height
      bound _ _ _ space tab cover
    let L:=(s.outer p a).market.shelf.L s.sampler depth i
    have leaf:=sources i
    change L.source.base+L.source.size≤bound at leaf
    have bank:L.source.Fits w bound:=⟨Nat.two_pow_pos _,by omega,leaf⟩
    exact ⟨bank,trivial,trivial⟩
  have radius : (ports.radiusAt c₀ j false).Fits w bound:=⟨core_bank_fits _ _ space orig,cell⟩
  exact ⟨radius,trivial,radius,trivial⟩

theorem purchased_diagnostic_fits (p a t h : ℕ) (space : bound<2^w) (geo : b.core.All (Expr.Fits w bound))
    (orig : G.core+CoreLookup.words s.sampler z (2^W) k≤bound)
    (tab : G.column+ColumnROM.words z (2^W) k≤bound)
    (cover : ColumnROM.Cover z W (d).remapBase (d).sitesBase (d).superBase G.oldGroups G.bins G.height bound)
    (head : (stratumHeader z (2^W) k s.sampler.degree depth (d).keysBase).stop≤bound)
    (slab : ∀i : Key z (2^W) k,((s.outer p a).market.shelf.L s.sampler depth i).endAddress≤bound) :
    LinkOperands (((past).inner p a t h).repair.link) w bound := by
  apply purchased_diagnostic_source_fits s c b G p a t h space geo orig tab cover head
  intro i
  let L:=(s.outer p a).market.shelf.L s.sampler depth i
  obtain ⟨_,_,_,_,_,source,gates,tape,last⟩:=L.regions
  have limit : L.endAddress≤bound:=slab i
  change L.source.base+L.source.size≤bound
  omega

end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI
