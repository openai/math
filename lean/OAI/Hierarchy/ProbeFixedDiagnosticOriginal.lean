import OAI.Hierarchy.ProbeFixedDiagnosticFits
import OAI.Hierarchy.ProbeFixedPurchaseHeaderFits
import OAI.Hierarchy.ProbeFixedCatalystHeaders
import OAI.Hierarchy.ProtocolRAMPaidCatalogueBoard
import OAI.Hierarchy.ProtocolRAMCoreRouteSafe

namespace OAI
/-! # Native diagnostic geometry from one public prefix and the genuine parent shelf -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard PurchaseFrozen
open StripChart StripDirectory CatalogueRows BoughtSockets
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (z width r K G H R idBase : ℕ) (joint : JointHeader.Board)
local notation "n" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
variable (origin : Directory ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel))
local notation "s" => v.sampler
local notation "d" => Public.join origin s z v.W k v.depth K G H R
local notation "cat" => liveBoard d s z v.W k v.depth R K G H (CoreCatalogue.pointBits z v.W) idBase
local notation "P" => v.catalystPlacement z K G H R joint cat origin
local notation "W" => wordBits z (2^v.W) copies
local notation "coreEnd" => CoreRoute.stop s z v.W k n v.depth K G H R
local notation "col" => CoreCatalogue.top z v.W K G H R
variable (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "C" => v.nativeChart P z width r banks src tab dst owners

/-- The site, radius, group, numeric length and role-header addresses used for
a diagnostic all belong to the chart's genuine global public input. -/
theorem diagnostic_original (bound : ℕ) (core : coreEnd≤bound) (space : bound<2^W) :
    (cat).core.All (Expr.Fits W bound) ∧
    CoreRoute.directoryBase s z v.W k n v.depth K G H R+CoreLookup.words s z (2^v.W) k≤bound ∧
    col+ColumnROM.words z (2^v.W) k≤bound ∧
    ColumnROM.Cover z v.W (d).remapBase (d).sitesBase (d).superBase K G H bound ∧
    (stratumHeader z (2^v.W) k (s).degree v.depth (d).keysBase).stop≤bound := by
  have ⟨column,cover⟩:=CoreRoute.column_bounds s z v.W k n v.depth K G H R bound core
  have ⟨_,keyEnd⟩:=Public.borders s col z v.W k n v.depth
  have start : CoreRoute.directoryBase s z v.W k n v.depth K G H R≤bound := (Nat.le_add_right ..).trans core
  exact ⟨(CoreCatalogue.top_fits _ _ _ _ _ _ _ _ _ _ ((Nat.le_add_right ..).trans column) space).all,
    core,column,cover,keyEnd.trans start⟩

theorem original_outer_link_fits (phase trial bound : ℕ) (core : coreEnd≤bound) (space : bound<2^W) :
    LinkOperands (repair C (.outer phase trial)).link W bound := by
  obtain ⟨geo,radii,columns,cover,_⟩:=v.diagnostic_original z K G H R idBase origin bound core space
  exact v.payload_link_fits P z width r banks src tab dst owners bound phase trial space geo radii columns cover

theorem original_inner_link_fits (phase trial j t bound : ℕ) (core : coreEnd≤bound) (space : bound<2^W)
    (parent : ∀i : Key z (2^v.W) k,
      (((v.located (v.seed P z width) P width).outer phase trial).market.shelf.L s v.depth i).endAddress≤bound) :
    LinkOperands (repair C (.inner phase trial j t)).link W bound := by
  obtain ⟨geo,radii,columns,cover,keys⟩:=v.diagnostic_original z K G H R idBase origin bound core space
  exact v.purchased_link_fits P z width r banks src tab dst owners bound phase trial space geo radii columns cover
    j t keys parent

/-- Both the regular and purchased four-field receipts and the selected
menu fit at the actual pricing boundary of every dated attempt. -/
theorem original_links_at_keys (a : Attempt) (allocated : coreEnd≤joint.initial)
    (space : (v.nativeFormats P z width a).board.keys<2^W) :
    let f:=v.nativeFormats P z width a
    LinkOperands (repair C a).link W f.board.keys ∧ LinkOperands f.board.purchaseLink W f.board.keys ∧
      f.board.purchaseMenu.Fits W f.board.keys := by
  intro f
  let bound:=f.board.keys
  let base:=(v.privateArena P z width).base v.mesh (.attempt a)
  have low : base≤bound:=(Nat.le_add_right ..).trans (v.stock_keys P z width a).1
  have start : joint.initial≤bound:=(v.catalyst_initial_le_first P z width).trans ((Nat.le_add_right ..).trans low)
  have hi:=allocated.trans start
  obtain ⟨geo,radii,columns,cover,keys⟩:=v.diagnostic_original z K G H R idBase origin bound hi space
  obtain ⟨_,_,_,static,keyLow⟩:=v.diagnostic_original z K G H R idBase origin joint.initial allocated (start.trans_lt space)
  refine ⟨?_,v.purchase_header_fits P z width a space static keyLow⟩
  cases a with
  | outer phase trial =>
    exact v.payload_link_fits P z width r banks src tab dst owners bound phase trial space geo radii columns cover
  | inner phase trial j t =>
    let fields:=v.located (v.seed P z width) P width
    have before:=(v.catalyst_bought_bank_room P z width phase trial j t).2
    exact purchased_diagnostic_source_fits fields v.mesh cat (P).routes phase trial j t space geo radii columns cover
      keys (fun i=>(before i).trans low)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
