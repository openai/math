import OAI.Computability.BorderVNP.DiagonalSignedFrozenReportRows
import OAI.Computability.BorderVNP.DiagonalReportPublishedExtent
import OAI.Computability.BorderVNP.FiniteEvaluatorCellKey

/-! # The signed source report list on the actual published geometric network -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM VPVNP.VerifierNetwork Crossing Packing Packing.BottomReports Packing.CellAddresses
open Packing.RoutingOutputs Packing.CellAddressCircuit Packing.CellAddressPhysical GeometryFrameEncoding
open Packing.Inherited ParseBatchSort DiagonalResidueRAM DiagonalTallyCellReports DiagonalTallyAllocation ReportDirectory
open Evaluator Evaluator.SignedPrep FiniteEvaluator

variable {dim sites np cb lb bits w frame origin next gap o R b : ℕ}
    {P σ : Type*} [Fintype P] [Fintype σ] {sizes : P → ℕ} (N : Network dim P sizes)
    (t : Layout) (cell : N.Site → Fin t.cube.cells) (state : N.Site → Site)
    (siteID : N.Site ↪ Fin sites) (edgeID : N.Edge ↪ Fin t.cube.cables) (portID : P ↪ Fin np)
    (F : Fields sites t.cube.cables np t.cube.cells cb lb bits σ) {x : σ → Bool}
    (D : Directory.Layout) (old : Fin D.entries → N.Site) (live : Fin (D.teams*D.sites) → P)
    (pp lp : ℕ → ℕ × ℕ) {profile placed : Memory w}
    (team : Fin (R+1)) (axis : Fin (t.cube.n+1)) (host : Fin D.entries → Fin t.cube.cells)
    (header : Fin D.entries → BundleHeader) (body original : Fin D.entries → List CellSparse.Factor)
    (src : Fin D.entries → ℕ → Bool)
local notation "table" => bases origin t.cube.cables t.cube.cells D.entries
local notation "ctrl" => controlsBase origin t.cube.cables t.cube.cells D.entries (D.teams*D.sites)
local notation "pubMem" => readings (Directory.ISA.publish placed frame next (D.directory pp lp))
local notation "report" => reportLayout t.before t.after frame ctrl t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop
local notation "dir" => t.bundleLayout frame ctrl D.entries
local notation "rows" => t.controlRows team.val frame (Bases.ends table) ctrl (Bases.livePairs table) (D.teams*D.sites)
local notation3 (prettyPrint := false) "physical" f => fun j => physicalBundle (header j) (body j) (original j) (f j)
local notation "aux" => (fun v => Site.size (state v))
local notation "key" => (fun v => Fin.val (cell v))

/-- The output widths in every row of the canonical report domain are the
ones on the actual network addressed after private placement and demand
publication. Source sampling may change every use flag and count digit. -/
theorem Layout.signedProfile_reportSource (input written returned : ℕ → ℕ)
    (entry : NativeEntry t.cube frame ctrl axis R input pubMem written)
    (keep : CubeAllocation.HostRetention t.cube frame pubMem written returned)
    (place : OpenSuffix.Placement
      (t.openInputs team.val frame (Bases.ends table) ctrl (Bases.livePairs table) (D.teams*D.sites) D.entries b host header)
      t.cube t.before frame returned)
    (space : t.OpenRoom frame (Bases.ends table) ctrl (Bases.livePairs table) (D.teams*D.sites) D.entries (2^b) w)
    (who : ℕ → ℕ) (chosen : ∀ c : Fin t.cube.cells, (t.cube.receivingOwner frame axis R input c.val).val=who c.val)
    (image : Image F (siteID ∘ old) (portID ∘ live) x origin (readings profile))
    (net : Represents N cell aux siteID edgeID portID F x) (codes : ∀ c,(F.cells c).val=c.val)
    (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^bits)
    (privatePlace : (privateLayout frame origin t.cube.cables t.cube.cells D.entries D.description gap).Image
      (readings profile) D.entries (readings placed))
    (low : frame+112 ≤ next) (reserve : next+7*D.candidates ≤ origin)
    (rest : Frame σ (Outputs o bits)) (width : bits ≤ w)
    (words : ∀ i : Fin ((t.cube.cells+(D.entries+t.cube.cells))+o),
      profile (origin+t.cube.cables*3+RoutingOutputs.count t.cube.cables t.cube.cells D.entries (D.teams*D.sites)+i.val)=
        word w (value fun j => (withPrivateViews F (siteID ∘ old) rest).eval x (.inl (i,j))))
    (digits : ℕ → Fin t.p.report.gadgets → Fin t.p.report.countWidth → Bool) :
    SameReportCells (directoryCells dir rows report host (physical src)
      (grouped dir host (physical src) (OpenSuffix.hostImage frame returned)) digits)
      (sourceCells report host (physical (fun _ _ => false)) team.val who
        (fun c => t.cube.cellBank+c*t.cube.cellStride) (fun c => suppliedSize N key c)
        (fun c => guessedSize N key c+siteSize N key c aux) (fun _ _ _ => false)) := by
  apply t.signedReport_sourceCells team axis host header body original src input pubMem written returned
    entry keep place space who _ _ chosen _ digits
  intro c
  have col := image.published_reportWidths N cell aux siteID edgeID portID F D old live pp lp net codes fit
    privatePlace low reserve rest width words c
  obtain ⟨g,s,p⟩ := Merged.CellKey.bankSizes N cell Fin.valEmbedding c state
  exact ⟨col.1.trans p.symm,col.2.trans (congrArg₂ Nat.add g s).symm⟩

/-- The address of each original site's private bank survives the physical
publication, the owned path, the cable scatter and the stable directory
grouping. The source ordinal is the one used by the public emitter. -/
theorem Layout.signedProfile_reportSiteBase (written returned : ℕ → ℕ)
    (keep : CubeAllocation.HostRetention t.cube frame pubMem written returned)
    (place : OpenSuffix.Placement
      (t.openInputs team.val frame (Bases.ends table) ctrl (Bases.livePairs table) (D.teams*D.sites) D.entries b host header)
      t.cube t.before frame returned)
    (space : t.OpenRoom frame (Bases.ends table) ctrl (Bases.livePairs table) (D.teams*D.sites) D.entries (2^b) w)
    (net : Represents N cell aux siteID edgeID portID F x)
    (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^bits)
    (privatePlace : (privateLayout frame origin t.cube.cables t.cube.cells D.entries D.description gap).Image
      (readings profile) D.entries (readings placed))
    (low : frame+112 ≤ next) (reserve : next+7*D.candidates ≤ origin)
    (rest : Frame σ (Outputs o bits)) (width : bits ≤ w)
    (words : ∀ i : Fin ((t.cube.cells+(D.entries+t.cube.cells))+o),
      profile (origin+t.cube.cables*3+RoutingOutputs.count t.cube.cables t.cube.cells D.entries (D.teams*D.sites)+i.val)=
        word w (value fun j => (withPrivateViews F (siteID ∘ old) rest).eval x (.inl (i,j))))
    (j : Fin D.entries) :
    grouped dir host (physical src) (OpenSuffix.hostImage frame returned)
      ((table).livePairs+2*(D.teams*D.sites)+t.cube.cells+j.val) =
        siteBase N cell (cell (old j)) siteID aux ⟨old j,rfl⟩ := by
  let a := (table).livePairs+2*(D.teams*D.sites)+t.cube.cells+j.val
  have stop : a<t.cube.header.header := by
    have h := space.controlEnd
    have hj := j.isLt
    dsimp only [a,controlsBase] at *
    omega
  have fromGrid := published_original_siteBase N cell aux siteID edgeID portID F D old pp lp net fit
    privatePlace low reserve rest width words j
  exact (t.open_bundle_low (team:=team.val) (b:=b) host header place a (stop.trans_le t.open_table_order.1)).trans
    ((keep.geometry space.liveLow a (by dsimp only [a]; omega) stop).trans fromGrid)

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
