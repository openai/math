import OAI.Computability.BorderVNP.DiagonalPositiveCoreFrozenDirectory
import OAI.Computability.BorderVNP.DiagonalPositiveCoreSignedDirectory
import OAI.Computability.BorderVNP.CubeRouteCommonOwners
import OAI.Computability.BorderVNP.PackedBottomReportBundle
import OAI.Computability.BorderVNP.DiagonalCanonicalReportDirectory

/-! # Signed report inputs for alternative claims on one physical geometry -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open FiniteEvaluator DiagonalTallyCellReports ReportDirectory Evaluator Packing Packing.BottomReports RoutingOutputs
open Evaluator.SignedPrep DiagonalTallyAllocation
open scoped Classical

variable (t : Layout) {frame origin ports bundles R b w : ℕ} (team : Fin (R+1))
    (axis : Fin (t.cube.n+1)) (owner : Fin bundles → Fin t.cube.cells)
local notation "table" => bases origin t.cube.cables t.cube.cells bundles
local notation "control" => controlsBase origin t.cube.cables t.cube.cells bundles ports
local notation "rows" => t.controlRows team.val frame (Bases.ends table) control (Bases.livePairs table) ports
local notation "dir" => t.bundleLayout frame control bundles
local notation "report" => reportLayout t.before t.after frame control t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop
local notation "room" => t.OpenRoom frame (Bases.ends table) control (Bases.livePairs table) ports bundles (2^b) w
local notation3 (prettyPrint := false) "open₀" f => t.openInputs team.val frame (Bases.ends table) control (Bases.livePairs table) ports bundles b owner (fun j => (f j).header)
local notation "middle" => (fun (f : Fin bundles → ReportBundle) (m : ℕ → ℕ) => grouped dir owner f (OpenSuffix.hostImage frame m))

/-- The entry, owned return and stable grouping recover the team number and
both widths of each cell from the original geometry, while its bank pointer
is the explicit affine address of the physical receiving cell. -/
theorem Layout.signedReportColumns (f : Fin bundles → ReportBundle) (input initial written returned : ℕ → ℕ)
    (entry : NativeEntry t.cube frame control axis R input initial written)
    (keep : CubeAllocation.HostRetention t.cube frame initial written returned)
    (place : OpenSuffix.Placement (open₀ f) t.cube t.before frame returned) (space : room)
    (c : Fin t.cube.cells) :
    (rows).owner (middle f returned) c.val=(t.cube.receivingOwner frame axis R input c.val).val ∧
    (middle f returned) ((rows).banks+2*c.val+1)=t.cube.cellBank+c.val*t.cube.cellStride ∧
    (middle f returned) ((rows).offsets+2*(rows).cables+c.val)=initial ((table).ends+2*t.cube.cables+c.val) ∧
    (middle f returned) ((rows).live+2*(rows).ports+c.val)=initial ((table).livePairs+2*ports+c.val) := by
  obtain ⟨owned,bank,sup⟩ := t.open_report_sources owner (fun j => (f j).header) place space axis entry keep
    (space.routing_width_end rfl) c.val c.isLt
  refine ⟨owned,bank,sup,?_⟩
  let a := (table).livePairs+2*ports+c.val
  have stop : a<t.cube.header.header := by
    have h := space.controlEnd
    have hc := c.isLt
    dsimp only [a,controlsBase] at *
    omega
  exact (t.open_bundle_low (team:=team.val) (b:=b) owner (fun j => (f j).header) place a
    (stop.trans_le t.open_table_order.1)).trans
    (keep.geometry space.liveLow a (by dsimp only [a]; omega) stop)

variable (header : Fin bundles → Packing.BottomReports.BundleHeader)
    (body original : Fin bundles → List CellSparse.Factor)
local notation3 (prettyPrint := false) "payload" src => fun j => physicalBundle (header j) (body j) (original j) (src j)

/-- Each guess and shared subtotal claim may give the teams different
private banks. The common selected lengths, labels and original widths force
the same native row order, IDs, factors and use positions on every return. -/
theorem Layout.same_signed_report_rows (left right : Fin bundles → ℕ → Bool)
    (p₁ a₁ wr₁ out₁ p₂ a₂ wr₂ out₂ : ℕ → ℕ)
    (entry₁ : NativeEntry t.cube frame control axis R p₁ a₁ wr₁)
    (entry₂ : NativeEntry t.cube frame control axis R p₂ a₂ wr₂)
    (keep₁ : CubeAllocation.HostRetention t.cube frame a₁ wr₁ out₁)
    (keep₂ : CubeAllocation.HostRetention t.cube frame a₂ wr₂ out₂)
    (place₁ : OpenSuffix.Placement (open₀ (payload left)) t.cube t.before frame out₁)
    (place₂ : OpenSuffix.Placement (open₀ (payload right)) t.cube t.before frame out₂)
    (space : room) (positive : 0<t.cube.header.d)
    (lengths : Sym2 (Fin t.cube.header.d) → Fin (t.cube.n+1) → ℕ)
    (stored₁ : CubeLengths.StoredRows p₁ (t.cube.header.header+13+t.cube.header.entries) lengths)
    (stored₂ : CubeLengths.StoredRows p₂ (t.cube.header.header+13+t.cube.header.entries) lengths)
    (measures : ∀ c<t.cube.cells, p₁ (t.cube.publicBase+c)=p₂ (t.cube.publicBase+c) ∧
      p₁ (t.cube.demands+c)=p₂ (t.cube.demands+c))
    (widths : ∀ c : Fin t.cube.cells, a₁ ((table).ends+2*t.cube.cables+c.val)=a₂ ((table).ends+2*t.cube.cables+c.val) ∧
      a₁ ((table).livePairs+2*ports+c.val)=a₂ ((table).livePairs+2*ports+c.val))
    (x y : ℕ → Fin t.p.report.gadgets → Fin t.p.report.countWidth → Bool) :
    SameReportCells (directoryCells dir rows report owner (payload left) (middle (payload left) out₁) x)
      (directoryCells dir rows report owner (payload right) (middle (payload right) out₂) y) := by
  have owned := (common_owners t.cube frame axis R positive lengths stored₁ stored₂ measures).2.2
  have col₁ := t.signedReportColumns team axis owner (payload left) p₁ a₁ wr₁ out₁ entry₁ keep₁ place₁ space
  have col₂ := t.signedReportColumns team axis owner (payload right) p₂ a₂ wr₂ out₂ entry₂ keep₂ place₂ space
  refine directoryCells_same_reports (l := report) (k := report) dir dir rows rows owner owner (payload left) (payload right)
    (middle (payload left) out₁) (middle (payload right) out₂) x y rfl ?_ rfl (fun _ => rfl)
    (fun _ => ⟨rfl,rfl,rfl⟩)
  refine ⟨rfl,?_,?_,?_,?_⟩
  · intro c hc
    have lhs := (col₁ ⟨c,hc⟩).1
    have rhs := (col₂ ⟨c,hc⟩).1
    rw [lhs,rhs,owned c hc]
  · intro c hc
    exact (col₁ ⟨c,hc⟩).2.1.trans (col₂ ⟨c,hc⟩).2.1.symm
  · intro c hc
    exact (col₁ ⟨c,hc⟩).2.2.1.trans ((widths ⟨c,hc⟩).1.trans (col₂ ⟨c,hc⟩).2.2.1.symm)
  · intro c hc
    exact (col₁ ⟨c,hc⟩).2.2.2.trans ((widths ⟨c,hc⟩).2.trans (col₂ ⟨c,hc⟩).2.2.2.symm)


/-- The fixed source rows used by the exterior decoder contain the original
headers, factors and use positions even on paths with arbitrary proposed
report bits. The source list is defined directly on the mathematical cells. -/
theorem Layout.signedReport_sourceCells (src : Fin bundles → ℕ → Bool)
    (input initial written returned : ℕ → ℕ)
    (entry : NativeEntry t.cube frame control axis R input initial written)
    (keep : CubeAllocation.HostRetention t.cube frame initial written returned)
    (place : OpenSuffix.Placement (open₀ (payload src)) t.cube t.before frame returned)
    (space : room) (who supply privateWidth : ℕ → ℕ)
    (chosen : ∀ c : Fin t.cube.cells, (t.cube.receivingOwner frame axis R input c.val).val=who c.val)
    (widths : ∀ c : Fin t.cube.cells, initial ((table).ends+2*t.cube.cables+c.val)=supply c.val ∧
      initial ((table).livePairs+2*ports+c.val)=privateWidth c.val)
    (digits : ℕ → Fin t.p.report.gadgets → Fin t.p.report.countWidth → Bool) :
    SameReportCells (directoryCells dir rows report owner (payload src) (middle (payload src) returned) digits)
      (sourceCells report owner (payload (fun _ _ => false)) team.val who
        (fun c => t.cube.cellBank+c*t.cube.cellStride) supply privateWidth (fun _ _ _ => false)) := by
  let empty : Fin bundles → ℕ → Bool := fun _ _ => false
  let zero : ℕ → Fin t.p.report.gadgets → Fin t.p.report.countWidth → Bool := fun _ _ _ => false
  have col := t.signedReportColumns team axis owner (payload empty) input initial written returned entry keep place space
  have unfilled := directoryCells_sourceCells report dir rows owner (payload empty) (middle (payload empty) returned)
    rfl who (fun c => t.cube.cellBank+c*t.cube.cellStride) supply privateWidth zero (fun c hc =>
      let i : Fin t.cube.cells := ⟨c,hc⟩
      ⟨(col i).1.trans (chosen i),(col i).2.1,(col i).2.2.1.trans (widths i).1,(col i).2.2.2.trans (widths i).2⟩)
  have same := directoryCells_same_reports (l := report) (k := report) dir dir rows rows owner owner (payload src) (payload empty)
    (middle (payload src) returned) (middle (payload empty) returned) digits zero rfl
    ⟨rfl,fun _ _ => Iff.rfl,fun _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl⟩ rfl (fun _ => rfl) (fun _ => ⟨rfl,rfl,rfl⟩)
  rw [unfilled] at same
  exact same

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
