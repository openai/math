import OAI.Computability.BorderVNP.DiagonalPositiveCoreDirectories
import OAI.Computability.BorderVNP.DiagonalSignedReportEntry

/-! # Global original-cell ordinals at the actual signed arena's host and bundle boundaries -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open FiniteEvaluator DiagonalTallyAllocation DiagonalTallyCellReports ReportDirectory Cube.Physical.NativeAssignments

variable (t : Layout) {frame offsets control live ports bundles b T : ℕ}
    (host : Fin bundles → Fin t.cube.cells) (source : Fin T → Fin bundles → ReportBundle)
    (m : Fin T → ℕ → ℕ)

local notation3 "D" => t.bundleLayout frame control bundles
local notation3 "rows" u => t.controlRows (Fin.val u) frame offsets control live ports
local notation3 "before" u => OpenSuffix.hostImage frame (m u)
local notation3 "report" => reportLayout t.before t.after frame control t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop

variable (place : ∀ u : Fin T, OpenSuffix.Placement
    (t.openInputs u.val frame offsets control live ports bundles b host (fun j => (source u j).header))
    t.cube t.before frame (m u))

include place in
/-- The first word of the installed host-directory record survives the cable
scatter and stable bundle publication. It is the exact owner word read while
enumerating the compact report rows. -/
theorem Layout.receivedOwnerWord (u : Fin T) (c : Fin t.cube.cells) :
    (rows u).owner (grouped D host (source u) (before u)) c.val = m u (t.cube.hostDirectory+2*c.val) := by
  let address := t.cube.hostDirectory+2*c.val
  have limit : address<t.cube.cellBank := by
    have := t.open_table_order.2.1
    have := c.isLt
    dsimp [address]
    omega
  exact t.open_bundle_low (team:=u.val) (b:=b) host (fun j => (source u j).header) (place u) address limit

variable (team : Fin t.cube.cells → Fin T) (installed : ∀ u (c : Fin t.cube.cells),
    m u (t.cube.hostDirectory+2*c.val)=(team c).val)
    (digits : Fin T → ℕ → Fin t.p.report.gadgets → Fin t.p.report.countWidth → Bool)

/-- The actual signed report layout on all teams, including empty owned rows,
with its global bijection derived from the original physical owner column. -/
noncomputable def Layout.receivedRows : ReceivedRows (fun _ : Fin T => report) t.cube.cells :=
  ReceivedRows.ofDirectories _ (fun _ => D) (fun u => rows u) (fun _ => host) source (fun u => before u)
    digits team (fun _ => rfl) (fun _ => rfl)
    (fun u c => (t.receivedOwnerWord host source m place u c).trans (installed u c))

local notation3 (prettyPrint := false) "actualRows" => t.receivedRows (b:=b) (frame:=frame) (offsets:=offsets) (control:=control) (ports:=ports) (live:=live) host source m place team installed digits

/-- The compact ordinal on this actual arena belongs to its executing team. -/
theorem Layout.receivedRows_owner (u : Fin T) (i : Fin ((actualRows).cells u).length) :
    team ((actualRows).order ⟨u,i⟩)=u :=
  ReceivedRows.ofDirectories_owner (fun _ : Fin T => report) (fun _ => D) (fun u => rows u) (fun _ => host)
    source (fun u => before u) digits team (fun _ => rfl) (fun _ => rfl)
    (fun u c => (t.receivedOwnerWord host source m place u c).trans (installed u c)) u i

/-- The actual stable producer chooses the original one-copy sources of this
global cell in their source order. -/
theorem Layout.receivedRows_bundles (u : Fin T) (i : Fin ((actualRows).cells u).length) :
    (((actualRows).cells u).get i).bundles =
      (Packing.BundleDirectory.sourceRows host ((actualRows).order ⟨u,i⟩).val).map (source u) :=
  ReceivedRows.ofDirectories_bundles (fun _ : Fin T => report) (fun _ => D) (fun u => rows u) (fun _ => host)
    source (fun u => before u) digits team (fun _ => rfl) (fun _ => rfl)
    (fun u c => (t.receivedOwnerWord host source m place u c).trans (installed u c)) u i

/-- The owner's value on the owned traversal's output comes from the actual
directory entry computed by the native schedule, at the same global cell. -/
theorem Layout.retainedOwner {R : ℕ} {axis : Fin (t.cube.n+1)} {input initial written returned : ℕ → ℕ}
    (entry : Evaluator.NativeEntry t.cube frame control axis R input initial written)
    (retention : CubeAllocation.HostRetention t.cube frame initial written returned) (c : Fin t.cube.cells) :
    returned (t.cube.hostDirectory+2*c.val)=(t.cube.receivingOwner frame axis R input c.val).val := by
  obtain ⟨_,_,directory⟩ := entry.image
  obtain ⟨_,labels,weights,owners,pair,host,_,_⟩ := t.cube.writer_order
  have bound := c.isLt
  have saved := retention.tables (t.cube.hostDirectory+2*c.val) (by omega) (by omega)
  exact saved.trans (by simpa only [Nat.mul_comm c.val 2] using (directory.hostRows c.val bound).1)

/-- Construct the global row bijection directly on the installed receiving
owner of the native header and its actual retained host-table words. -/
noncomputable def Layout.receivedEntryRows {R : ℕ} (axis : Fin (t.cube.n+1))
    (payload : Fin (R+1) → Fin bundles → ReportBundle)
    (returned initial written : Fin (R+1) → ℕ → ℕ) (input : ℕ → ℕ)
    (placed : ∀ u, OpenSuffix.Placement (t.openInputs u.val frame offsets control live ports bundles b host
      (fun j => (payload u j).header)) t.cube t.before frame (returned u))
    (entry : ∀ u, Evaluator.NativeEntry t.cube frame control axis R input (initial u) (written u))
    (retention : ∀ u, CubeAllocation.HostRetention t.cube frame (initial u) (written u) (returned u))
    (counts : Fin (R+1) → ℕ → Fin t.p.report.gadgets → Fin t.p.report.countWidth → Bool) :
    ReceivedRows (fun _ : Fin (R+1) => report) t.cube.cells :=
  t.receivedRows host payload returned placed (fun c => t.cube.receivingOwner frame axis R input c.val)
    (fun u => t.retainedOwner (entry u) (retention u)) counts

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
