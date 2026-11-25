import OAI.Computability.BorderVNP.PackedSubdivisionBoxRoster
import OAI.Computability.BorderVNP.PackedHistoryNormalizedCompilation
import OAI.Computability.BorderVNP.PackedHistoryOuterPrivateSites

/-! # Box rosters at the named inputs of a compiled outer epoch

The first inner histogram sees the extended child roster in the exact site
directory returned by the physical subdivision frame.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary.Compilation

open Diagonal.ExternalSew Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive
open Packing Packing.Inherited Shortening.PublicCapacity CellSparse
open scoped Classical
attribute [local instance] portFintype
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000

private theorem subdivision_at_names {D d j V E np : ℕ} {P K : Type} [Field K]
    {bits : P → ℕ} (fin outFin : Fintype P) {L δ : ℝ} {hδ : 0 < δ} {s : Shape}
    (z : PlacedPack D P bits K (Cube D) j) (init : InitialSites z L hδ)
    (p : Pack D P bits K) (r : SiteRoutes p (Cube D) d L) (hl : j = d)
    (hp : init.pack = p) (hr : HEq init.routes r) (row : Rows s p.layout) (dummy : Fin s.edges → p.layout.Site)
    (dir : Directory z V E) (hv : V = (s.subdivide ⌈L/δ⌉₊).sites) (he : E = (s.subdivide ⌈L/δ⌉₊).edges)
    (hd : HEq dir (RouteRows.initialDirectory p r row dummy hδ))
    (old : @Site.Programs D P fin bits p.layout) (port : P ↪ Fin np)
    (known : Fin s.sites → List (List Factor))
    (hprev : BoxRoster.Realizes row.site (fun v => (old v).program.boxes) known) :
    let orig := congrArg Pack.layout hp.symm
    let saved := congrArg (fun q => q.pack.layout) init.realizes.symm
    let raw := RowTrace.sameRows orig row
    let new := raw.siteRoutes init.routes δ
    let prior := @samePrivatePrograms D P fin bits _ _ orig old
    let sub := @Subdivision.subdividePrivatePrograms D _ _ np P outFin bits init.pack.layout
      (init.routes.routes δ) raw.edge new.edge port (changePrivateInstance _ prior)
    let actual := @samePrivatePrograms D P outFin bits _ _ saved sub
    BoxRoster.Realizes dir.sites (fun v => (actual v).program.boxes)
      (BoxRoster.subdivided ⌈L/δ⌉₊ known ∘ finCongr hv) := by
  obtain rfl : outFin = fin := Subsingleton.elim _ _
  subst d; subst p; subst V; subst E
  obtain rfl := eq_of_heq hr
  rcases init with ⟨p,r,rfl⟩
  obtain rfl := eq_of_heq hd
  exact @BoxRoster.subdividePrivatePrograms_roster D np P outFin bits p.layout s row (r.routes δ)
    ⌈L/δ⌉₊ (Rows.route_interior_le r δ) port (changePrivateInstance p.layout old) known hprev

variable {D m start T t w : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : SiteSchedule e} {shape : ℕ → Shape}
    {deep : S.floor+1+S.drop*T ≤ start} {ht : t<T} {budget V E cap : ℕ → ℕ}
    {endShape : shape (t+1) = ⟨V S.rounds,E S.rounds⟩}
    {nodes : ∀ i : Fin S.rounds, S.source.Node S.last (S.high (offset S start t)) V E w S.fanIn i}
    (A : Compilation (bits := bits) deep ht budget V E cap w endShape nodes)

/-- At the actual named input the child's padded roster is extended with empty
relay slots and reindexed by the input frame's recorded site capacity. -/
theorem installedBoxRoster (rows : A.epoch.F.SiteRows)
    (c : Fin (fan S) → Admissible (Good (S := S) (start := start) (bits := bits) (shape := shape) (w := w) budget) t)
    (old : ∀ i, Site.Programs (c i).val.pack.layout) (i : Fin (fan S))
    (known : Fin (shape t).sites → List (List Factor))
    (hprev : BoxRoster.Realizes (c i).val.rows.site (fun v => (old i v).program.boxes) known) :
    BoxRoster.Realizes (((A.epoch.run c).flat i).val.names.sites)
      (fun v => (A.epoch.installedPrivatePrograms rows c old i v).program.boxes)
      (BoxRoster.subdivided ⌈S.budget/S.radius⌉₊ known ∘ finCongr (A.input c).siteWidth) := by
  let run := (A.returned c).run
  let dir := (run.flat i).val.names
  let raw := RouteRows.initialDirectory (c i).val.pack (routes deep ht c i) (c i).val.rows
    (c i).val.dummy S.radius_pos
  have names : HEq dir raw := by
    dsimp only [dir,run]
    rw [(A.returned c).leaves]
    exact (A.input c).names i
  exact subdivision_at_names (portFintype (P := P) (k := fan S) (b := t))
    (portFintype (P := Port (fan S) P t) (k := S.fanIn) (b := 0)) (run.flat i).val.placed
    (run.initialSites i) (c i).val.pack (routes deep ht c i) (S.start_level (offset S start t))
    (run.originalPack i) (run.originalRoutes i) (c i).val.rows (c i).val.dummy dir (A.input c).siteWidth
    (A.input c).edgeWidth names (old i) (rows.ports 0) known hprev

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary.Compilation

end BorderVNP
end Computability
end OAI
