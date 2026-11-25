import OAI.Computability.BorderVNP.PackedFrozenTapeRows
import OAI.Computability.BorderVNP.PackedInheritedWorkPrepTransport

/-! # The complete subdivision tape at the named input of the first inner node

The named directory, the routed leaf, and the inherited private program carry
separate equalities of their physical layout. This transport identifies their
true owner numbers and complete row lists with the raw subdivision writer.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary.Compilation

open Diagonal.ExternalSew Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive
open Packing Packing.Inherited Shortening.PublicCapacity
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1800000
set_option maxRecDepth 3000

private theorem tape_at_names {D d j V E np w : ℕ} {P K R B : Type} [Field K]
    {bits : P → ℕ} (fin outFin : Fintype P) {L δ : ℝ} {hδ : 0 < δ} {s : Shape}
    (z : PlacedPack D P bits K (Cube D) j) (init : InitialSites z L hδ)
    (p : Pack D P bits K) (r : SiteRoutes p (Cube D) d L) (hl : j = d)
    (hp : init.pack = p) (hr : HEq init.routes r) (row : Rows s p.layout) (dummy : Fin s.edges → p.layout.Site)
    (dir : Directory z V E) (hv : V = (s.subdivide ⌈L/δ⌉₊).sites) (he : E = (s.subdivide ⌈L/δ⌉₊).edges)
    (hd : HEq dir (RouteRows.initialDirectory p r row dummy hδ))
    (old : @Site.Programs D P fin bits p.layout) (port : P ↪ Fin np)
    (tape : FrozenTape.Schema R B) (x : FrozenTape.Pins R B w → Bool)
    (rawImage : tape.Image x ((row.siteRoutes r δ).site.trans Fin.valEmbedding)
      (fun v => (@Subdivision.subdividePrivatePrograms D _ _ np P fin bits p.layout
        (r.routes δ) row.edge (row.siteRoutes r δ).edge port old v).program)) :
    let orig := congrArg Pack.layout hp.symm
    let saved := congrArg (fun q => q.pack.layout) init.realizes.symm
    let raw := RowTrace.sameRows orig row
    let new := raw.siteRoutes init.routes δ
    let prior := @samePrivatePrograms D P fin bits _ _ orig old
    let sub := @Subdivision.subdividePrivatePrograms D _ _ np P outFin bits init.pack.layout
      (init.routes.routes δ) raw.edge new.edge port (changePrivateInstance _ prior)
    let actual := @samePrivatePrograms D P outFin bits _ _ saved sub
    tape.Image x (dir.sites.trans Fin.valEmbedding) (fun v => (actual v).program) := by
  obtain rfl : outFin = fin := Subsingleton.elim _ _
  subst d; subst p; subst V; subst E
  obtain rfl := eq_of_heq hr
  rcases init with ⟨p,r,rfl⟩
  obtain rfl := eq_of_heq hd
  exact rawImage

variable {D m start T t w : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : SiteSchedule e} {shape : ℕ → Shape}
    {deep : S.floor+1+S.drop*T ≤ start} {ht : t<T} {budget V E cap : ℕ → ℕ}
    {endShape : shape (t+1) = ⟨V S.rounds,E S.rounds⟩}
    {nodes : ∀ i : Fin S.rounds, S.source.Node S.last (S.high (offset S start t)) V E w S.fanIn i}
    (A : Compilation (bits := bits) deep ht budget V E cap w endShape nodes)

/-- The raw child image compiled from its true route is precisely the full private tape of
the named installed child passed to the next node. Both the physical keys and the rows are
transported through the compilation's stored equalities. -/
theorem installedTape_image (rows : A.epoch.F.SiteRows)
    (c : Fin (fan S) → Admissible (Good (S := S) (start := start) (bits := bits) (shape := shape) (w := w) budget) t)
    (old : ∀ i, Site.Programs (c i).val.pack.layout) (i : Fin (fan S))
    (hv : V 0 = ((shape t).subdivide ⌈S.budget/S.radius⌉₊).sites)
    {R B : Type} (tape : FrozenTape.Schema R B) (x : FrozenTape.Pins R B w → Bool)
    (rawImage : let p := (c i).val.pack
      let r := routes deep ht c i
      let row := (c i).val.rows
      let new := row.siteRoutes r S.radius
      tape.Image x (new.site.trans Fin.valEmbedding)
        (fun v => (Subdivision.subdividePrivatePrograms p.layout (r.routes S.radius) row.edge new.edge
          (rows.ports 0) (old i) v).program)) :
    tape.Image x (((A.epoch.run c).flat i).val.names.sites.trans Fin.valEmbedding)
      (fun v => (A.epoch.installedPrivatePrograms rows c old i v).program) := by
  let run := (A.returned c).run
  let dir := (run.flat i).val.names
  let raw := RouteRows.initialDirectory (c i).val.pack (routes deep ht c i) (c i).val.rows
    (c i).val.dummy S.radius_pos
  have names : HEq dir raw := by
    dsimp only [dir,run]
    rw [(A.returned c).leaves]
    exact (A.input c).names i
  exact tape_at_names (portFintype (P := P) (k := fan S) (b := t))
    (portFintype (P := Port (fan S) P t) (k := S.fanIn) (b := 0)) (run.flat i).val.placed
    (run.initialSites i) (c i).val.pack (routes deep ht c i) (S.start_level (offset S start t))
    (run.originalPack i) (run.originalRoutes i) (c i).val.rows (c i).val.dummy dir hv
    (A.input c).edgeWidth names (old i) (rows.ports 0) tape x rawImage

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary.Compilation

end BorderVNP
end Computability
end OAI
