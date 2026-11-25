import OAI.Computability.BorderVNP.PackedInheritedWorkBoundary
import OAI.Computability.BorderVNP.PackedHistoryNormalizedCompilation
import OAI.Computability.BorderVNP.PackedHistoryOuterPrivateSites

/-! # Reading installed subdivision work at the compiled epoch's named leaves -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary.Compilation

open Diagonal.ExternalSew Crossing Cover BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive
open Packing Packing.Inherited Packing.Inherited.WorkWords Shortening.PublicCapacity
open VPVNP.VerifierNetwork (Frame)
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000

private theorem subdivision_at_names {D d j V E np w : ℕ} {P K : Type} {σ : Type*} [Field K] [Fintype σ]
    {bits : P → ℕ} (fin outFin : Fintype P) {L δ : ℝ} {hδ : 0 < δ} {s : Shape}
    (z : PlacedPack D P bits K (Cube D) j) (init : InitialSites z L hδ)
    (p : Pack D P bits K) (r : SiteRoutes p (Cube D) d L) (hl : j = d)
    (hp : init.pack = p) (hr : HEq init.routes r) (row : Rows s p.layout) (dummy : Fin s.edges → p.layout.Site)
    (dir : Directory z V E) (hv : V = (s.subdivide ⌈L/δ⌉₊).sites) (he : E = (s.subdivide ⌈L/δ⌉₊).edges)
    (hd : HEq dir (RouteRows.initialDirectory p r row dummy hδ))
    (old : @Site.Programs D P fin bits p.layout) (port : P ↪ Fin np)
    (prev : Frame σ (Fin s.sites × Fin w)) (x : σ → Bool)
    (hprev : Covers row.site (fun v => (old v).program.size) prev x) :
    let orig := congrArg Pack.layout hp.symm
    let saved := congrArg (fun q => q.pack.layout) init.realizes.symm
    let raw := RowTrace.sameRows orig row
    let new := raw.siteRoutes init.routes δ
    let prior := @samePrivatePrograms D P fin bits _ _ orig old
    let sub := @Subdivision.subdividePrivatePrograms D _ _ np P outFin bits init.pack.layout
      (init.routes.routes δ) raw.edge new.edge port (changePrivateInstance _ prior)
    let actual := @samePrivatePrograms D P outFin bits _ _ saved sub
    Covers dir.sites (fun v => (actual v).program.work)
      ((subdivision ⌈L/δ⌉₊ prev).select (fun a : Fin V × Fin w => (Fin.cast hv a.1,a.2))) x := by
  obtain rfl : outFin = fin := Subsingleton.elim _ _
  subst d; subst p; subst V; subst E
  obtain rfl := eq_of_heq hr
  rcases init with ⟨p,r,rfl⟩
  obtain rfl := eq_of_heq hd
  have h := @subdivision_covers σ _ s w D np P outFin bits p.layout (r.routes δ) row ⌈L/δ⌉₊ (Rows.route_interior_le r δ)
    port (changePrivateInstance p.layout old) prev x hprev
  constructor
  · intro v
    simp only [Frame.select_eval,Fin.cast_refl,id_eq]
    exact h.live v
  · intro a ha
    simpa only [Frame.select_eval,Fin.cast_refl,id_eq] using h.hole a ha

variable {D m start T t w : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : SiteSchedule e} {shape : ℕ → Shape}
    {deep : S.floor+1+S.drop*T ≤ start} {ht : t<T} {budget V E cap : ℕ → ℕ}
    {endShape : shape (t+1) = ⟨V S.rounds,E S.rounds⟩}
    {nodes : ∀ i : Fin S.rounds, S.source.Node S.last (S.high (offset S start t)) V E w S.fanIn i}
    (A : Compilation (bits := bits) deep ht budget V E cap w endShape nodes)

/-- The subdividing work frame sends the prior extent to its actual retained site and zero to
every inserted relay or vacant row in the named leaf consumed by the first histogram. -/
theorem installedWork_covers (rows : A.epoch.F.SiteRows)
    (c : Fin (fan S) → Admissible (Good (S := S) (start := start) (bits := bits) (shape := shape) (w := w) budget) t)
    (old : ∀ i, Site.Programs (c i).val.pack.layout) (i : Fin (fan S))
    (hv : V 0 = ((shape t).subdivide ⌈S.budget/S.radius⌉₊).sites)
    {σ : Type*} [Fintype σ] (prev : Frame σ (Fin (shape t).sites × Fin w)) (x : σ → Bool)
    (hprev : Covers (c i).val.rows.site (fun v => (old i v).program.size) prev x) :
    Covers (((A.epoch.run c).flat i).val.names.sites)
      (fun v => (A.epoch.installedPrivatePrograms rows c old i v).program.work)
      ((subdivision ⌈S.budget/S.radius⌉₊ prev).select fun a : Fin (V 0) × Fin w => (Fin.cast hv a.1,a.2)) x := by
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
    (run.originalPack i) (run.originalRoutes i) (c i).val.rows (c i).val.dummy dir hv
    (A.input c).edgeWidth names (old i) (rows.ports 0) prev x hprev

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary.Compilation

end BorderVNP
end Computability
end OAI
