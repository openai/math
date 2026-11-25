import OAI.Computability.BorderVNP.PackedOuterSiteFieldRows
import OAI.Computability.BorderVNP.PackedHistoryPrivateNamedRows
import OAI.Computability.BorderVNP.PackedHistoryNormalizedCompilation

/-! # The compiled outer epoch supplies its complete physical row receipt

The subdivision frame's leaf names and the terminal frame's flattened return
names agree with the actual intrinsic private-program replay. Both are read
from the same completed compilation that generated the geometric pack and
histogram frames.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

open Diagonal.ExternalSew Crossing BorderVNP.Epoch BorderVNP.Epoch.Round Cover Shortening Packing Catalog Adaptive PublicCapacity
open Packing.Inherited
open scoped Classical
attribute [local instance] portFintype
set_option maxHeartbeats 2000000
set_option maxRecDepth 3000

private theorem cable_heq {D n m s t a b : ℕ} {K P : Type} {bits : P → ℕ}
    {p : PlacedPack D P bits K (Cube D) a} {p' : PlacedPack D P bits K (Cube D) b}
    (dir : Directory p s n) (dir' : Directory p' t m)
    (hl : a=b) (hs : s=t) (hm : n=m) (hp : HEq p p') (hd : HEq dir dir') : HEq dir.cables dir'.cables := by
  subst b; subst t; subst m
  obtain rfl := eq_of_heq hp
  obtain rfl := eq_of_heq hd
  rfl

private theorem same_val {X : Type*} {n m : ℕ} (f : X ↪ Fin n) (g : X ↪ Fin m) (hn : n=m) (he : HEq f g)
    (z : X) : (f z).val = (g z).val := by
  subst m
  obtain rfl := eq_of_heq he
  rfl

private theorem installed_cable_heq {D d j : ℕ} {P K : Type} [CommSemiring K] {bits : P → ℕ} {L h : ℝ}
    (hh : 0<h) (z : PlacedPack D P bits K (Cube D) j) (init : InitialSites z L hh)
    (p : Pack D P bits K) (r : SiteRoutes p (Cube D) d L) (lev : j=d)
    (hp : init.pack=p) (hr : HEq init.routes r) {s : Shape} (row : Rows s p.layout)
    (dummy : Fin s.edges → p.layout.Site) :
    let orig := RowTrace.sameRows (congrArg Pack.layout hp.symm) row
    let leaf := RowTrace.sameRows (congrArg (fun p => p.pack.layout) init.realizes.symm) (orig.siteRoutes init.routes h)
    HEq leaf.edge (RouteRows.initialDirectory p r row dummy hh).cables := by
  subst d; subst p
  obtain rfl := eq_of_heq hr
  rcases init with ⟨pack,route,realizes⟩
  subst z
  rfl

private theorem returned_edge {D n m : ℕ} {K P : Type} {bits : P → ℕ}
    {p : Pack D P bits K} (outer : Shape) (shape : outer = ⟨n,m⟩) (rows : Rows ⟨n,m⟩ p.layout) (z : p.layout.Edge) :
    ((returnedRows (p := p) shape rows).edge z).val = (rows.edge z).val := by
  subst outer
  rfl

variable {D m start T t w np : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P]
    {bits : P → ℕ} {e : PaidIdentity K D m} {S : SiteSchedule e} {shape : ℕ → Shape}
    {deep : S.floor+1+S.drop*T ≤ start} {ht : t<T} {budget V E cap : ℕ → ℕ}
    {endShape : shape (t+1) = ⟨V S.rounds,E S.rounds⟩}
    {nodes : ∀ i : Fin S.rounds, S.source.Node S.last (S.high (offset S start t)) V E w S.fanIn i}
    (A : Compilation (bits := bits) deep ht budget V E cap w endShape nodes)
    (port : Port (fan S) P t ↪ Fin np)
    (seeds : ∀ i : Fin S.rounds, ((Cube D → Deck (S.level (offset S start t) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)

local notation3 "dir₀" => A.program.privateSiteRows port seeds
local notation3 "layout₀" => A.program.modelRows port seeds
local notation3 "next₀" => Flat.portRows S.rounds (Parallel.nestedPorts S.fanIn port S.rounds)

/-- The literal geometric compilation discharges every epoch field-row premise.
The next exterior directory uses the actual flattened child-and-port names. -/
noncomputable def Compilation.fieldRows : A.epoch.FieldRows dir₀ port next₀ where
  layout := layout₀
  inputCap c := (A.input c).edgeWidth
  inputRows c i z := by
    let run := (A.returned c).run
    let inp := A.input c
    let placed := (run.flat i).val.placed
    let rootDir := (run.flat i).val.names
    let raw := RouteRows.initialDirectory (c i).val.pack (routes deep ht c i) (c i).val.rows (c i).val.dummy S.radius_pos
    have hnames : HEq rootDir raw := by
      dsimp only [rootDir,run]
      rw [(A.returned c).leaves]
      exact inp.names i
    have hl := S.start_level (offset S start t)
    have hphys := RouteRows.actual_initial S.radius_pos placed (run.initialSites i) (c i).val.pack
      (routes deep ht c i) hl (run.originalPack i) (run.originalRoutes i)
    have h₁ := cable_heq rootDir raw hl inp.siteWidth inp.edgeWidth hphys hnames
    have h₂ := installed_cable_heq S.radius_pos placed (run.initialSites i) (c i).val.pack
      (routes deep ht c i) hl (run.originalPack i) (run.originalRoutes i) (c i).val.rows (c i).val.dummy
    exact same_val rootDir.cables (A.epoch.installedFieldRows c i).edge inp.edgeWidth (h₁.trans h₂.symm) z
  outputCap := congrArg Shape.edges endShape
  outputRows c q z := by
    change (((A.returned c).rows q).edge z).val = _
    rw [(A.returned c).rows_eq q]
    exact returned_edge (p := flattenPack S.rounds (A.epoch.F.terminal (A.epoch.run c).flat q).pack)
      (shape (t+1)) endShape (Terminal.boundaryRows ((A.returned c).run.root q).val.names).flatten z
  inputPortCap := rfl
  inputPorts _ := rfl
  outputPortCap := rfl
  outputPorts _ := rfl

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

end BorderVNP
end Computability
end OAI
