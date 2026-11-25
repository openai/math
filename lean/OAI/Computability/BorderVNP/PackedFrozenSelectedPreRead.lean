import OAI.Computability.BorderVNP.PackedInheritedWorkWrapped
import OAI.Computability.BorderVNP.PackedFrozenSelectedPre
import OAI.Computability.BorderVNP.PackedFrozenPrepImage
import OAI.Computability.BorderVNP.PackedFrozenTapePreTransport

/-! # Exact sparse program image on every selected physical epoch input -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

open Crossing Cover Cover.AddressCircuit Epoch Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Inherited WorkWords FrozenTape EnrichedOuter ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1600000
set_option maxRecDepth 3000

private theorem endpoints_at_names {D l d V E w : ℕ} {P K B : Type} {bits : P → ℕ}
    (p : PlacedPack D P bits K (Cube D) l) (p' : PlacedPack D P bits K (Cube D) d)
    (dir : Directory p V E) (dir' : Directory p' V E) (level : l = d) (hp : HEq p p') (hd : HEq dir dir')
    (y : WorkWords.SavedPins B V E w → Bool)
    (ready : PublicEndpoints.Represents p.pack.layout dir.sites dir.cables dir.dummy (fun z => y (.inr (.inr z))))
    (live : ∀ i, y (.inl i) = true ↔ i ∈ Set.range dir.cables) :
    PublicEndpoints.Represents p'.pack.layout dir'.sites dir'.cables dir'.dummy (fun z => y (.inr (.inr z))) ∧
      ∀ i, y (.inl i) = true ↔ i ∈ Set.range dir'.cables := by
  subst d
  obtain rfl := eq_of_heq hp
  obtain rfl := eq_of_heq hd
  exact ⟨ready,live⟩

variable {D m : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : Normalized.SiteSchedule e} {start T w : ℕ}
    {deep : S.floor+1+S.drop*T ≤ start} {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ}
    (C : Compiled bits deep budget cap w) (base : FrozenTape.Format) (t : ℕ) (ht : t<T)
    (ports : WorkWords.Ports (portSlots S start t 0)) (fit : (before S start t 0).sites ≤ 2^w)
    (c : Fin (fan S) → Admissible (Boundary.Good (S := S) (start := start) (bits := bits)
      (shape := boundaryShape S start) (w := w) budget) t)
    (old : ∀ i, Site.Programs (c i).val.pack.layout)
    (x : Fin (fan S) × ProgramSchemas.outerPins S start w base t → Bool)

local notation3 "comp" => C.atLevel t ht
local notation3 (prettyPrint := false) "W" => (comp).widthPre rfl ports fit
local notation3 (prettyPrint := false) "input" => fun z : Fin (fan S) × Boundary.OuterWidthPins S start (boundaryShape S start) w t => x (z.1,.inl z.2)
local notation3 "shape₀" => boundaryShape S start t
local notation3 "Fmt" => ProgramSchemas.epoch S start w base t
local notation3 "outFmt" => ProgramSchemas.stage S start w base t 0
local notation3 "leafB" => ProductSlots (Fintype.card (Cube D)) (S.level (offset S start t) 0+1) ⊕ ↥(S.source.catalog 0)

/-- The checked subdividing gate output contains exactly the raw route's occupied hops
and its true new endpoint rows. This identifies the actual leaf with its public source
before the private-program transport at that same leaf. -/
theorem pre_names (geometry : ∀ i, (fun j => x (i,.inl (.inl j))) = (c i).val.words) (i : Fin (fan S)) :
    let p := (c i).val.pack
    let route := routes deep ht c i
    let names := (c i).val.rows.siteRoutes route S.radius
    let y := fun z => (W).eval input (i,.inl z)
    PublicEndpoints.Represents (route.subdivided S.radius).layout names.site names.edge
      (RouteRows.stripeDummy p route (c i).val.rows (c i).val.dummy) (fun z => y (.inr (.inr z))) ∧
      ∀ j, y (.inl j) = true ↔ j ∈ Set.range names.edge := by
  intro p route names y
  let a := (comp).input c
  let z := (a.flat i).val
  have childEq : (fun j : Fin (fan S) × Boundary.Pins S start (boundaryShape S start) w t =>
      x (j.1,.inl (.inl j.2))) = childWords c := funext fun j => congrFun (geometry j.1) j.2
  have same : y = z.words := by
    funext j
    have hj := (comp).widthPre_geo rfl ports fit (fun u v => x (u,.inl v)) i j
    exact hj.trans ((congrArg (fun f => (comp).pre.eval f (i,j)) childEq).trans (congrFun (a.initialWords i) j))
  let original := RouteRows.initialDirectory p route (c i).val.rows (c i).val.dummy S.radius_pos
  have loc := RouteRows.actual_initial S.radius_pos z.placed (a.initialSites i) p route
    (S.start_level (offset S start t)) (a.originalPack i) (a.originalRoutes i)
  have chk := endpoints_at_names z.placed (route.initialPlacedPack S.radius_pos) z.names original
    (S.start_level (offset S start t)) loc (a.names i) z.words
    (a.flat i).property.reads.geometry.names (a.flat i).property.reads.present
  rw [same]; exact chk

variable (port : Port (fan S) P t ↪ Fin (portSlots S start t 0))
    (seedNum : ∀ i : Fin S.rounds, ((Cube D → Deck (S.level (offset S start t) (i.val+1)+1)) × (S.source.pattern i).bins.Bin) → ℕ)
local notation3 (prettyPrint := false) "privateRows" => (comp).program.privateSiteRows port seedNum

/-- Every real named child at the first inner stage receives the complete executable
row sequence of its genuine installed program, with no geometry-specific tape input. -/
theorem tapePre_image (i : Fin (fan S))
    (geometry : ∀ j, (fun z => x (j,.inl (.inl z))) = (c j).val.words)
    (widths : ∀ v b, value (fun j => x (i,.inl (.inr ((c i).val.rows.site v,b,j)))) =
      if b then (old i v).program.size else (old i v).program.work)
    (previous : (Fmt).schema.Image (fun z => x (i,.inr z)) ((c i).val.rows.site.trans Fin.valEmbedding)
      (fun v => (old i v).program))
    (portOK : ports.Reads (c i).val.pack.layout (c i).val.rows.site port)
    (widthFit : ∀ j, ports.width j < 2^w) (one : 1 < 2^w)
    (oldFit : ∀ v, incoming (c i).val.pack.layout v < 2^w)
    (newFit : ∀ z, incoming ((routes deep ht c i).subdivided S.radius).layout z < 2^w)
    (room : ∀ v, (old i v).program.size + incoming ((routes deep ht c i).subdivided S.radius).layout (.inl v) < 2^w) :
    (outFmt).schema.Image (fun z => (tapePre C base t ht ports fit).eval x (i,.inr z))
      ((((comp).epoch.run c).flat i).val.names.sites.trans Fin.valEmbedding)
      (fun v => ((comp).epoch.installedPrivatePrograms privateRows c old i v).program) := by
  let row := (c i).val.rows
  let rt := routes deep ht c i
  let p := (c i).val.pack
  let next := row.siteRoutes rt S.radius
  let raw := priorEndpoints (S := S) (start := start) (w := w) t
  have original : PublicEndpoints.Represents p.layout row.site row.edge (c i).val.dummy
      (fun z => x (i,.inl (.inl (raw z)))) := by
    have read : (fun z => x (i,.inl (.inl (raw z)))) =
        (fun z => (c i).val.words (.inr (.inr z))) := funext fun z => congrFun (geometry i) (raw z)
    rw [read]
    exact (c i).property.ready.names
  obtain ⟨endpoints,alive⟩ := pre_names C base t ht ports fit c x geometry i
  have img := PrepBatch.batch_image (B := leafB) (extra := interiors S) (s := shape₀) Fmt raw ports fit W x i
    p.layout (rt.routes S.radius) row (Rows.route_interior_le rt S.radius) port (c i).val.dummy
    (RouteRows.stripeDummy p rt row (c i).val.dummy) (old i)
    original endpoints alive portOK widthFit (Subdivision.Gates.siteRoutes_length rt S.radius) widths previous oldFit newFit room one
  exact (comp).installedTape_image privateRows c old i rfl (outFmt).schema
    (fun z => (tapePre C base t ht ports fit).eval x (i,.inr z)) img

end PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

end BorderVNP
end Computability
end OAI
