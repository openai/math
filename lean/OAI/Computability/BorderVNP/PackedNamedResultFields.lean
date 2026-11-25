import OAI.Computability.BorderVNP.PackedNamedPortSave
import OAI.Computability.BorderVNP.PackedInheritedWorkPortPath
import OAI.Computability.BorderVNP.PackedInheritedWorkReceipt

/-! # The unsorted physical endpoint table in the shared selected-node frame

The actual geometric node emits the sparse source and destination words.
The exterior words are the static grouped header, and each inactive
width is zero. These fields supply the native saved bank emitter.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open CellAddressCircuit Shortening.PublicEndpoints PackedHistoryCircuit.TerminalCells

/-- Static fields in the common source frame, using the geometric output
selectors, literal bit selectors, and fixed successor rectangle sizes. -/
def Ports.sharedResultFields {np v e v' e' w : ℕ} {B σ τ : Type*}
    (header : Ports np) (fit : v ≤ 2^w) (pin : Inputs B v e w w → σ)
    (sv : v = v') (se : e = e') (select : σ ⊕ Bool → τ) :
    Fields v' e' np 1 w 0 w τ :=
  ((endpointFields fit pin header.host header.width).castRect sv se).mapPins select

/-- Each successor site key is its actual row ordinal in the frozen
rectangle, also after pin selection and capacity transport. -/
theorem Ports.sharedResultSite {np v e v' e' w : ℕ} {B σ τ : Type*}
    (header : Ports np) (fit : v ≤ 2^w) (pin : Inputs B v e w w → σ)
    (sv : v = v') (se : e = e') (select : σ ⊕ Bool → τ) (i : Fin v') :
    ((header.sharedResultFields fit pin sv se select).sites i).val = i.val :=
  (endpointFields fit pin header.host header.width).castRect_site sv se i

end Packing.Inherited.WorkWords

namespace PackedHistoryCircuit.Normalized.SourcePath.NamedRun

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive Shortening.PublicRelative Shortening.PublicParallel
open Shortening.StaticRows Shortening.CombiningStep Shortening.PublicEndpoints Packing Inherited CellAddressCircuit
open DirectoryCircuit Diagonal.ExternalSew.FieldExport
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2400000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency false

variable {D m b k np last high w : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {h H ν : ℝ} {path : SourcePath b e h H ν} {V E cap : ℕ → ℕ}
    {Extra : ℕ → Type*} {keep : ∀ j,path.NamedAt last high V E w P bits k Extra j → Prop} {hk : 0<k}
    {nodes : ∀ i : Fin b,path.Node last high V E w k i} (r : path.NamedRun last high V E w cap keep hk nodes)
    (i : Fin b) (c : Fin k → NamedState.Admissible (path.NamedGood last high V E w cap keep) i.val)
    (q : (r.program.stage i c).Index e)
local notation3 (prettyPrint := false) "st" => r.program.stage i c
local notation3 (prettyPrint := false) "dir" => r.directory i c q
variable (header : WorkWords.Ports np) (port : Port k P i.val ↪ Fin np)
    (oldReads : ∀ j, header.Reads (c j).val.placed.pack.layout (c j).val.names.sites port)
    (small : (WorkWords.PortTable.mk _ port header).Widths (Shortening.Adaptive.width bits k i.val) w)
local notation3 (prettyPrint := false) "next" => header.parallel k (V i.val)
local notation3 (prettyPrint := false) "portRows" => Parallel.portRows k port
local notation3 (prettyPrint := false) "child" => fun z : Fin k × path.StatePins last high V E w i.val => (c z.1).val.words z.2
local notation3 (prettyPrint := false) "geom" => (nodes i).eval (Sum.elim child (NamedReceipt.word st (r.fits i c) q)) ∘ Sum.inl

include oldReads small in
/-- The literal output of the selected geometry node supplies all seven
endpoint columns on its original combining result. -/
theorem rawResultPortEndpoints (fit : V (i.val+1) ≤ 2^w) :
    let pin := fun z : Inputs (Cover.AddressCircuit.ProductSlots (Fintype.card (Cube D))
      (path.asPath.depth last high (i.val+1)+1) ⊕ ↥(path.catalog (i.val+1)))
      (V (i.val+1)) (E (i.val+1)) w w => (Sum.inr (Sum.inr z) : path.StatePins last high V E w (i.val+1))
    Views.EndpointData ((st).result e q).pack.layout
      (TerminalCells.endpointFields fit pin (next).host (next).width) (dir).sites (dir).cables portRows
      ((constants _).eval geom) := by
  intro pin
  let result := (st).result e q
  let saved := result.dense (dir).cables
  let n := (dir).dense
  have hw := small.parallel k (V i.val)
  have portRead : (next).Reads saved.pack.layout n.sites portRows := by
    refine ⟨?_,hw.live,hw.holes⟩
    rintro ⟨j,z⟩
    have pair := finProdFinEquiv.symm_apply_apply (j,port z)
    have prior := NamedRun.retained_sites path last high V E w cap keep hk r i c q ⟨j,(c j).val.placed.pack.layout.attach z⟩
    change (finProdFinEquiv.symm (finProdFinEquiv (j,port z))).1.val * V i.val +
      header.host (finProdFinEquiv.symm (finProdFinEquiv (j,port z))).2 =
      ((dir).sites (.inl ⟨j,(c j).val.placed.pack.layout.attach z⟩)).val
    rw [pair,(oldReads j).attach,prior]
    change j.val * V i.val + _ = _ + V i.val * j.val
    ac_rfl
  let fields := TerminalCells.endpointFields fit pin (next).host (next).width
  have endpoints := TerminalCells.named_endpoints fit pin (next).host (next).width saved.pack.layout n.sites n.cables
    (dir).dummy portRows geom (r.geometry_endpoints i c q) portRead.attach portRead.size hw.fit portRead.hole
  exact Views.EndpointData.of_named_save result saved dir n fields portRows rfl HEq.rfl endpoints

local notation3 (prettyPrint := false) "seedN" => Fintype.card (Shortening.PublicDenseReceipt.Seed (path.pattern i).bins (path.asPath.depth last high (i.val+1)))
local notation3 (prettyPrint := false) "site" => siteRows e (st).input (parallelName fun j => (c j).val.names.sites) (r.directorySeed i).toEmbedding

include oldReads small in
/-- The selected successor fields in the combined source represent every
original output endpoint at its actual static arithmetic name. -/
theorem sharedResultEndpoints (fit : V (i.val+1) ≤ 2^w)
    (sv : V (i.val+1) = siteCapacity e (k*V i.val) seedN)
    (se : E (i.val+1) = edgeCapacity e (k*E i.val) seedN) {τ : Type}
    (select : (path.StatePins last high V E w (i.val+1) ⊕ Bool) → τ) (y : τ → Bool) (wires : y ∘ select = (constants _).eval geom) :
    let pin := fun z : Inputs (Cover.AddressCircuit.ProductSlots (Fintype.card (Cube D))
      (path.asPath.depth last high (i.val+1)+1) ⊕ ↥(path.catalog (i.val+1)))
      (V (i.val+1)) (E (i.val+1)) w w => (Sum.inr (Sum.inr z) : path.StatePins last high V E w (i.val+1))
    Views.EndpointData ((st).result e q).pack.layout ((next).sharedResultFields (w := w) (v := V (i.val+1)) (e := E (i.val+1)) fit pin sv se select)
      site (r.resultCableRows i c q) portRows y := by
  intro pin
  have nativeEnds := r.rawResultPortEndpoints i c q header port oldReads small fit
  let F := TerminalCells.endpointFields fit pin (next).host (next).width
  have sized := r.resultFieldRows i c q F portRows sv se nativeEnds
  exact Views.EndpointData.mapPins (F.castRect sv se) portRows select y wires sized

end PackedHistoryCircuit.Normalized.SourcePath.NamedRun

end BorderVNP
end Computability
end OAI
