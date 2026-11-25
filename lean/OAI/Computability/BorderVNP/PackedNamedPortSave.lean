import OAI.Computability.BorderVNP.PackedNamedEndpointTransport
import OAI.Computability.BorderVNP.PackedInheritedWorkNames

/-! # Stable result rows of the actual named combining step -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SourcePath.NamedRun

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive Shortening.PublicRelative Shortening.PublicParallel
open Shortening.StaticRows Shortening.CombiningStep Shortening.PublicEndpoints Packing Inherited CellAddressCircuit
open DirectoryCircuit
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
local notation3 (prettyPrint := false) "sd" => (r.directorySeed i).toEmbedding
local notation3 (prettyPrint := false) "seedN" => Fintype.card (Shortening.PublicDenseReceipt.Seed (path.pattern i).bins (path.asPath.depth last high (i.val+1)))
local notation3 (prettyPrint := false) "old" => CutCircuit.denseRows (raw fun j => (c j).val.placed).layout (st).slot
local notation3 (prettyPrint := false) "vs" => siteRows e (st).input (parallelName fun j => (c j).val.names.sites) sd
local notation3 (prettyPrint := false) "es" => outputRows e (st).input (st).label (st).perm (st).orient (0,false) q old sd

variable {σ : Type} {C d a : ℕ} (F : Fields (V (i.val+1)) (E (i.val+1)) np C d a w σ)
    (ports : Port k P (i.val+1) ↪ Fin np) {x : σ → Bool}

/-- The physical output cable name in the preallocated successor rectangle.
Only its type needs the equality of the selected row count and the static
parallel input capacity. -/
noncomputable def resultCableRows : ((st).result e q).pack.layout.Edge ↪ Fin (edgeCapacity e (k*E i.val) seedN) :=
  (es).trans (finCongr (congrArg (fun a => edgeCapacity e a seedN) (r.installed i c).capacity)).toEmbedding

/-- The true named result rows are precisely the arithmetic rows of the
preselected code at the static site and cable capacities. -/
theorem resultFieldRows (sv : V (i.val+1) = siteCapacity e (k*V i.val) seedN)
    (se : E (i.val+1) = edgeCapacity e (k*E i.val) seedN)
    (raw : Views.EndpointData ((st).result e q).pack.layout F (dir).sites (dir).cables ports x) :
    Views.EndpointData ((st).result e q).pack.layout (F.castRect sv se) vs (r.resultCableRows i c q) ports x := by
  have ids := r.directorySeed_spec i c q
  exact raw.castRect F ports sv se ids.1 ids.2

/-- Transport the saved branch's true readback to the native unsorted
result, using the same static seed code for site names and cable names. -/
theorem resultPortEndpoints (sv : V (i.val+1) = siteCapacity e (k*V i.val) seedN)
    (se : E (i.val+1) = edgeCapacity e (k*E i.val) seedN)
    (saved : Views.EndpointData (r.program.advance i c q).val.placed.pack.layout F (r.program.advance i c q).val.names.sites
      (r.program.advance i c q).val.names.cables ports x) :
    Views.EndpointData ((st).result e q).pack.layout (F.castRect sv se) vs (r.resultCableRows i c q) ports x :=
  r.resultFieldRows i c q F ports sv se (Views.EndpointData.of_named_save ((st).result e q)
    (r.program.advance i c q).val.placed dir (r.program.advance i c q).val.names F ports
    (r.stored i c q) (r.saved_names i c q) saved)

end PackedHistoryCircuit.Normalized.SourcePath.NamedRun

end BorderVNP
end Computability
end OAI
