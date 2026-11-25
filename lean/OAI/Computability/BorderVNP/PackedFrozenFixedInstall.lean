import OAI.Computability.BorderVNP.PackedFrozenNamedInstall
import OAI.Computability.BorderVNP.PackedNamedPortSave

/-! # The fixed schedule's cable rectangle installs the attained private program -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SourcePath.NamedRun

open Cover Crossing Shortening Shortening.Adaptive Shortening.PublicParallel Shortening.StaticRows
open Epoch Epoch.Round Shortening.CombiningStep Packing.DirectoryCircuit Packing Packing.Inherited Packing.Inherited.FrozenTape
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1800000

variable {D m b k last high w np : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {h H ν : ℝ} {path : SourcePath b e h H ν} {V E cap : ℕ → ℕ}
    {Extra : ℕ → Type*} {keep : ∀ j,path.NamedAt last high V E w P bits k Extra j → Prop} {hk : 0<k}
    {nodes : ∀ i : Fin b,path.Node last high V E w k i} (r : path.NamedRun last high V E w cap keep hk nodes)
    (i : Fin b) (c : Fin k → NamedState.Admissible (path.NamedGood last high V E w cap keep) i.val)
    (q : (r.program.stage i c).Index e) (port : P ↪ Fin np)
    (names : ∀ i : Fin b, Shortening.PublicDenseReceipt.Seed (path.pattern i).bins (path.asPath.depth last high (i.val+1)) → ℕ)
    (position : e.Entry → ℕ) (old : ∀ j, Site.Programs (c j).val.placed.pack.layout)
    {R B : Type*} (S : Schema R B) {d : ℕ} (out : FrozenTape.Pins R B d → Bool)

local notation3 (prettyPrint := false) "A" => Shortening.PublicDenseReceipt.Seed (path.pattern i).bins (path.asPath.depth last high (i.val+1))
local notation3 (prettyPrint := false) "st" => r.program.stage i c
local notation3 (prettyPrint := false) "oldID" => CutCircuit.denseRows (raw (fun j => (c j).val.placed)).layout (st).slot
local notation3 (prettyPrint := false) "site" => siteRows e (st).input (parallelName fun j => (c j).val.names.sites) (r.directorySeed i).toEmbedding
local notation3 (prettyPrint := false) "port₁" => Parallel.nestedPorts k port (i.val+1)
local notation3 (prettyPrint := false) "edge" => outputRows e (st).input (st).label (st).perm (st).orient (0,false) q oldID (r.directorySeed i).toEmbedding
local notation3 (prettyPrint := false) "physical" => r.resultCableRows i c q

set_option backward.isDefEq.respectTransparency false in
/-- The one physical kernel may use the fixed edge capacity throughout. Its site
and cable numbers still install the true saved private programs. -/
theorem fixed_installed_tape (sv : V (i.val+1) = siteCapacity e (k*V i.val) (Fintype.card A))
    (se : E (i.val+1) = edgeCapacity e (k*E i.val) (Fintype.card A))
    (img : S.Image out ((site).trans Fin.valEmbedding)
      (roundSites e (st).input (st).label (st).perm (st).orient (0,false) q (names i) position site physical port₁
        (fun z => (old z.1 z.2).program)
        (fun v => Layer.orderedCuts (st).input oldID port₁ v e (st).label (st).perm (names i) (st).orient (0,false) q physical))) :
    S.Image out ((r.program.advance i c q).val.names.sites.trans Fin.valEmbedding)
      (fun v => (r.program.savePrivatePrograms r.saveNames (r.privateSiteRows port names) position i c q old v).program) := by
  apply r.installed_tape i c q port names position old S out sv se
  exact round_image_cast e (st).input (st).label (st).perm (st).orient (0,false) q site site physical edge
    oldID port₁ (names i) position (fun z => (old z.1 z.2).program) S out rfl
    (congrArg (fun z => edgeCapacity e z (Fintype.card A)) (r.installed i c).capacity.symm)
    (fun _ => rfl) (fun _ => rfl) img

end PackedHistoryCircuit.Normalized.SourcePath.NamedRun

end BorderVNP
end Computability
end OAI
