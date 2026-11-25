import OAI.Computability.BorderVNP.PackedFrozenNodeProgram
import OAI.Computability.BorderVNP.PackedFrozenTapeSave
import OAI.Computability.BorderVNP.PackedHistoryCompilerRows
import OAI.Computability.BorderVNP.PackedHistoryPrivateNamedRows
import OAI.Computability.BorderVNP.PackedInheritedWorkNames

/-! # Installing the emitted shortening-node tape on the exact saved site programs

The site and cable assignments come from one seed enumeration on the actual
named program. The second dense cable sort carries the complete row image
to that program's attained successor.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows DirectoryCircuit
open Shortening.CombiningStep PackedHistoryCircuit.Normalized
open scoped Classical

variable {D m : ℕ} [NeZero D] {K P A : Type} [Field K] [Fintype P] [Fintype A]
    {bits : P → ℕ} (e : PaidIdentity K D m) (p : Pack D P bits K) (bin : p.layout.Edge → Option A)
    (perm : Fin D → Equiv.Perm A) (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
variable {s s' n n' old np d : ℕ} (site : (output e p bin perm positive first q).layout.Site ↪ Fin s)
    (site' : (output e p bin perm positive first q).layout.Site ↪ Fin s')
    (edge : (output e p bin perm positive first q).layout.Edge ↪ Fin n)
    (edge' : (output e p bin perm positive first q).layout.Edge ↪ Fin n')
    (original : p.layout.Edge ↪ Fin old) (port : P ↪ Fin np) (seedName : A → ℕ) (position : e.Entry → ℕ)
    (state : p.layout.Site → Site) {R B : Type*} (S : Schema R B) (x : Pins R B d → Bool)

/-- Equality of numeric names and of their public capacities transports every
row and each site's program across the two physical rectangle casts. -/
theorem round_image_cast (hs : s = s') (hn : n = n') (vs : ∀ v,(site v).val=(site' v).val)
    (ve : ∀ z,(edge z).val=(edge' z).val)
    (h : S.Image x (site.trans Fin.valEmbedding)
      (roundSites e p bin perm positive first q seedName position site edge port state
        (fun v => Layer.orderedCuts p original port v e bin perm seedName positive first q edge))) :
    S.Image x (site'.trans Fin.valEmbedding)
      (roundSites e p bin perm positive first q seedName position site' edge' port state
        (fun v => Layer.orderedCuts p original port v e bin perm seedName positive first q edge')) := by
  subst s'; subst n'
  have siteEq : site = site' := DFunLike.ext _ _ fun v => Fin.ext (vs v)
  have edgeEq : edge = edge' := DFunLike.ext _ _ fun z => Fin.ext (ve z)
  simpa only [siteEq,edgeEq] using h

end Packing.Inherited.FrozenTape

namespace PackedHistoryCircuit.Normalized.SourcePath.NamedRun

open Cover Crossing Shortening Shortening.Adaptive Shortening.PublicParallel Shortening.StaticRows
open Epoch Epoch.Round Shortening.CombiningStep Packing.DirectoryCircuit Packing Packing.Inherited Packing.Inherited.FrozenTape
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 2400000

variable {D m b k last high w np : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {h H ν : ℝ} {path : SourcePath b e h H ν} {V E cap : ℕ → ℕ}
    {Extra : ℕ → Type*} {keep : ∀ j,path.NamedAt last high V E w P bits k Extra j → Prop} {hk : 0<k}
    {nodes : ∀ i : Fin b,path.Node last high V E w k i} (r : path.NamedRun last high V E w cap keep hk nodes)
    (i : Fin b) (c : Fin k → NamedState.Admissible (path.NamedGood last high V E w cap keep) i.val)
    (q : (r.program.stage i c).Index e) (port : P ↪ Fin np)
    (names : ∀ i : Fin b, Shortening.PublicDenseReceipt.Seed (path.pattern i).bins (path.asPath.depth last high (i.val+1)) → ℕ)
    (position : e.Entry → ℕ) (old : ∀ j, Site.Programs (c j).val.placed.pack.layout)
    {R B : Type*} (S : Schema R B) {d : ℕ} (out : FrozenTape.Pins R B d → Bool)

local notation3 "st" => r.program.stage i c
local notation3 "dir" => r.directory i c q
local notation3 "seed" => (r.directorySeed i).toEmbedding
local notation3 "source" => raw (fun j => (c j).val.placed)
local notation3 "priorID" => CutCircuit.denseRows (source).layout (st).slot
local notation3 "port₁" => Parallel.nestedPorts k port (i.val+1)
local notation3 "site₁" => siteRows e (st).input (parallelName fun j => (c j).val.names.sites) seed
local notation3 (prettyPrint := false) "edge₁" => outputRows e (st).input (st).label (st).perm (st).orient (0,false) q priorID seed

set_option backward.isDefEq.respectTransparency false in
/-- On the attained histogram, the concrete node image is the full image of the
actual saved private programs. This uses both real directory-number equations
from the same seed choice, and the named run's exact second dense sort. -/
theorem installed_tape
    (sRect : V (i.val+1) = siteCapacity e (k*V i.val) (Fintype.card (Shortening.PublicDenseReceipt.Seed
      (path.pattern i).bins (path.asPath.depth last high (i.val+1)))))
    (eRect : E (i.val+1) = edgeCapacity e (k*E i.val) (Fintype.card (Shortening.PublicDenseReceipt.Seed
      (path.pattern i).bins (path.asPath.depth last high (i.val+1)))))
    (himg : S.Image out ((site₁).trans Fin.valEmbedding)
      (roundSites e (st).input (st).label (st).perm (st).orient (0,false) q (names i) position site₁ edge₁ port₁
        (fun z => (old z.1 z.2).program)
        (fun v => Layer.orderedCuts (st).input priorID port₁ v e (st).label (st).perm (names i) (st).orient (0,false) q edge₁))) :
    S.Image out ((r.program.advance i c q).val.names.sites.trans Fin.valEmbedding)
      (fun v => (r.program.savePrivatePrograms r.saveNames (r.privateSiteRows port names) position i c q old v).program) := by
  have physical := r.directorySeed_spec i c q
  have rowCount : (st).rowCount = k*E i.val := (r.installed i c).capacity
  have he : edgeCapacity e (st).rowCount (Fintype.card (Shortening.PublicDenseReceipt.Seed
      (path.pattern i).bins (path.asPath.depth last high (i.val+1)))) = E (i.val+1) := by rw [rowCount]; exact eRect.symm
  have saved := FrozenTape.round_image_cast e (st).input (st).label (st).perm (st).orient (0,false) q site₁
    (dir).sites edge₁ (dir).cables priorID port₁ (names i) position (fun z => (old z.1 z.2).program) S out
    sRect.symm he (fun v => (physical.1 v).symm) (fun z => (physical.2 z).symm) himg
  let programs := (st).privatePrograms e q old (dir).sites (dir).cables port₁ (names i) position
  have actual : S.Image out ((dir).sites.trans Fin.valEmbedding) (fun v => (programs v).program) := by
    have same := funext ((st).privatePrograms_program e q old (dir).sites (dir).cables port₁ (names i) position)
    rw [show (fun v => (programs v).program) = _ from same]
    exact saved
  exact FrozenTape.dense_image S ((st).result e q) (r.program.advance i c q).val.placed dir
    (r.program.advance i c q).val.names (r.stored i c q) (r.saved_names i c q) programs out actual

end PackedHistoryCircuit.Normalized.SourcePath.NamedRun

end BorderVNP
end Computability
end OAI
