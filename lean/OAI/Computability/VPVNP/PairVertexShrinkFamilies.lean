import OAI.Computability.VPVNP.PairShrinkSiteOrdinal
import OAI.Computability.VPVNP.PairVertexRoleNativeShrink
import OAI.Computability.VPVNP.PairShrinkRoleCanonicalExecution
import OAI.Computability.VPVNP.PairShrinkCallFrameStores

/-! # Canonical shrinking families at the actual selected directory addresses -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage.RoleDomains

open BurstRAM PrivateRAM DFS Compression CompressorRecords LocalHistory TraversalRows TraversalRoles
open ShrinkRoleDirectory ShrinkVertexImage TraversalControllerInputs NodeArguments TreeDecode
open scoped Fin.CommRing

set_option quotPrecheck false
attribute [local irreducible] ShrinkRoleDirectory.occurrence BlockProgram.layout
  BlockSchedule.Templates.execute StateExecution.finalState executeLevels ShrinkRole.canonicalFamily

variable {k : Type} [Field k] {S : BlockSchedule k} (B : S.Templates)
    {K : Type*} [CommRing K] (f : B.Entry → K) (hf : B.IsSolution f)
    {lanes : ℕ} (T : ℕ) (hT : T*S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
    (branch : (B.execute f hf T hT X).Choices)

local notation "passes₀" => executeLevels B f hf T hT X branch
local notation "leaf₀" => TaggedLayer.mk (leafLayer (siteOrder X)) Role.cursor
local notation "labels₀" => Fintype.card B.Entry

variable {w n p r : ℕ} (ord : B.Entry → Fin (Fintype.card B.Entry))
    (geometry rootFields leaf refresh : Segment)
    (V : Placement (vertexParts B ord geometry rootFields leaf refresh) p r)
    (M : Machine w p r 11) (installed : Contains V M)
    (sites : SiteBank (w := w) (n := n) (t := (Fintype.card B.Entry)) (executeLevels B f hf T hT X branch))
    (base : ℕ) (R : LeafArena.Regions) (data : Fin 10 → Word w)
    (offset : Word w) (vals : LeafSourceLoad.Static 34 → Word w)
    (hist : Scratch w n → B.Entry → ℕ) (nodeCap limit : ℕ) (m : Memory w)

local notation "regAt" => (fun x : ShrinkSite (passes₀) => TerminalLayout.privateRegions (slotDegree S) n (sites x).rowEnd (labels₀))
local notation "rowAt" => (fun x : ShrinkSite (passes₀) => ShrinkRoleDirectory.address B.recordLimit base (leaf₀) (passes₀) x.val)
local notation "par₀" => Parent X B.recordLimit base (passes₀) R data offset vals hist nodeCap limit

include installed in
set_option maxHeartbeats 2500000 in
/-- The published native level and map rows instantiate the exact family for
every independent parent. Its private handoff reads the common geometry
already present in the popped packet's scratch memory. -/
theorem selectedFamilies {raw : Memory w} {publicH first pitch roleBase : ℕ}
    (ds : (j : Fin (passes₀).length) → LevelDirectory (passes₀)[j] raw base)
    (resident : Resident M.publicData m publicH first pitch roleBase B.recordLimit base (leaf₀)
      (levelFibers (passes₀) ds))
    (regionEq : ∀ x, (regAt) x = R) (memEq : ∀ x, (sites x).mem = m)
    (cache : data 8 = (R.cacheBase : Word w)) (length : data 9 = (n : Word w)) (H : Word w)
    (facts : ∀ (x : ShrinkSite (passes₀)), ShrinkRole.CanonicalSiteData (sites x) M f hf T hT X branch x.val.1
      (siteId B f hf T hT X branch x) base)
    (maps : ∀ (x : ShrinkSite (passes₀)) (parent : x.occurrence.nextState.network.Half x.occurrence.site),
      ShrinkRole.CanonicalMapData (sites x) H parent) :
    ∀ (x : ShrinkSite (passes₀)) (parent : x.occurrence.nextState.network.Half x.occurrence.site),
      (ShrinkRole.canonicalFamily (sites x) ord f hf parent).ExactOn
      (fun node s => node.val = (rowAt) x ∧ (par₀) x parent s) M (V.entry .shrink) (V.dfsPC 3) V.dfs m := by
  intro x parent
  let P := (par₀) x parent
  have fd := facts x
  have source : Resident M.publicData (sites x).mem publicH first pitch roleBase B.recordLimit base (leaf₀)
      (levelFibers (passes₀) ds) := by rw [memEq x]; exact resident
  have prepare (priv : Word w → Word w) (h : P (scratch n priv)) :
      ShrinkCallFrameLive.Stored ((regAt) x) n priv := by
    rw [regionEq x]
    exact ShrinkCallFrameLive.of_vertex h.frame cache length ((regionEq x) ▸ fd.above) ((regionEq x) ▸ fd.frameRoom)
  have packet s (h : P s) := h.stored
  have addrEq := rowAddress_siteId B f hf T hT X branch base x
  have regEq : TerminalLayout.privateRegions (slotDegree S) n (sites x).rowEnd (Fintype.card B.Entry) = R :=
    regionEq x
  have run := ShrinkRole.canonicalFamily_exactOn (sites x) ord geometry rootFields leaf refresh V M
    f hf T hT X branch x.val.1 (siteId B f hf T hT X branch x) base ds source installed fd H parent
    (maps x parent) P prepare (fun s h => by rw [fd.siteAddr,← addrEq,regEq]; exact packet s h)
  simpa only [← addrEq,memEq x,P] using run

end PairSimulation.VertexImage.RoleDomains

end VPVNP
end Computability
end OAI
