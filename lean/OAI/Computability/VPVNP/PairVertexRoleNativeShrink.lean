import OAI.Computability.VPVNP.PairShrinkSelectedParent
import OAI.Computability.VPVNP.PairShrinkRoleCanonicalReader

/-! # Native shrinking reader on every selected chronological output row -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage.RoleDomains

open BurstRAM PrivateRAM DFS NodeArguments TreeDecode Compression CompressorRecords LocalHistory
open TraversalRows TraversalRoles ShrinkRoleDirectory

variable {k : Type} {K : Type*} [Field k] [CommRing K] {S : BlockSchedule k} {B : S.Templates}
    {f : B.Entry → K} {hf : B.IsSolution f}
variable {w n t a g : ℕ} (X : State a g) (cap base : ℕ)
    (passes : List (SelectedLevel B f hf)) (R : LeafArena.Regions) (data : Fin 10 → Word w)
    (offset : Word w) (vals : LeafSourceLoad.Static 34 → Word w)
    (hist : Scratch w n → B.Entry → ℕ) (nodeCap limit : ℕ)

local notation "leaf₀" => TaggedLayer.mk (leafLayer (siteOrder X)) Role.cursor
local notation "tags₀" => (leaf₀) :: outputTags passes

/-- The selected site's original kernel determines the types of its native
address, packed fields, row sources and matrix-job operands. -/
abbrev SiteBank := (x : ShrinkSite passes) →
  ShrinkRole.CanonicalSite B x.occurrence.i x.occurrence.state x.occurrence.selection x.occurrence.site w n t

variable (sites : SiteBank (w := w) (n := n) (t := t) passes) (ord : B.Entry → Fin t)

/-- Read the chronological parent address before running its concrete
shrinking kernel with the recovered independent output half. -/
noncomputable def shrinkHandler : HookParser w n :=
  ShrinkRoleDirectory.parser cap base (leaf₀) passes fun x => ShrinkRole.canonicalParent (sites x) ord f hf

attribute [local irreducible] ShrinkRoleDirectory.occurrence ShrinkRole.canonicalFamily ShrinkRole.canonicalActions
  ShrinkRole.parentParser

set_option maxHeartbeats 1500000 in
/-- The exact native family at each stored parent supplies the complete
selected shrinking reader on both accepting and rejecting tapes. -/
theorem nativeShrink {p r : ℕ} (M : Machine w p r 11) (visit ret : Fin p)
    (dfs : Fin 9 ↪ Fin r) (m : Memory w) (positive : 0 < w)
    (fit : layerBase cap base (tags₀) (passes.length+1) ≤ 2^w)
    (arena : ∀ x, (TerminalLayout.privateRegions (slotDegree S) n (sites x).rowEnd
      (Fintype.card B.Entry)).arguments = R.arguments)
    (actual : ∀ (x : ShrinkSite passes) (z : x.occurrence.nextState.network.Half x.occurrence.site), (ShrinkRole.canonicalFamily (sites x) ord f hf z).ExactOn
      (fun node s => node.val = ShrinkRoleDirectory.address cap base (leaf₀) passes x.val ∧
        Parent X cap base passes R data offset vals hist nodeCap limit x z s) M visit ret dfs m) :
    (shrinkHandler X cap base passes sites ord).ExactOn
      (Domain X cap base passes R data offset vals hist nodeCap limit .shrink) M visit ret dfs m := by
  apply ShrinkRoleDirectory.exactOn cap base (leaf₀) passes M visit ret dfs m _ _ fit
  intro x
  dsimp only [ShrinkRole.canonicalParent]
  rw [arena x]
  exact parent_exact X cap base passes R data offset vals hist nodeCap limit x M visit ret dfs m
    positive _ (actual x)

end PairSimulation.VertexImage.RoleDomains

end VPVNP
end Computability
end OAI
