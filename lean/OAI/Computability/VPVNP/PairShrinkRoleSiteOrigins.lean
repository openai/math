import OAI.Computability.VPVNP.PairShrinkRoleSiteOperands
import OAI.Computability.VPVNP.PairShrinkRoleItemOrigins
import OAI.Computability.VPVNP.PairShrinkRoleParsed
import OAI.Computability.VPVNP.PairShrinkRoleChild
import OAI.Computability.VPVNP.PairShrinkRoleHidden

/-!
# The concrete origin retained throughout one selected shrinking map row

The parser has fixed the parent, child list and absorbed fields. The origin
records their actual memory and the initialized map ABI from the installed
header. It may vary with the caller's unused memory and registers.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM BurstRAM.PrivateRAM Compression NodeArguments NodeArguments.ChildScan
open ShrinkHiddenGuess ResidentMapLoop.Exact

variable {w n p r a g k : ℕ} {Z : State a g} (dfs : Fin 9 ↪ Fin r) (common : Fin 24 ↪ Fin r)
  (regions : LeafArena.Regions) (level term : Word w) (address older cap : ℕ)
  (desc : Word w → ChildArguments.Descriptor w Z) (arg : Args w) (seed : List ShrinkHiddenGuess.Row)
  (m : Memory w) (ready : DFS.Scratch w n → Prop)
  (xs : List (Child Z)) (es : List ShrinkHiddenGuess.Row)

/-- The raw entry may vary, but the five map operands, typed stores and accepted
hidden parse are determined by the selected physical data. -/
structure SiteOrigin where
  /-- Word address of the popped node whose row the handler is reading. -/
  node : Word w
  /-- Private memory before the child packets and hidden rows are stored for this visit. -/
  before : Word w → Word w
  /-- Machine configuration on entry to the resident map scan after installing the child
  packets and hidden rows. -/
  entry : Config w p r
  atRow : node.val = address
  prepared : ready (DFS.scratch n before)
  sites : xs.map Child.site = (desc node).sites
  valid : ValidRows arg m es
  parsed : Parsed (n := n) (hiddenReader arg m seed) node es
  operands : SiteMapInput common dfs regions n node level term
    (storeRows arg.scratchBase arg.slotStride es
      (storePackets regions.arguments (xs.map (Child.packet Z older cap)) before)) entry

local notation "Origin" => SiteOrigin (p := p) dfs common regions level term address older cap
  desc arg seed m ready xs es

/-- One retained initial configuration suffices for the whole resident loop. -/
def siteInv (fixed : Origin → Config w p r → Prop) (node : Word w) (c : Config w p r) : Prop :=
  ∃ origin : Origin, origin.node = node ∧ fixed origin c

variable {P : ResidentMapLoop.Program p r} {M : Machine w p r k}

theorem siteInv_stable (fixed : Origin → Config w p r → Prop)
    (stable : ∀ origin, P.Stable (fixed origin)) (node : Word w) :
    P.Stable (siteInv dfs common regions level term address older cap desc arg seed m ready xs es
      fixed node) :=
  OriginInvariant.stable (inv := fun origin _ => fixed origin) (fun origin _ => stable origin) node

/-- The actual header output is one witness for the initial map invariant. -/
theorem siteInv_start (fixed : Origin → Config w p r → Prop)
    (initial : ∀ origin : Origin, fixed origin origin.entry)
    (node : Word w) (priv : Word w → Word w) (c : Config w p r) (atRow : node.val = address)
    (good : ready (DFS.scratch n priv)) (sites : xs.map Child.site = (desc node).sites)
    (valid : ValidRows arg m es) (parsed : Parsed (n := n) (hiddenReader arg m seed) node es)
    (operands : SiteMapInput common dfs regions n node level term
      (storeRows arg.scratchBase arg.slotStride es
        (storePackets regions.arguments (xs.map (Child.packet Z older cap)) priv)) c) :
    siteInv dfs common regions level term address older cap desc arg seed m ready xs es
      fixed node c := by
  let origin : Origin := ⟨node, priv, c, atRow, good, sites, valid, parsed, operands⟩
  exact ⟨origin, rfl, initial origin⟩

/-- The origin may be chosen anew for each compatible entry configuration, while
each selected action is independent of that choice. -/
theorem siteInv_items (fixed : Origin → Config w p r → Prop)
    {start : ℕ} {actions : List (Action w n)} (quiet : ∀ job ∈ actions, NoChoices job)
    (items : ∀ origin : Origin, Items P M m dfs (fun _ => fixed origin) start actions) :
    Items P M m dfs
      (siteInv dfs common regions level term address older cap desc arg seed m ready xs es fixed)
      start actions :=
  Items.existsInvariant (inv := fun origin _ => fixed origin) quiet items

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
