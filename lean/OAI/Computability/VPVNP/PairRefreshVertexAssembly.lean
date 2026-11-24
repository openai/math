import OAI.Computability.VPVNP.PairVertexLevelLocator
import OAI.Computability.VPVNP.PairVertexStagePrefix
import OAI.Computability.VPVNP.PairVertexSegmentChain

/-!
# The refresh role's complete vertex image

The level locator runs first, using the fourteen registers retained by the
refresh body. The handoff and child scan then fill the private child argument
buffer. The remainder of the body reuses the saved locator values and returns
to the DFS continuation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshVertexAssembly

open BurstRAM BurstRAM.PrivateRAM VertexImage VertexStagePrefix NodeArguments
open TraversalControllerInputs TraversalRows TraversalRoles
open scoped Fin.CommRing

variable (a : ℕ) (body : Segment) (locator : Fin 14 ↪ Fin body.privateRegs)

/-- The refresh child-argument preparation and its continuation into the resident kernel body. -/
abbrev childBody := withChildren a body locator

/-- The locator register bank as embedded in the complete refresh vertex segment. -/
def locatorBank : Fin 14 ↪ Fin (childBody a body locator).privateRegs :=
  locator.trans (Fin.castAddEmb (ChildCode.RegisterBank.segment a).privateRegs)

/-- One role entry for the locator, argument scan and the kernel body. -/
def segment := Segment.thenWith VertexLevel.segment (childBody a body locator)
  (locatorBank a body locator) (Function.Embedding.refl _)

variable {w p r : ℕ} (loc : Fin (segment a body locator).count → Fin p)
  (dfs : Fin 9 ↪ Fin r) (saved : Saved ↪ Fin r) (reg : Fin (segment a body locator).privateRegs ↪ Fin r)
  (done : Fin p) (M : Machine w p r 11)

/-- Program counters of the level-location phase preceding child preparation. -/
def levelPC := Segment.leftPC VertexLevel.segment (childBody a body locator) loc
/-- Program counters in the combined child-preparation and resident-body segment following the
level scan. -/
def childPC := Segment.rightPC VertexLevel.segment (childBody a body locator) loc
/-- Program counters of the resident refresh body after the child argument has been installed. -/
def bodyPC := (childPreparation a body locator).bodyPC (childPC a body locator loc)
/-- Embedding of the resident refresh body's private registers inside the child-preparation
segment. -/
def bodyRegs := Preparation.bodyRegs (ChildCode.RegisterBank.segment a) body reg
/-- The level locator's registers transported through the resident body's embedding. -/
def levelRegs := locator.trans (bodyRegs a body locator reg)

/-- Agreement of the installed refresh vertex instructions with the width-resized assembly at
each placed address. -/
def Installed : Prop := ∀ i, M.code (loc i) = ((segment a body locator).row loc dfs saved reg done i).resize w

variable (installed : Installed a body locator loc dfs saved reg done M)

include installed in
theorem linked :
    (∀ i, M.code (levelPC a body locator loc i) = (VertexLevel.segment.row (levelPC a body locator loc)
      dfs saved (levelRegs a body locator reg) (childPC a body locator loc (childBody a body locator).entry) i).resize w) ∧
    (∀ i, M.code (childPC a body locator loc i) = ((childBody a body locator).row (childPC a body locator loc)
      dfs saved reg done i).resize w) := by
  exact Segment.split_link VertexLevel.segment (childBody a body locator) (locatorBank a body locator)
    (Function.Embedding.refl _) loc dfs saved reg done M installed

include installed in
theorem body_linked (i) : M.code (bodyPC a body locator loc i) = (body.row (bodyPC a body locator loc)
    dfs saved (bodyRegs a body locator reg) done i).resize w :=
  (child_rows a body locator M (childPC a body locator loc) dfs saved reg done
    (linked a body locator loc dfs saved reg done M installed).2).2.2.2 i

include installed in
/-- Locate the actual noninitial node before reading its children. The locator
writes only its assigned registers and reaches the first handoff instruction. -/
theorem locate {m : Memory w} {header first pitch offset cap base : ℕ} {old : TaggedLayer} {ls : List (Fiber w)}
    (resident : TraversalControllerInputs.Resident M.publicData m header first pitch offset cap base old ls)
    (j : Fin (old :: ls.map Prod.fst).length) (level : ℕ) (hj : j.val = level+1)
    (id : Fin (old :: ls.map Prod.fst)[j].layer.count) (c : Config w p r)
    (entry : c.pc = loc (segment a body locator).entry)
    (node : (c.reg (dfs 7)).val = address cap (layerBase cap base (old :: ls.map Prod.fst) j) id)
    (fit : layerBase cap base (old :: ls.map Prod.fst) (ls.length+1) < 2^w) :
    ∃ out, ChildScan.Prefix M m c out [] (VertexLevel.trace M.publicData m (level+1) (ls.length-(level+1))) ∧
      out.pc = childPC a body locator loc (childBody a body locator).entry ∧
      VertexLevel.Located M.publicData m (levelRegs a body locator reg) (c.reg (dfs 7)) level (id.val : Word w) out ∧
      VertexLevel.Frame (levelRegs a body locator reg) c out :=
  VertexLevel.run M (levelPC a body locator loc) dfs saved (levelRegs a body locator reg) _
    (linked a body locator loc dfs saved reg done M installed).1 resident j level hj id c entry node fit

end PairSimulation.RefreshVertexAssembly

end VPVNP
end Computability
end OAI
