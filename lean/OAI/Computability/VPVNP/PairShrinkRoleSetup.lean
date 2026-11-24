import OAI.Computability.VPVNP.PairShrinkRoleStages
import OAI.Computability.VPVNP.PairShrinkRoleHandoff
import OAI.Computability.VPVNP.PairVertexLevelLocator

/-!
# Physical operand loads of a shrinking visit

The level scan reads the old header and computes the packed owner of the popped
row. The child handoff copies the node and old-field address. The hidden
handoff obtains its owner and old header from the locator and its stride from
the geometry in private memory. All three stages preserve the pending stack.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM BurstRAM.PrivateRAM DFS TraversalControllerInputs TraversalRoles TraversalRows
open VertexLevelBounds
open scoped Fin.CommRing

variable {w p r endAddr : ℕ} {M : Machine w p r 11} {m : Memory w}
  {dfs : Fin 9 ↪ Fin r} {regs : Fin 14 ↪ Fin r} {next : Fin p}
  {pre post : Word w → Config w p r → Prop}

/-- The trace of the selected level scan includes every candidate level it passes. -/
def locatorSetup (pub : Fin 11 → Word w) (m : Memory w) (level later : ℕ) : Setup w endAddr where
  trace _ _ := VertexLevel.trace pub m level later
  updated _ s := s
  quiet _ _ := (VertexLevel.trace_cost pub m level later).2.2

/-- Locate a genuine noninitial row, without relying on any scratch register at entry. -/
theorem locator_realizes {loc : Fin 35 → Fin p} {saved : VertexImage.Saved ↪ Fin r}
    (code : ∀ i, M.code (loc i) = (VertexLevel.segment.row loc dfs saved regs next i).resize w)
    {H first pitch offset cap base : ℕ} {old : TaggedLayer} {ls : List (Fiber w)}
    (resident : Resident M.publicData m H first pitch offset cap base old ls)
    (stage : Fin (old :: ls.map Prod.fst).length) (level : ℕ) (hs : stage.val = level + 1)
    (id : Fin (old :: ls.map Prod.fst)[stage].layer.count)
    (fit : layerBase cap base (old :: ls.map Prod.fst) (ls.length + 1) < 2 ^ w)
    (separate : ∀ i : Fin 9, i = 3 ∨ i = 5 ∨ i = 6 ∨ i = 7 → dfs i ∉ Set.range regs)
    (start : ∀ node c, pre node c → c.pc = loc VertexLevel.segment.entry ∧
      c.reg (dfs 7) = node ∧ node.val = address cap (layerBase cap base (old :: ls.map Prod.fst)
        stage) id)
    (resume : ∀ node c d, pre node c → d.pc = next →
      VertexLevel.Located M.publicData m regs node level (id.val : Word w) d →
      VertexLevel.Frame regs c d → post node d) :
    Realizes (endAddr := endAddr)
      (locatorSetup M.publicData m (level + 1) (ls.length - (level + 1))).reader
      M m dfs pre (fun _ => post) := by
  apply Setup.realizes
  intro node c hc
  obtain ⟨pc,hnode,addr⟩ := start _ _ hc
  obtain ⟨d,run,done,located,fr⟩ :=
    VertexLevel.run M loc dfs saved regs next code resident stage level hs id c pc
      (hnode ▸ addr) fit
  exact ⟨d, resume node c d hc done (hnode ▸ located) fr,
    ⟨fun i hi => fr.outside _ (separate i hi), fun a _ => congrFun fr.privateMem a,
      fr.persistent⟩, congrArg (DFS.scratch endAddr) fr.privateMem, run⟩

/-- The two real copy rows prepare the node and directory pointer in the child bank. -/
theorem childHandoff_realizes {pc : Fin 2 → Fin p} {child : Fin 16 ↪ Fin r}
    (code : ∀ i, M.code (pc i) = VertexLevel.childHandoff pc regs child next i)
    (apart : child 7 ≠ regs 12)
    (separate : ∀ i : Fin 9, i = 3 ∨ i = 5 ∨ i = 6 ∨ i = 7 → dfs i ≠ child 7 ∧ dfs i ≠ child 8)
    (start : ∀ node c, pre node c → c.pc = pc 0)
    (resume : ∀ node c d, pre node c → d.pc = next → d.reg (child 7) = c.reg (regs 0) →
      d.reg (child 8) = c.reg (regs 12) →
      (∀ q, q ≠ child 7 → q ≠ child 8 → d.reg q = c.reg q) →
      d.privateMem = c.privateMem → d.persistent = c.persistent → post node d) :
    Realizes (Setup.ticks (endAddr := endAddr) 2).reader M m dfs pre (fun _ => post) := by
  apply Setup.realizes
  intro node c hc
  obtain ⟨d,run,done,nodeWord,dirWord,keep,mem,pers⟩ :=
    VertexLevel.childHandoff_run code apart c (start _ _ hc) m
  exact ⟨d, resume node c d hc done nodeWord dirWord keep mem pers,
    ⟨fun i hi => keep _ (separate i hi).1 (separate i hi).2, fun a _ => congrFun mem a, pers⟩,
    congrArg (DFS.scratch endAddr) mem, run⟩

/-- The installed rows compute the owner, scratch base beyond the scalar stacks,
stride, and old level.
The squared stride uses the geometry word at offset nine. -/
theorem hiddenHandoff_realizes {pc : Fin VertexLevel.hiddenCount → Fin p}
    {inputs : Fin 6 ↪ Fin r} {stackEnd : Fin r}
    (code : ∀ i, M.code (pc i) = VertexLevel.hiddenHandoff pc regs inputs stackEnd next i)
    (apart : ∀ i j, inputs i ≠ regs j)
    (separate : ∀ i : Fin 9, i = 3 ∨ i = 5 ∨ i = 6 ∨ i = 7 → ∀ j, dfs i ≠ inputs j)
    (start : ∀ node c, pre node c → c.pc = pc 0)
    (resume : ∀ node c d, pre node c →
      let geom := c.privateMem (c.reg stackEnd)
      let n := c.privateMem (geom + 9)
      d.pc = next → d.reg (inputs 0) = c.reg (regs 7) →
      d.reg (inputs 1) = VertexLevel.hiddenBaseWord (c.privateMem (geom + 8)) n →
      d.reg (inputs 2) = n * n → d.reg (inputs 5) = c.reg (regs 11) →
      (∀ q, q ≠ inputs 0 → q ≠ inputs 1 → q ≠ inputs 2 → q ≠ inputs 5 → d.reg q = c.reg q) →
      d.privateMem = c.privateMem → d.persistent = c.persistent → post node d) :
    Realizes (Setup.ticks (endAddr := endAddr) VertexLevel.hiddenCount).reader M m dfs
      pre (fun _ => post) := by
  apply Setup.realizes
  intro node c hc
  obtain ⟨d,run,done,owner,base,stride,head,keep,mem,pers⟩ :=
    VertexLevel.hiddenHandoff_run code apart c (start _ _ hc) m
  exact ⟨d, resume node c d hc done owner base stride head keep mem pers,
    ⟨fun i hi => keep _ (separate i hi 0) (separate i hi 1) (separate i hi 2) (separate i hi 5),
      fun a _ => congrFun mem a, pers⟩, congrArg (DFS.scratch endAddr) mem, run⟩

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
