import OAI.Computability.VPVNP.PairShrinkRoleStages
import OAI.Computability.VPVNP.PairShrinkRoleHandoff

/-!
# Caching the hidden-field address during a shrinking visit

The installed handoff reads the live geometry, prepares the hidden scanner's
four inputs, and saves its private base in the locator register used by the
map. The traversal keeps the pending DFS stack throughout these local steps.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing

variable {w p r endAddr : ℕ} {M : Machine w p r 11} {m : Memory w}
  {dfs : Fin 9 ↪ Fin r} {loc : Fin 14 ↪ Fin r} {next : Fin p}
  {pre post : Word w → Config w p r → Prop}

/-- The cached handoff realizes a fixed tick trace and exposes its live
outputs and preserved registers to the next reader. -/
theorem cachedHiddenHandoff_realizes {pc : Fin (VertexLevel.hiddenCount + 1) → Fin p}
    {inputs : Fin 6 ↪ Fin r} {stackEnd : Fin r}
    (linked : ∀ i, M.code (pc i.castSucc) =
      VertexLevel.hiddenHandoff (pc ∘ Fin.castSucc) loc inputs stackEnd
        (pc (Fin.last VertexLevel.hiddenCount)) i)
    (cacheRow : M.code (pc (Fin.last VertexLevel.hiddenCount)) = .copy (loc 8) (inputs 1) next)
    (apart : ∀ i j, inputs i ≠ loc j)
    (separate : ∀ i : Fin 9, i = 3 ∨ i = 5 ∨ i = 6 ∨ i = 7 →
      dfs i ≠ loc 8 ∧ ∀ j, dfs i ≠ inputs j)
    (start : ∀ node c, pre node c → c.pc = pc 0)
    (resume : ∀ node c d, pre node c →
      let G := c.privateMem (c.reg stackEnd)
      let n := c.privateMem (G + 9)
      d.pc = next → d.reg (inputs 0) = c.reg (loc 7) →
      d.reg (inputs 1) = VertexLevel.hiddenBaseWord (c.privateMem (G + 8)) n →
      d.reg (inputs 2) = n * n → d.reg (inputs 5) = c.reg (loc 11) →
      d.reg (loc 8) = d.reg (inputs 1) →
      (∀ j, j ≠ loc 8 → j ≠ inputs 0 → j ≠ inputs 1 → j ≠ inputs 2 → j ≠ inputs 5 →
        d.reg j = c.reg j) →
      d.privateMem = c.privateMem → d.persistent = c.persistent → post node d) :
    Realizes (Setup.ticks (endAddr := endAddr) (VertexLevel.hiddenCount + 1)).reader M m dfs
      pre (fun _ => post) := by
  apply Setup.realizes
  intro node c hc
  obtain ⟨d, run, done, owner, base, stride, level, cached, keep, mem, pers⟩ :=
    VertexLevel.cachedHiddenHandoff_run linked cacheRow apart c (start node c hc) m
  refine ⟨d, resume node c d hc done owner base stride level cached keep mem pers,
    ⟨?_, fun a _ => congrFun mem a, pers⟩, congrArg (DFS.scratch endAddr) mem, run⟩
  intro i hi
  obtain ⟨hloc, hinputs⟩ := separate i hi
  exact keep _ hloc (hinputs 0) (hinputs 1) (hinputs 2) (hinputs 5)

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
