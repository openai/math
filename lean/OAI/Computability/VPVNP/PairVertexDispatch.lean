import OAI.Computability.VPVNP.PairVertexControl

/-! # The exact DFS hook of the assembled three-role image -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage

open BurstRAM PrivateRAM DFS
open scoped Fin.CommRing
open private returns_prefix from OAI.Computability.VPVNP.PairSimulationDFSDecode

variable {W endAddr p r : ℕ} {S : Part → Segment} {A : Placement S p r} {M : Machine W p r 11}

/-- Add the dispatcher's tag lookup to a role path on the scratch from
which it was selected. The role body still performs the scratch update. -/
def dispatchJob (m : Memory W) (offset node : Word W) (saved : Scratch W endAddr)
    (body : VisitPath W endAddr) : VisitPath W endAddr :=
  ⟨body.node, dispatchEvents m offset node ++ body.trace,
    fun old => old = saved ∧ body.enabled old, body.update⟩

/-- The enabling scratch fixes the stored geometry used by this call as
well as the role's own local argument precondition. -/
def dispatcher (handlers : NodeDispatch.Role → HookParser W endAddr) (m : Memory W)
    (offset : Word W) : HookParser W endAddr where
  read node saved bits :=
    let role := NodeDispatch.role (m (offset + node).val)
    ((handlers role).read node saved bits).map fun (job, tail) =>
      (dispatchJob m offset node saved job, tail)

/-- Compose a linked role path with the actual geometry and role-tag rows. -/
theorem dispatchJob_linked (linked : Contains A M) {G offset hist node : Word W} {m : Memory W}
    {saved : Scratch W endAddr} {role : NodeDispatch.Role} {body : VisitPath W endAddr}
    (resident : ResidentGeometry saved G offset hist)
    (tag : NodeDispatch.role (m (offset + node).val) = role)
    (nodeEq : body.node = node)
    (runBody : body.Linked M (A.entry (rolePart role)) (A.dfsPC 3) A.dfs m) :
    (dispatchJob m offset node saved body).Linked M (A.core (.roleBase 0)) (A.dfsPC 3) A.dfs m := by
  intro c top pending enabled hc hn hs hend ht he h1
  have original : scratch endAddr c.privateMem = saved := enabled.1
  rw [← original] at resident
  obtain ⟨mid, pc, mem, persist, frame, prefixRun⟩ :=
    dispatch_run linked G offset hist c hc h1 he resident m
  change c.reg (A.dfs 7) = body.node at hn
  rw [hn, nodeEq] at pc prefixRun
  rw [tag] at pc
  have reg (i : Fin 9) (hi : i ≠ 0) (hj : i ≠ 1) :=
    frame (A.dfs i) (A.dfs.injective.ne hi) (A.dfs.injective.ne hj)
  obtain ⟨out, hpc, nodeReg, topReg, endReg, unit, state, stack, scratchEq, run⟩ :=
    runBody mid top pending (mem ▸ enabled.2) pc ((reg 7 (by decide) (by decide)).trans hn)
      (mem ▸ hs) hend
      ((reg 5 (by decide) (by decide)).trans ht)
      ((reg 6 (by decide) (by decide)).trans he) ((reg 3 (by decide) (by decide)).trans h1)
  refine ⟨out, hpc, nodeReg, topReg, endReg, unit, state.trans persist, stack, mem ▸ scratchEq, ?_⟩
  intro fuel more
  change execute M.program (fuel + (dispatchEvents m offset node ++ body.trace).length) c m
    (choiceBits (dispatchEvents m offset node ++ body.trace) ++ more) = _
  rw [PrimedInputRAM.Flow.choiceBits_append,
        (dispatchEvents_cost m offset node).2.2,
    List.nil_append,
    List.length_append, show fuel + ((dispatchEvents m offset node).length + body.trace.length) =
      (fuel + body.trace.length) + (dispatchEvents m offset node).length by omega, prefixRun, run]
  simp only [dispatchJob, Option.map_map, Function.comp_def, List.append_assoc]

/-- The private geometry and the external role tag are read again on
every visit. Both success and rejection hold for arbitrary unused
registers and for every stream suffix. -/
theorem dispatch_exactOn (linked : Contains A M) (G offset hist : Word W) (m : Memory W)
    (domain : Word W → Scratch W endAddr → Prop)
    (geometry : ∀ node saved, domain node saved → ResidentGeometry saved G offset hist)
    (handlers : NodeDispatch.Role → HookParser W endAddr)
    (exactRole : ∀ role, (handlers role).ExactOn
      (fun node saved => domain node saved ∧ NodeDispatch.role (m (offset + node).val) = role)
      M (A.entry (rolePart role)) (A.dfsPC 3) A.dfs m) :
    (dispatcher handlers m offset).ExactOn domain M (A.core (.roleBase 0)) (A.dfsPC 3) A.dfs m := by
  constructor
  · intro node saved hd bits job tail hit
    let role := NodeDispatch.role (m (offset + node).val)
    obtain ⟨⟨body, rest⟩, read, eqn⟩ := Option.map_eq_some_iff.mp hit
    cases eqn
    obtain ⟨nodeEq, en, word, runBody⟩ :=
      (exactRole role).success node saved ⟨hd, rfl⟩ bits body tail read
    refine ⟨nodeEq, ⟨rfl, en⟩, ?_, ?_⟩
    · simpa only [dispatchJob, PrimedInputRAM.Flow.choiceBits_append,
        (dispatchEvents_cost m offset node).2.2,
        List.nil_append] using word
    · exact dispatchJob_linked linked (geometry node saved hd) rfl nodeEq runBody
  · intro node bits c top pending hd hc hn hs hend ht he h1 fail
    let role := NodeDispatch.role (m (offset + node).val)
    have read : (handlers role).read node (scratch endAddr c.privateMem) bits = none :=
      Option.map_eq_none_iff.mp fail
    obtain ⟨mid, pc, mem, _, frame, run⟩ :=
      dispatch_run linked G offset hist c hc h1 he (geometry _ _ hd) m
    rw [hn] at pc run
    have reg (i : Fin 9) (hi : i ≠ 0) (hj : i ≠ 1) :=
      frame (A.dfs i) (A.dfs.injective.ne hi) (A.dfs.injective.ne hj)
    have reject := (exactRole role).reject node bits mid top pending ⟨mem ▸ hd, rfl⟩ pc
      ((reg 7 (by decide) (by decide)).trans hn) (mem ▸ hs) hend
      ((reg 5 (by decide) (by decide)).trans ht)
      ((reg 6 (by decide) (by decide)).trans he) ((reg 3 (by decide) (by decide)).trans h1)
      (mem ▸ read)
    exact fun ok => reject ((returns_prefix (fun fuel => run fuel bits)).mp ok)

/-- Removing the recorded private geometry ticks and tag probe from a
successful dispatch leaves exactly the selected native handler's suffix. -/
theorem dispatcher_suffix (handlers : NodeDispatch.Role → HookParser W endAddr) (m : Memory W)
    (offset node : Word W) (saved : Scratch W endAddr) (bits : List Bool) :
    ((dispatcher handlers m offset).read node saved bits).map Prod.snd =
      ((handlers (NodeDispatch.role (m (offset + node).val))).read node saved bits).map
        Prod.snd := by
  simp [dispatcher, Option.map_map, Function.comp_def]

end PairSimulation.VertexImage

end VPVNP
end Computability
end OAI
