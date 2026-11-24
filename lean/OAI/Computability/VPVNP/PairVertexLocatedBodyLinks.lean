import OAI.Computability.VPVNP.PairVertexLocatedBody

/-!
# The actual PC and register placements of a selected nonleaf stage
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocatedBody

open BurstRAM BurstRAM.PrivateRAM VertexImage VertexStageDispatch

variable {N p r w : ℕ} (B : Fin N → LocatedBody)

/-- Map the instructions of one scheduled body into the normalized family dispatch layout. -/
noncomputable abbrev stagePC (pc : Fin (family B).count → Fin p) (i : Fin N) :=
  bodyPC (fun i => (B i).normalized) (familyPC (fun i => (B i).normalized) pc) i

/-- Embed a selected body's original register bank using its locator-first ordering and its own
tail register block. -/
noncomputable abbrev stageBank (reg : Fin (family B).privateRegs ↪ Fin r) (i : Fin N) :
    Fin (B i).code.privateRegs ↪ Fin r :=
  (B i).order.symm.toEmbedding.trans ((bodyBank (fun i => (B i).normalized)
    (fun i => (B i).tailCount) (fun _ => rfl) i).trans reg)

/-- Place the single locator bank shared by all normalized stage bodies in the enclosing
machine. -/
noncomputable abbrev commonLocator (reg : Fin (family B).privateRegs ↪ Fin r) :=
  (locatorBank (fun i => (B i).tailCount)).trans reg

/-- Each stage, in its own original register order, reads the same locator registers
written by the header scan. No register copies or extra labels are required. -/
theorem shared_locator (reg : Fin (family B).privateRegs ↪ Fin r) (i : Fin N) (j : Fin 14) :
    stageBank B reg i ((B i).locator j) = commonLocator B reg j := by
  change reg (bodyBank (fun l => (B l).normalized) (fun l => (B l).tailCount) (fun _ => rfl) i
    ((B i).order.symm ((B i).locator j))) = reg (locatorBank (fun l => (B l).tailCount) j)
  rw [← order_locator (B i) j, Equiv.symm_apply_apply]
  apply congrArg reg
  exact bodyBank_locator (fun i => (B i).normalized) (fun i => (B i).tailCount) (fun _ => rfl) i j

/-- The source stage sees its original numerical code and the relocated source registers. -/
theorem stage_rows (M : Machine w p r 11) (pc : Fin (family B).count → Fin p)
    (dfs : Fin 9 ↪ Fin r) (saved : Saved ↪ Fin r) (reg : Fin (family B).privateRegs ↪ Fin r)
    (done : Fin p) (rows : ∀ a, M.code (pc a) = ((family B).row pc dfs saved reg done a).resize w)
    (i : Fin N) (j : Fin (B i).code.count) :
    M.code (stagePC B pc i j) =
      ((B i).code.row (stagePC B pc i) dfs saved (stageBank B reg i) done j).resize w :=
  (locatedFamily_link (fun i => (B i).normalized) dfs saved done M (fun i => (B i).tailCount)
    (fun _ => rfl) pc reg rows).2.2 i j

end PairSimulation.LocatedBody

end VPVNP
end Computability
end OAI
