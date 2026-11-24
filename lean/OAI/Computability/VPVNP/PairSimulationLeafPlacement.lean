import OAI.Computability.VPVNP.PairSimulationLeafGeometryLoad
import OAI.Computability.VPVNP.PairVertexImage

/-! # Allocating the leaf role inside the final vertex instruction image -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafRole

open BurstRAM PrivateRAM LeafRegisterBank

set_option synthInstance.maxSize 10000

/-- Labels of the cursor-leaf segment, covering both the private geometry loader and the
verifier body. -/
abbrev Label := LeafGeometryLoad.Label ⊕ LeafImage.Label

/-- Only the nine common DFS registers are external to this allocation. -/
inductive Private where
  | cursor
  | operand (i : Source 6)
  | address (i : {j : LeafAddress.Reg // j ≠ .node})
  | route (i : Fin 32)
  | boot (i : LeafBoot.Reg)

noncomputable instance : Fintype Private := by classical exact derive_fintype% _

/-- Number of instruction rows reserved for the leaf geometry loader and verifier body
together. -/
noncomputable def labelCount := Fintype.card Label
/-- Number of leaf-local register names to reserve in the enclosing vertex image. -/
noncomputable def privateCount := Fintype.card Private

/-- Number the loader and body labels for placement in the leaf segment of the vertex
instruction table. -/
noncomputable def labelIndex : Label ≃ Fin labelCount := Fintype.equivFin _
/-- Number the leaf-local registers for allocation in the vertex's register bank. -/
noncomputable def privateIndex : Private ≃ Fin privateCount := Fintype.equivFin _

variable {p r : ℕ}
variable (pc : Label → Fin p) (dfs : Fin 9 ↪ Fin r) (priv : Private ↪ Fin r)

/-- Every shared DFS register has a physical index distinct from every leaf-local register. -/
def Apart := ∀ i j, dfs i ≠ priv j

/-- Assign a leaf body register to the shared DFS bank or to the private address, routing or
startup bank according to its name. -/
def place : LeafImage.Reg → Fin r
  | .dfs i => dfs i
  | .address i => priv (.address i)
  | .route i => priv (.route i)
  | .boot i => priv (.boot i)

private theorem place_injective (apart : Apart dfs priv) : Function.Injective (place dfs priv) := by
  intro i j h
  cases i <;> cases j <;> simp only [place,dfs.injective.eq_iff,priv.injective.eq_iff] at h
  all_goals first | contradiction | cases h; rfl | exact (apart _ _ h).elim | exact (apart _ _ h.symm).elim

/-- The injective placement of all verifier body registers, using disjoint DFS and leaf-local
register banks. -/
def bodyReg (apart : Apart dfs priv) : LeafImage.Reg ↪ Fin r := ⟨place dfs priv,place_injective dfs priv apart⟩

/-- Embed the geometry loader's source registers in the leaf-local operand bank. -/
def ports : Source 6 ↪ Fin r := ⟨fun i => priv (.operand i),fun _ _ h => Private.operand.inj (priv.injective h)⟩

/-- The ten physical registers receiving the geometry words used as operands by the verifier
body. -/
def values := LeafGeometryLoad.bank (ports priv)

/-- Place a private geometry-load instruction at its label in the combined leaf segment. -/
def loadPC := pc ∘ Sum.inl
/-- Place a verifier body instruction at its label in the combined leaf segment. -/
def bodyPC := pc ∘ Sum.inr

theorem dfs_body (apart : Apart dfs priv) : LeafImage.dfsReg (bodyReg dfs priv apart) = dfs := rfl

theorem value_outside (apart : Apart dfs priv) (i : Fin 10) : values priv i ∉ Set.range (bodyReg dfs priv apart) := by
  rintro ⟨j,h⟩
  cases j with
  | dfs j => exact apart j _ h
  | address j | route j | boot j =>
    have e := priv.injective h
    cases e

end PairSimulation.LeafRole

end VPVNP
end Computability
end OAI
