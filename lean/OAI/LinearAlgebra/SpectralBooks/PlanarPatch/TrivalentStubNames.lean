import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.TrivalentOpenShape
import Mathlib.Data.List.NodupEquivFin

/-! # Retaining the original boundary names in the tree replacement -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace PlanarPatch.TrivalentTree

open PortGraph
open scoped Classical

variable {K V S : Type*} {d : V → ℕ} {q : ℕ}

/-- Number input leaves in the order in which pruning retained the boundary labels. -/
def leafSlot (t : TrivalentTree K d q) : t.Leaf ≃ Fin t.labels.length :=
  ((t.leafPaths_nodup).getEquiv t.leafPaths).symm.trans (finCongr t.leafPaths_length)

/-- Output first, followed by the left to right leaf slots. -/
def stubSlot (t : TrivalentTree K d q) : t.Stub ≃ Fin (t.labels.length+1) where
  toFun := Option.elim' 0 (fun p => (t.leafSlot p).succ)
  invFun := Fin.cases none (some ∘ t.leafSlot.symm)
  left_inv := by rintro (_ | p) <;> simp [Option.elim', Function.comp_def]
  right_inv := by intro i; induction i using Fin.cases <;> simp [Option.elim', Function.comp_def]

/-- The original name at an input leaf occurrence. -/
def leafName (t : TrivalentTree K d q) (p : t.Leaf) : V := t.labels.get (t.leafSlot p)

/-- The stub names are a bijection when the distinguished output followed by
the retained leaf list visits all original stubs exactly once. -/
def stubNames (t : TrivalentTree K d q) (out : V) (nd : (out :: t.labels).Nodup)
    (all : ∀ v, v ∈ out :: t.labels) : t.Stub ≃ V :=
  (t.stubSlot).trans (nd.getEquivOfForallMemList _ all)

@[simp] theorem stubNames_output (t : TrivalentTree K d q) (out : V)
    (nd : (out :: t.labels).Nodup) (all : ∀ v, v ∈ out :: t.labels) :
    t.stubNames out nd all none = out := rfl

@[simp] theorem stubNames_input (t : TrivalentTree K d q) (out : V)
    (nd : (out :: t.labels).Nodup) (all : ∀ v, v ∈ out :: t.labels) (p : t.Leaf) :
    t.stubNames out nd all (some p) = t.leafName p := rfl

/-- Renaming the boundary does not change the internal graph. Stub direction
data are those of the original patch, even when they disagree with the
output/input convention for tensor evaluation. -/
def templateAt {S : Type} (t : TrivalentTree K d q) (h : [] ∈ t.branchAddresses)
    (e : S ≃ t.Stub) (dir : S → Bool) : ReplacementTemplate.{0,0,0} where
  Role := t.Role
  Wire := t.InternalWire
  Stub := S
  graph := t.internalGraph
  root := ⟨[],h⟩
  tree := t.rootedTreeData h
  attach := t.attach h ∘ e
  direction := dir

/-- Renaming an attached stub induces a bijection on the three ports of each
role, preserving its prescribed slot number. -/
def namedSlotEquiv (t : TrivalentTree K d q) (h : [] ∈ t.branchAddresses)
    (e : S ≃ t.Stub) (v : t.Role) :
    t.internalGraph.Port v ⊕ {s : S // t.attach h (e s) = v} ≃ Fin 3 :=
  (Equiv.sumCongr (Equiv.refl _) (e.subtypeEquiv (fun _ => Iff.rfl))).trans (t.openSlotEquiv h v)

end PlanarPatch.TrivalentTree

end

end SpectralBooks
end LinearAlgebra
end OAI
