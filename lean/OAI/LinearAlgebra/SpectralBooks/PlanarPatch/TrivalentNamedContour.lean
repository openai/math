import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.TrivalentContour
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.TrivalentStubNames
import Mathlib.Logic.Equiv.Fin.Rotate

/-! # Boundary names and numbered turns of a trivalent replacement

The names on the disk walk occur in the prescribed boundary order. Numbering
the slots as output, left, right identifies the disk's positive vertex rotation
with addition of one modulo three.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical
namespace PlanarPatch.TrivalentTree

variable {K V S : Type*} {d : V → ℕ} {q : ℕ} (t : TrivalentTree K d q)
    (h : [] ∈ t.branchAddresses)

/-- Reading the external stubs on the disk, in order, recovers their original names. -/
theorem diskWalk_namedStubs (out : V) (nd : (out :: t.labels).Nodup)
    (all : ∀ v, v ∈ out :: t.labels) :
    ((t.diskWalk h).filterMap t.readStub).map (t.stubNames out nd all) = out :: t.labels := by
  rw [diskWalk_stubs, List.map_cons, stubNames_output, List.map_map, List.cons.injEq]
  refine ⟨rfl, ?_⟩
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hi' : i < t.leafPaths.length := t.leafPaths_length ▸ hj
    let k : Fin t.leafPaths.length := ⟨i, hi'⟩
    have ht : t.leafPaths.attach[i]'(by simpa using hi') =
        (t.leafPaths_nodup.getEquiv t.leafPaths) k := by
      apply Subtype.ext
      simp [k]
    simp only [List.getElem_map, Function.comp_apply, ht, stubNames_input, leafName, leafSlot,
      Equiv.trans_apply, Equiv.symm_apply_apply]
    rfl

include h in
/-- The parent wire belongs to its nonroot child, and the root supplies the one extra role. -/
theorem card_internalWire_add_one : Fintype.card t.InternalWire + 1 = Fintype.card t.Role := by
  let r : t.Role := ⟨[],h⟩
  have hc := Fintype.card_congr (t.rootedTreeData h).edge
  have hn : Nonempty t.Role := ⟨r⟩
  have hp := Fintype.card_pos_iff.mpr hn
  change Fintype.card {v : t.Role // v ≠ r} = Fintype.card t.InternalWire at hc
  rw [Fintype.card_subtype_compl] at hc
  simp only [Fintype.card_unique] at hc
  omega

/-- Interpret an incident port carrying its original boundary name as an actual tree dart. -/
def namedDartEquiv (e : S ≃ t.Stub) (v : t.Role) :
    t.internalGraph.Port v ⊕ {s : S // t.attach h (e s) = v} ≃
      {a : t.TreeEnd // t.endOwner h a = v} :=
  (Equiv.sumCongr (Equiv.refl _) (e.subtypeEquiv (fun _ => Iff.rfl))).trans (t.openDartEquiv h v)

theorem namedSlotEquiv_apply (e : S ≃ t.Stub) (v : t.Role)
    (p : t.internalGraph.Port v ⊕ {s : S // t.attach h (e s) = v}) :
    t.namedSlotEquiv h e v p = slotOfPosition (t.endPosition h (t.namedDartEquiv h e v p).val) := rfl

private theorem slotOfPosition_positive (a : Option Bool) :
    slotOfPosition (positivePosition a) = finRotate 3 (slotOfPosition a) := by
  rcases a with _ | (_ | _) <;> decide

/-- The physical turn from a named port is the port with the next number in cyclic order. -/
theorem positiveTurn_namedSlot (e : S ≃ t.Stub) (v : t.Role) (i : Fin 3) :
    t.positiveTurn h ((t.namedDartEquiv h e v) ((t.namedSlotEquiv h e v).symm i)).val =
      ((t.namedDartEquiv h e v) ((t.namedSlotEquiv h e v).symm (finRotate 3 i))).val := by
  let a (j : Fin 3) := (t.namedDartEquiv h e v) ((t.namedSlotEquiv h e v).symm j)
  have hpos (j : Fin 3) : slotOfPosition (t.endPosition h (a j).val) = j :=
    (t.namedSlotEquiv h e v).apply_symm_apply j
  apply (t.treeEndEquiv h).injective
  change t.treeEndEquiv h ((t.positiveTurn h) (a i).val) = t.treeEndEquiv h (a (finRotate 3 i)).val
  simp only [positiveTurn, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.prodCongr_apply]
  apply Prod.ext
  · exact (a i).property.trans (a _).property.symm
  · apply slotOfPosition.injective
    change slotOfPosition (positivePosition (t.endPosition h (a i).val)) =
      slotOfPosition (t.endPosition h (a (finRotate 3 i)).val)
    rw [slotOfPosition_positive, hpos, hpos]

end PlanarPatch.TrivalentTree

end

end SpectralBooks
end LinearAlgebra
end OAI
