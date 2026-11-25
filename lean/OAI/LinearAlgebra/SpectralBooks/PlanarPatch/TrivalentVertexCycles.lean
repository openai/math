import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.TrivalentNamedContour
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarAssemblyIncidence

/-! # Vertex cycles and internal darts of a trivalent replacement tree -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical
open Equiv Equiv.Perm HyperbolicObstruction.PictureSwitch
namespace PlanarPatch.TrivalentTree

variable {K V : Type*} {d : V → ℕ} {q : ℕ} (t : TrivalentTree K d q)

private theorem positivePosition_sameCycle (x y : Option Bool) :
    positivePosition.SameCycle x y := by
  rcases x with _ | (_ | _) <;> rcases y with _ | (_ | _) <;>
    first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩

/-- The three positions at a branch form exactly one vertex cycle. -/
theorem cycles_positiveTurn (h : [] ∈ t.branchAddresses) :
    cycles (t.positiveTurn h) = Fintype.card t.Role := by
  let e := (t.treeEndEquiv h).trans (sigmaEquivProd t.Role (Option Bool)).symm
  have turn (a : t.TreeEnd) :
      e (t.positiveTurn h a) = Equiv.sigmaCongrRight (fun _ : t.Role => positivePosition) (e a) := by
    simp only [e, positiveTurn, Equiv.trans_apply, Equiv.apply_symm_apply]
    rfl
  apply cycles_of_classifier _ (fun a => (e a).1)
    (PortGraph.StubPairing.sameCycle_iff_piece e _ _ turn (fun _ => positivePosition_sameCycle))
  exact fun v => ⟨e.symm ⟨v,none⟩, congrArg Sigma.fst (e.apply_symm_apply _)⟩

/-- Each internal wire contributes both its darts to the support; every stub is fixed. -/
theorem internalPairing_support_card :
    t.internalPairing.support.card = 2 * Fintype.card t.InternalWire := by
  have hs : t.internalPairing.support =
      Finset.univ.map (Function.Embedding.inl : t.InternalWire × Bool ↪ t.TreeEnd) := by
    ext e
    rcases e with ⟨w, _ | _⟩ | s <;> simp [internalPairing, mem_support, Finset.mem_map]
  rw [hs, Finset.card_map, Finset.card_univ, Fintype.card_prod, Fintype.card_bool, Nat.mul_comm]

end PlanarPatch.TrivalentTree

end

end SpectralBooks
end LinearAlgebra
end OAI
