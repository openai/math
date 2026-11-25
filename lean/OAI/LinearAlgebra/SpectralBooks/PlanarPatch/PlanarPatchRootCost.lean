import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchPruneCost
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchTreeRoot

/-! # Arithmetic input cost and height of a rooted triangulation

A boundary side multiplies one scalar edge check by one corner entry. A triangle
uses that scalar check whenever its three endpoint pairs agree, and zero otherwise.
The number of polygon sides bounds the height after adding the closing root.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

namespace PlanarPatch

variable {F I V : Type*} [Field F] {d : V → ℕ}

namespace CornerTable

/-- Each corner entry is given by an arithmetic formula of weight at most `C`. -/
def FormulaBound {A : Type*} (C : ℕ) : CornerTable (MvPolynomial I F) d A → Prop
  | .scalar f => ∀ a, HasFormula C (f a)
  | .stub _ f => ∀ a c, HasFormula C (f a c)

theorem sideTree_formulaBound {A B : Type*} [Fintype A] [Fintype B] {C : ℕ}
    (U : CornerTable (MvPolynomial I F) d A) (E : A → B → MvPolynomial I F)
    (hU : U.FormulaBound C) (hE : ∀ a b, HasFormula 1 (E a b)) :
    (U.sideTree E).FormulaBound (C+1) := by
  cases U with
  | scalar f =>
    intro k
    exact ((hE _ _).mul (hU _)).mono (by omega)
  | stub v f =>
    intro k c
    exact ((hE _ _).mul (hU _ c)).mono (by omega)

end CornerTable

namespace Triangulation

variable {lo hi q C : ℕ} (T : Triangulation lo hi) (S : ℕ → Type*) [∀ i, Fintype (S i)]

theorem orderedTree_height_lt {K : Type*} [CommSemiring K] (U : ∀ i, CornerTable K d (S i))
    (E : ∀ i j, S i → S j → K) : (T.orderedTree S U E).height < hi-lo := by
  induction T with
  | side i =>
    cases h : U i <;> simp [orderedTree, h, CornerTable.sideTree, OrderedTensorTree.height]
  | split hl hr L R il ir =>
    simp only [orderedTree, OrderedTensorTree.height]
    omega

theorem rootedTree_height_le {K : Type*} [CommSemiring K] (U : ∀ i, CornerTable K d (S i))
    (E : ∀ i j, S i → S j → K) (A : Fin q → S hi → K) :
    (T.rootedTree S U E A).height ≤ hi-lo :=
  T.orderedTree_height_lt S U E

variable (U : ∀ i, CornerTable (MvPolynomial I F) d (S i))
    (E : ∀ i j, S i → S j → MvPolynomial I F)

theorem orderedTree_formulaBound
    (hU : ∀ i, lo ≤ i → i < hi → (U i).FormulaBound C)
    (hE : ∀ i j, (i,j) ∈ T.edges → ∀ a b, HasFormula 1 (E i j a b)) :
    (T.orderedTree S U E).FormulaBound (C+1) := by
  induction T with
  | side i =>
    exact (U i).sideTree_formulaBound _ (hU i le_rfl (by omega)) (hE i (i+1) (root_mem _))
  | @split i m j hl hr L R il ir =>
    refine ⟨?_, il (fun a ha hb ↦ hU a ha (hb.trans hr)) ?_,
      ir (fun a ha hb ↦ hU a (hl.le.trans ha) hb) ?_⟩
    · intro a b c
      unfold pairingTable triangleTable
      split
      · exact (hE i j (root_mem _) _ _).mono (by omega)
      · simpa using (HasFormula.const (I := I) (0 : F)).mono (Nat.succ_le_succ (Nat.zero_le C))
    · exact fun a b he ↦ hE a b (split_hasEdge.mpr (Or.inr (Or.inl he)))
    · exact fun a b he ↦ hE a b (split_hasEdge.mpr (Or.inr (Or.inr he)))

theorem rootedTree_formulaBound (A : Fin q → S hi → MvPolynomial I F)
    (hU : ∀ i, lo ≤ i → i < hi → (U i).FormulaBound C)
    (hE : ∀ i j, (i,j) ∈ T.edges → ∀ a b, HasFormula 1 (E i j a b))
    (hA : ∀ o a, HasFormula C (A o a)) : (T.rootedTree S U E A).FormulaBound (C+1) :=
  ⟨fun o k ↦ (hA o (statePair (S lo) (S hi) k).2).mono (Nat.le_succ _), T.orderedTree_formulaBound S U E hU hE⟩

end Triangulation
end PlanarPatch

end

end SpectralBooks
end LinearAlgebra
end OAI
