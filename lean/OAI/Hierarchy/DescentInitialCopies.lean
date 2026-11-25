import OAI.Hierarchy.DescentInitialPackage
import OAI.Hierarchy.CatalystIndependentCopies

namespace OAI
/-! # The exact unstacked S-copy input tensor with physical hub labels -/

namespace Hierarchy.DescentInitialHost
open ThreeFlat Routing
open Catalyst CatalystSubstitution CorrectionBatch CorrectionFrame
open scoped Classical BigOperators
noncomputable section
variable {F : Type*} [Field F] {k p : ℕ}

/-- One internal state for each copied trivalent graph and one tether word per
copied exterior port. The complete coefficient identity holds before any
merging or layout choice, at the external coordinates of independentCopies. -/
theorem initialize_copies (s : ℕ) (X : Approximation F k p)
    (x : Port (s*p) (copiesWidth s X.width) → Bool) :
    let N := X.network.copyGraph
    let xrow := fun (i : Fin s) (j : Fin (Fintype.card (Port p X.width))) (_ : Fin 1) =>
      x (copiesPortEquiv (p:=p) s X.width (i,(Fintype.equivFin _).symm j))
    (independentCopies s X).coeff x =
      ∑ z : Fin s → (Fin (Fintype.card (Port p X.width)) → Fin 1→Bool) × N.Assignment,
        ∏ i, (∏ v,N.read X.network.copyTable (z i).2 (z i).1 v)*
          (∏ j,if (z i).1 j=xrow i j then 1 else 0) := by
  dsimp only
  rw [CatalystSubstitution.copies_coeff]
  let N := X.network.copyGraph
  let row (i : Fin s) (j : Fin (Fintype.card (Port p X.width))) (_ : Fin 1) :=
    x (copiesPortEquiv (p:=p) s X.width (i,(Fintype.equivFin _).symm j))
  let term (i : Fin s) (a : (Fin (Fintype.card (Port p X.width))→Fin 1→Bool)×N.Assignment) : F :=
    (∏v,N.read X.network.copyTable a.2 a.1 v)*(∏j,if a.1 j=row i j then 1 else 0)
  calc
    _ = ∏i,∑z,term i z := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Fintype.sum_prod_type]
      exact ((«initialize» X).2.2 (fun j => x (copiesPortEquiv (p:=p) s X.width (i,j)))).symm
    _ = _ := Fintype.prod_sum term

end
end Hierarchy.DescentInitialHost

end OAI
