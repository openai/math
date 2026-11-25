import OAI.Hierarchy.DescentOrdinaryNodeOrder
import OAI.Hierarchy.DescentSeedRootRows
import OAI.Hierarchy.DescentBoundedWorldHistory

namespace OAI
/-! # Immutable public seed-table row of every actual original coefficient node -/

namespace Hierarchy.DescentKernelHistory.NodeOrder
open Computability.BorderVNP.Crossing Catalyst CorrectionBatch DescentInitialHost DescentSeedRoot
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {k n : ℕ} (X : Approximation F k n) (R s : ℕ)
variable (c : (initialGroup X R s).Choice)
local notation "B" => BitDescription.initial X R s c

private def atSeed (j : Fin R) : (v : Vertex X) → ((B).recipe ⟨j,v⟩).Node
  | .inl _=>()
  | .inr _=>()

def seedSites : All B ≃ Fin R × Vertex X where
  toFun a:=⟨a.1.1,a.1.2⟩
  invFun x:=⟨⟨x.1,x.2⟩,atSeed X R s c x.1 x.2⟩
  left_inv := by
    rintro ⟨⟨j,v|v⟩,a⟩ <;> cases a <;> rfl
  right_inv := by rintro ⟨j,v⟩; rfl

def seedOrdinal : All B ≃ Fin (R*Fintype.card (Vertex X)) :=
  (seedSites X R s c).trans ((Equiv.prodCongr (Equiv.refl _) (Fintype.equivFin (Vertex X))).trans finProdFinEquiv)

/-- This is the very number in the startup vertex record before any profile choice. -/
theorem seedOrdinal_val (a : All B) :
    (seedOrdinal X R s c a).val=vertexID X a.1.1 a.1.2 := by
  rcases a with ⟨⟨j,v⟩,b⟩
  change index v + Fintype.card (Vertex X) * j.val = j.val * Fintype.card (Vertex X) + index v
  ac_rfl

end
end Hierarchy.DescentKernelHistory.NodeOrder

end OAI
