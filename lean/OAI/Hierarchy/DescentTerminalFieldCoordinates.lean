import OAI.Hierarchy.DescentTerminalFieldSize
import OAI.Hierarchy.DescentTerminalPrintedFields

namespace OAI
/-! # Digits and their order in a printed terminal field record -/
namespace Hierarchy.DescentTerminalLeafDigits
open DescentTerminalPrintedFields
noncomputable section
variable {q t V H N A w : ℕ}

def digit (f : Fields q t H N A w V) : (i : Coord V H N A)→Fin (radix q t V H N A w i)
  | .inl _=>f.count
  | .inr (.inl i)=>(f.sizes i).1
  | .inr (.inr (.inl i))=>(f.sizes i).2
  | .inr (.inr (.inr (.inl z)))=>f.width z.1 z.2
  | .inr (.inr (.inr (.inr (.inl z))))=>f.role z.1 z.2
  | .inr (.inr (.inr (.inr (.inr (.inl z)))))=>f.arity z.1 z.2
  | .inr (.inr (.inr (.inr (.inr (.inr z)))))=>f.operand z.1 z.2.1 z.2.2

private def addEquiv {a b : ℕ} {X Y : Type} (x : X≃Fin a) (y : Y≃Fin b) :
    (X⊕Y)≃Fin (a+b) := (Equiv.sumCongr x y).trans finSumFinEquiv
private def mulEquiv {a b : ℕ} {X Y : Type} (x : X≃Fin a) (y : Y≃Fin b) :
    (X×Y)≃Fin (a*b) := (Equiv.prodCongr x y).trans finProdFinEquiv

def fieldsOrder (V H N A : ℕ) : Coord V H N A≃Fin (1+(V+(V+(V*H+(V*N+(V*N+V*(N*A))))))) :=
  addEquiv (Equiv.ofUnique Unit (Fin 1)) (addEquiv (Equiv.refl _) (addEquiv (Equiv.refl _)
    (addEquiv (mulEquiv (Equiv.refl _) (Equiv.refl _)) (addEquiv (mulEquiv (Equiv.refl _) (Equiv.refl _))
    (addEquiv (mulEquiv (Equiv.refl _) (Equiv.refl _)) (mulEquiv (Equiv.refl _) (mulEquiv (Equiv.refl _) (Equiv.refl _))))))))

end
end Hierarchy.DescentTerminalLeafDigits

end OAI
