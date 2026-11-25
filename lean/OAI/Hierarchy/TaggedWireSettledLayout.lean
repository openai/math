import OAI.Hierarchy.TaggedWireRoleIndices
import OAI.Hierarchy.TaggedWireWalkOrientation

namespace OAI
/-! # Endpoint and occurrence indexing for each settled report -/

noncomputable section
namespace Hierarchy.WireTelescope.SettledMatrix
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor AdaptiveProbe
open scoped Classical BigOperators

variable {S r : ℕ} {I A : Type} [Fintype I] [Fintype A] {F : Type*} [Field F]

structure Layout (S r : ℕ) (I A : Type) where
  edge : Fin r→Chord S
  goods : PortGraph (Fin S) I
  reserve : PortGraph (Fin S) A
  goodsDistinct : ∀i,goods.tail i≠goods.head i
  reserveDistinct : ∀i,reserve.tail i≠reserve.head i
  core : I→List (Fin r)
  center : A→List (Fin r)
  corePath : ∀i,Traverses (rowGraph edge) (goods.tail i) (core i) (goods.head i)
  centerPath : ∀i,Traverses (rowGraph edge) (reserve.tail i) (center i) (reserve.head i)

namespace Layout
variable (B : Layout S r I A)

def available (fixed : Fin r→ℕ) (stock : I→ℕ) (reserved used : A→ℕ) : Source r I A→ℕ :=
  Sum.elim fixed (Sum.elim stock fun i=>reserved i-used i)

def original : Source r I A→Chord S :=
  Sum.elim B.edge (Sum.elim (fun i=>orderedChord _ _ (B.goodsDistinct i)) (fun i=>orderedChord _ _ (B.reserveDistinct i)))

def steps : Source r I A→List (Fin r) :=
  Sum.elim (fun i=>[i]) (Sum.elim (fun i=>oriented (B.goods.tail i) (B.goods.head i) (B.core i))
    (fun i=>oriented (B.reserve.tail i) (B.reserve.head i) (B.center i)))

omit [Fintype I] [Fintype A] in
theorem paths (i : Source r I A) : Traverses (rowGraph B.edge) (B.original i).1.1 (B.steps i) (B.original i).1.2 := by
  rcases i with i|i|i
  · exact .forward i (.nil _)
  · exact oriented_walk _ _ _ (B.goodsDistinct i) _ (B.corePath i)
  · exact oriented_walk _ _ _ (B.reserveDistinct i) _ (B.centerPath i)


def family := B.original ∘ numbered (r:=r) (I:=I) (A:=A)
def routes := B.steps ∘ numbered (r:=r) (I:=I) (A:=A)

def bits (fixed : Fin r→ℕ) (stock : I→ℕ) (reserved used : A→ℕ) :=
  available fixed stock reserved used ∘ numbered (r:=r) (I:=I) (A:=A)

end Layout
end Hierarchy.WireTelescope.SettledMatrix

end
end OAI
