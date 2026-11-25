import OAI.Hierarchy.GraphContractions

namespace OAI
/-! # A Boolean-witness polynomial for vertex-table contraction

Each edge has one Boolean variable per label. The selector for a label
tests its entire bit vector, so any edge without exactly one chosen label
makes its incident table factors vanish.
-/

namespace Hierarchy.IncidenceGraph

open MvPolynomial
noncomputable section
open scoped Classical

variable (G : IncidenceGraph) (F : Type*) [Field F] (q : ℕ)

abbrev Witness := G.E × Fin q

def labelFactor (e : G.E) (a i : Fin q) : MvPolynomial (G.TableVar q ⊕ G.Witness q) F :=
  if i=a then X (Sum.inr (e,i)) else 1-X (Sum.inr (e,i))

def labelSelector (e : G.E) (a : Fin q) : MvPolynomial (G.TableVar q ⊕ G.Witness q) F :=
  ∏ i, G.labelFactor F q e a i

def tableTerm (v : G.V) (t : G.Incident v → Fin q) :
    MvPolynomial (G.TableVar q ⊕ G.Witness q) F :=
  X (Sum.inl ⟨v,t⟩) * ∏ e : G.Incident v, G.labelSelector F q e.val (t e)

def tablePolynomial (v : G.V) : MvPolynomial (G.TableVar q ⊕ G.Witness q) F :=
  ∑ t, G.tableTerm F q v t

def witnessPolynomial : MvPolynomial (G.TableVar q ⊕ G.Witness q) F :=
  ∏ v, G.tablePolynomial F q v

end
end Hierarchy.IncidenceGraph

end OAI
