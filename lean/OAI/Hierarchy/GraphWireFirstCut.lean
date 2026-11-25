import OAI.Hierarchy.GraphWireCoefficients
import OAI.Hierarchy.GraphWireClass
import OAI.Hierarchy.ABPFirstCutBorder

namespace OAI
/-! # First-cut rank decompositions of graph equality wires -/

namespace Hierarchy.IncidenceGraph

open ABPFirstCut Computability.BorderVNP
open scoped BigOperators Classical

/-- A degree-component border ABP for a graph contraction gives a border sum of
its physical equality wires. For each allowed vertex cut the corresponding
summand has rank at most the size bound across the legs owned by that cut. -/
theorem border_abp_wire_cut_sums (G : IncidenceGraph) [DecidableEq G.V] [DecidableEq G.E]
    (F : Type*) [Field F] {q s : ℕ} (family : Finset (Finset G.V))
    (hempty : ∅ ∉ family) (hcover : HitsEveryOrder family)
    (h : DegreeBorderAtMost HasABP (Fintype.card G.V) s (G.contraction F q)) :
    (equalityWireRaw G.E (AlgebraicClosure F) q).coeff ∈
      imageClosure (rankSumsOn (fun U : family => legsOfCut G.portOwner U.val) s) := by
  have withFormat (I : Fintype (G.TableVar q)) :
      DegreeBorderAtMost (@HasABP (AlgebraicClosure F) (G.TableVar q) _ I)
        (Fintype.card G.V) s (G.contraction F q) := by
    rw [Subsingleton.elim I (G.tableVarFintype q)]
    exact h
  have hc := border_abp_first_cut_on_legs (ν := fun _ : G.E × Bool => Fin q)
    (τ := fun v : G.V => G.Incident v → Fin q) (f := G.contraction F q) (s := s)
    G.portOwner (G.portAssemble (q := q)) family hempty hcover (withFormat _)
  have heq : (fun x => slotCoeff (slotRead G.portOwner (G.portAssemble (q := q)) x) Finset.univ
      (MvPolynomial.map (algebraMap F (AlgebraicClosure F)) (G.contraction F q))) =
      (equalityWireRaw G.E (AlgebraicClosure F) q).coeff := by
    funext x
    exact G.map_slotCoeff_portAssignment (algebraMap F (AlgebraicClosure F)) x
  exact heq ▸ hc


end Hierarchy.IncidenceGraph

end OAI
