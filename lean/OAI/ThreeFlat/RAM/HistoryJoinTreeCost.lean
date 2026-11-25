import OAI.ThreeFlat.Diagonal.HistoryStageCharges

namespace OAI
/-! # Charging the command and pin words of an ordered history join to its compiled tree -/

namespace ThreeFlat.RAM.HistoryMotifJoin

open Diagonal.HistoryContraction
open scoped BigOperators Classical

/-- The pin words and copied rows in a real ordered glue are charged to the
corresponding tree at that same site. -/
theorem join_tree_words {F : Type*} {n h p : ℕ} {arity : Fin n→ℕ}
    (N : ∀ i,Tree F (arity i)) (wire : ∀ i,Fin (arity i)→BitSource h p) :
    ((List.finRange n).map (fun i=>arity i+4*(N i).compile.cells)).sum≤
      4*(Tree.join h n arity wire N).resources := by
  rw [←Fin.sum_univ_def]
  simp only [Tree.compiled_rows,Finset.sum_add_distrib,←Finset.mul_sum]
  change (∑ i,arity i)+4*(∑ i,(N i).rows)≤4*(
    (Tree.join h n arity wire N).bits+(∑ i,(N i).rows)+(Tree.join h n arity wire N).nodes+
      ((∑ i,(N i).footprint.pins)+(∑ i,arity i)))
  omega

/-- Each child has two command fields in addition to its actual pin and cell data. -/
theorem join_tree_units {F : Type*} {n h p cap : ℕ} {arity : Fin n → ℕ}
    (N : ∀ i, Tree F (arity i)) (wire : ∀ i, Fin (arity i) → BitSource h p) (bound : n ≤ cap) :
    1+n+n+((List.finRange n).map (fun i => arity i+4*(N i).compile.cells)).sum ≤
      (5+2*cap)*(1+(Tree.join h n arity wire N).resources) := by
  have words := join_tree_words N wire
  rw [Nat.mul_add,Nat.mul_one,Nat.add_mul]
  omega

end ThreeFlat.RAM.HistoryMotifJoin

end OAI
