import OAI.Optimization.LinearProgramming.PriceGame.Skeletons
import OAI.Optimization.LinearProgramming.PriceGame.VertexEncoding

/-! # Source enumeration order and binary vertex addresses -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Cold

open States.Mass

theorem finRange_values (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i h h'; simp

theorem flatMap_finRange {A : Type} (n : ℕ) (f : ℕ → List A) :
    (List.finRange n).flatMap (fun i => f i.val) = (List.range n).flatMap f := by
  rw [← finRange_values n,List.flatMap_map]

private theorem double_range (n : ℕ) :
    (List.range n).flatMap (fun i => [2*i,2*i+1]) = List.range (2*n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ,List.flatMap_append,ih,show 2*(n+1) = (2*n+1)+1 by omega]
    rw [List.range_succ,List.range_succ (n := 2*n)]
    simp

/-- Nested pairs in the textual enumeration give increasing numerical addresses,
including the false-before-true order at each duplicated vertex. -/
theorem vertices_addresses (N k : ℕ) :
    (Skeleton.vertices N k).map (fun v => (vertexEquivFin N k v).val) = List.range (N*2^k) := by
  induction k with
  | zero =>
    simpa only [pow_zero,Nat.mul_one] using! finRange_values N
  | succ k ih =>
    let address (v : Vertex N k) := (vertexEquivFin N k v).val
    have hfalse (v : Vertex N k) : (vertexEquivFin N (k+1) (v,false)).val = 2*address v := by
      change 0+2*address v = 2*address v; omega
    have htrue (v : Vertex N k) : (vertexEquivFin N (k+1) (v,true)).val = 2*address v+1 := by
      change 1+2*address v = 2*address v+1; omega
    rw [Skeleton.vertices,List.map_flatMap]
    calc
      _ = ((Skeleton.vertices N k).map address).flatMap (fun i => [2*i,2*i+1]) := by
        rw [List.flatMap_map]
        apply List.flatMap_congr
        intro v _
        change [(vertexEquivFin N (k+1) (v,false)).val, (vertexEquivFin N (k+1) (v,true)).val] = [2*address v,2*address v+1]
        rw [hfalse,htrue]
      _ = List.range (2*(N*2^k)) := by rw [show (Skeleton.vertices N k).map address = _ from ih,double_range]
      _ = _ := by congr 1; ring

/-- The source pivot list uses ascending prior levels and ascending addresses
within each one. The inherited descriptor is always first. -/
theorem pivots_addresses (N k : ℕ) :
    (Skeleton.pivots N k).map (fun p => p.map (fun v => (v.1.val,(vertexEquivFin N v.1.val v.2).val))) =
    none :: (List.range k).flatMap (fun j => (List.range (N*2^j)).map (fun i => some (j,i))) := by
  rw [Skeleton.pivots,List.map_cons,List.map_flatMap,← flatMap_finRange]
  congr 1
  apply List.flatMap_congr
  intro j _
  rw [← vertices_addresses N j,List.map_map,List.map_map]
  rfl

end Cold
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
