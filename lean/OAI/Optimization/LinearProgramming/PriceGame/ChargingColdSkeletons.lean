import OAI.Optimization.LinearProgramming.PriceGame.ChargingColdRanges
import OAI.Optimization.LinearProgramming.PriceGame.ChargingColdOrder
import OAI.Optimization.LinearProgramming.PriceGame.ControlScalarMachine
import OAI.Optimization.LinearProgramming.PriceGame.ControlEncodingPad

/-! # A uniform polynomial-bit machine for the complete cold-start skeleton roster -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Cold

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open States.Mass

theorem packShape_eq {N : ℕ} (s : Skeleton N) (raw : Fin N → ℚ) :
    packShape s = {packExpert ⟨s,raw⟩ with raw := []} := rfl

private theorem pivotWords_rows (N k : ℕ) (hk : k ≤ depth N) :
    pivotWords (rows N) k = (Skeleton.pivots N k).map (fun p =>
      p.map (fun v => (v.1.val,(vertexEquivFin N v.1.val v.2).val))) := by
  rw [pivots_addresses,pivotWords,rows,List.flatMap_map]
  apply congrArg (none :: ·)
  change (List.range (depth N)).flatMap (fun j => if j<k then (List.range (N*2^j)).map
    (fun i => some (j,i)) else []) = _
  rw [show (List.range (depth N)).flatMap (fun j => if j<k then (List.range (N*2^j)).map
      (fun i => some (j,i)) else []) = ((List.range (depth N)).filter (fun j => decide (j<k))).flatMap
      (fun j => (List.range (N*2^j)).map (fun i => some (j,i))) from by
    simpa only [decide_eq_true_eq] using flat_guard (List.range (depth N)) (fun j => decide (j<k))
      (fun j => (List.range (N*2^j)).map (fun i => some (j,i)))]
  rw [filter_range_lt,Nat.min_eq_right hk]

private theorem source_row (N : ℕ) (k : Fin (depth N)) :
    (([false,true] : List Bool).flatMap (fun h => (Skeleton.tuples (Skeleton.vertices N k) 64).flatMap
      (fun t => (Skeleton.pivots N k).map (fun p => (⟨k,h,t,p⟩ : Skeleton N))))).map packShape =
      rowExperts (rows N) (k.val,List.range (N*2^k.val)) := by
  have ht := tupleWords_eq_map (fun v : Vertex N k => (vertexEquivFin N k v).val) (Skeleton.vertices N k) 64
  rw [vertices_addresses] at ht
  rw [rowExperts]
  change _ = ([false,true] : List Bool).flatMap (fun h => (tupleWords 64 (List.range (N*2^k.val))).flatMap
    (fun t => (pivotWords (rows N) k.val).map fun p => (⟨k.val,h,t,p,[]⟩ : PackedExpert)))
  rw [← ht,pivotWords_rows N k k.isLt.le,List.map_flatMap]
  apply List.flatMap_congr
  intro h _
  rw [List.map_flatMap,List.flatMap_map]
  apply List.flatMap_congr
  intro t _
  rw [List.map_map,List.map_map]
  rfl

/-- Exactly the public skeleton order, before any raw-value representatives are attached. -/
def coldSkeletons (N : ℕ) : List PackedExpert := (Skeleton.enumerate N).map packShape

theorem coldSkeletons_eq_rows (N : ℕ) : coldSkeletons N = (rows N).flatMap (rowExperts (rows N)) := by
  rw [coldSkeletons,Skeleton.enumerate,List.map_flatMap]
  calc
    _ = (List.finRange (depth N)).flatMap (fun k => rowExperts (rows N) (k.val,List.range (N*2^k.val))) :=
      List.flatMap_congr fun k _ => source_row N k
    _ = (List.range (depth N)).flatMap (fun k => rowExperts (rows N) (k,List.range (N*2^k))) :=
      flatMap_finRange (depth N) (fun k : ℕ => rowExperts (rows N) (k,List.range (N*2^k)))
    _ = _ := by rw [rows,List.flatMap_map]

/-- One finite binary-stack program writes the entire roster from a unary `N`.
The polynomial clock includes constructing every tuple, pivot, bit and frame. -/
noncomputable def coldSkeletonsP : Procedure unaryCode (listCode Wire.packedExpertCode) coldSkeletons :=
  (allRowsP.comp (rowsFromRangeP Native.addressRangeP)).congrFun (fun N => (coldSkeletons_eq_rows N).symm)

/-- Extract the already materialized dimension from the real padded cold-start interface. -/
noncomputable def paddedColdSkeletonsP : Procedure eiPad (listCode Wire.packedExpertCode)
    (fun i => coldSkeletons i.goods) := by
  let take : Procedure eiPad unaryCode (fun i : PublicInput => i.goods) := unaryGoodsP.result fun _ => rfl
  exact coldSkeletonsP.comp take

/-- The step polynomial is fixed before the dimension and output are chosen. -/
theorem coldSkeletons_runs (N : ℕ) :
    ∃ c, c ≤ coldSkeletonsP.bound.eval N ∧
    @Runs coldSkeletonsP.K coldSkeletonsP.decideK coldSkeletonsP.program
      (@singletonStore coldSkeletonsP.K coldSkeletonsP.decideK coldSkeletonsP.input (unaryCode N))
      (@singletonStore coldSkeletonsP.K coldSkeletonsP.decideK coldSkeletonsP.output
        (listCode Wire.packedExpertCode (coldSkeletons N))) c := by
  simpa [unaryCode] using coldSkeletonsP.runs N

end Cold
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
