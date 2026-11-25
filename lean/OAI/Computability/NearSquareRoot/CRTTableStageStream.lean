import OAI.Computability.NearSquareRoot.CRTTableStageHeader
import OAI.Computability.NearSquareRoot.CRTTablePackedSchedule
import OAI.Computability.IntegerMultiplication.Carry.Small

/-! # Uniform generation of the full ordered stream of CRT stage headers -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable
open IntegerMultiplication IntegerMultiplication.Code

private def unaryDepths (q : Bool × List ControlAxis) : List Tally :=
  let levels := Iter.lineup (Carry.light (Carry.born q.2.length))
  bif q.1 then levels else levels.reverse

private theorem unaryDepths_poly : Poly unaryDepths := by
  let X := Bool × List ControlAxis
  have bin := (Easy.ruler (Easy.snd (X := Bool) (Y := List ControlAxis))).compose Carry.easy_chart
  have count : Poly (fun q : X => Carry.born q.2.length) := by simpa using bin.poly
  have levels := (count.compose Carry.lightPoly).compose Iter.poly_line
  exact Poly.choose Easy.fst.poly levels levels.rev

private def localOrder (t : Tally) : List (Bool × Tally) :=
  (Iter.lineup t).map (fun j => (false,j)) ++ (Iter.lineup t).reverse.map (fun j => (true,j))

private theorem localOrder_poly : Poly localOrder := by
  exact (Iter.poly_line.compose (Poly.maps _ (show Poly (fun j : Tally => (false,j)) by fun_prop))).app
    (Iter.poly_line.rev.compose (Poly.maps _ (show Poly (fun j : Tally => (true,j)) by fun_prop)))

private theorem lineup_range (v : ℕ) : Iter.lineup (tally v) = (List.range v).map tally := by
  apply List.ext_getElem <;> simp [Iter.lineup]

private theorem localOrder_eq (D : ℕ) :
    localOrder (tally D) = (Benes.executionOrder D).map (fun t => (t.1,tally t.2)) := by
  rw [localOrder,lineup_range]
  simp [Benes.executionOrder,List.map_map,List.map_reverse,Function.comp_def]

private theorem depthOrder_vals (d : ℕ) :
    (depthOrder d).map (fun j => tally j.val) = ((List.range (Nat.clog 2 d)).map tally).reverse := by
  apply List.ext_getElem <;> simp [depthOrder]

private theorem unaryDepths_eq (inv : Bool) (ds : List ControlAxis) :
    unaryDepths (inv,ds) = (bif inv then (depthOrder ds.length).reverse else depthOrder ds.length).map
      (fun j => tally j.val) := by
  simp only [unaryDepths,Carry.light_v,Carry.birthValue,lineup_range]
  cases inv <;> simp [depthOrder_vals,List.map_reverse]

private abbrev LocalSeed := (Bool × List ControlAxis × List (Bool × Tally)) × Tally

private def emitDepth (q : LocalSeed) : List HeaderSeed :=
  polyPush (fun s : (Bool × Tally × List ControlAxis) × (Bool × Tally) => (s.2,s.1))
    ((q.1.1,q.2,q.1.2.1),q.1.2.2)

private theorem emitDepth_poly : Poly emitDepth := by
  have init : Poly (fun q : LocalSeed => ((q.1.1,q.2,q.1.2.1),q.1.2.2)) := by fun_prop
  exact init.compose (Poly.push (false,[],[]) (false,[]) Easy.exchange.poly)

abbrev StreamQuery := Bool × Tally × List ControlAxis

/-- Reuse the box descriptor on every depth and on every direction/bit stage
of that depth. The raw input gives the common padded width in unary. -/
def seedStream (q : StreamQuery) : List HeaderSeed :=
  (polyPush emitDepth ((q.1,q.2.2,localOrder q.2.1),unaryDepths (q.1,q.2.2))).flatten

theorem seedStream_poly : Poly seedStream := by
  have localLayers := (show Poly (fun q : StreamQuery => q.2.1) by fun_prop).compose localOrder_poly
  have levels := (show Poly (fun q : StreamQuery => (q.1,q.2.2)) by fun_prop).compose unaryDepths_poly
  have ctx := (show Poly (fun q : StreamQuery => q.1) by fun_prop).pair
    ((show Poly (fun q : StreamQuery => q.2.2) by fun_prop).pair localLayers)
  exact ((ctx.pair levels).compose (Poly.push (false,[],[]) [] emitDepth_poly)).compose Easy.flatten.poly

theorem seedStream_eq (D : ℕ) (ds : List ControlAxis) (inv : Bool) :
    seedStream (inv,tally D,ds) = (switchOrder ds.length D inv).map
      (fun s => ((s.2.1,tally s.2.2),inv,tally s.1.val,ds)) := by
  simp [seedStream,unaryDepths_eq,localOrder_eq,polyPush,emitDepth,switchOrder,
    List.flatMap_def,List.map_map,Function.comp_def]

def headerStream (q : StreamQuery) : List (Benes.BatchPlan TargetTag) :=
  (seedStream q).map stageHeader

theorem headerStream_poly : Poly headerStream :=
  seedStream_poly.compose (Poly.maps stageHeader stageHeader_poly)

theorem headerStream_eq (D : ℕ) (ds : List ControlAxis) (inv : Bool) :
    headerStream (inv,tally D,ds) = (switchOrder ds.length D inv).map
      (fun s => stageHeader ((s.2.1,tally s.2.2),inv,tally s.1.val,ds)) := by
  simp [headerStream,seedStream_eq,List.map_map,Function.comp_def]

end CRTTable

end NearSquareRoot
end Computability
end OAI
