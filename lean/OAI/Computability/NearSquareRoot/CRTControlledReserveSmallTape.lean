import OAI.Computability.NearSquareRoot.CRTControlledReserveConjugate
import OAI.Computability.NearSquareRoot.CRTPositionDescriptorEval
import OAI.Computability.IntegerMultiplication.Code.Pace

/-! # Compiling small permutation tables into elementary exchanges -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.ReserveSmall

open IntegerMultiplication IntegerMultiplication.Code
open Reflections (Table Pair table next next_table)

/-- Emit the position and its image in ascending position order, retaining precisely
the lower endpoint of each transposition when the table is an involution. -/
def compile (t : Table) : List Pair :=
  (polyPush (fun z => (z.2, next z)) (t, Iter.lineup (ruler t))).filter Iter.small

@[fun_prop] theorem poly_compile : Poly compile := by
  have inputs : Poly (fun t : Table => (t, Iter.lineup (ruler t))) :=
    Poly.identity.pair ((Easy.ruler Easy.identity).poly.compose Iter.poly_line)
  have rows := inputs.compose
    (Poly.push [] [] (show Poly (fun z : Table × Tally => (z.2, next z)) by fun_prop))
  exact rows.compose (Poly.filter _ Iter.small_easy.poly)

theorem compile_table {k : ℕ} (p : Equiv.Perm (Fin k)) :
    compile (table p) = ReserveProgram.encodedMoves
      (((List.finRange k).filter fun j => decide (j < p j)).map fun j => (j, p j)) := by
  have h : Iter.lineup (ruler (table p)) = (List.finRange k).map (fun j => tally j.val) := by
    rw [← recover_tally (ruler (table p)), ruler_length,
      show (table p).length = k by simp [table], Iter.lined, ← List.ofFn_id k, List.map_ofFn]
    rfl
  simp only [compile, h, polyPush, List.map_map, List.filter_map, Function.comp_def,
    next_table, Iter.small, tally_length, ReserveProgram.encodedMoves, ReserveProgram.endpointPair]
  rfl

/-- Emit the second reflection's moves followed by the first reflection's moves,
in the order used by `positionExchanges`. -/
def compileBoth (t : Table) : List Pair :=
  let z := Reflections.prepare t
  compile z.2 ++ compile z.1

@[fun_prop] theorem poly_compileBoth : Poly compileBoth := by
  unfold compileBoth
  fun_prop

theorem compileBoth_table {k : ℕ} (p : Equiv.Perm (Fin k)) :
    compileBoth (table p) = compile (table (Reflections.second p)) ++
      compile (table (Reflections.first p)) := by
  simp only [compileBoth, Reflections.prepare_spec]

end Controlled.ReserveSmall

end NearSquareRoot
end Computability
end OAI
