import OAI.Computability.NearSquareRoot.CRTControlledReserveAddress
import OAI.Computability.NearSquareRoot.CRTPositionProgramNative
import OAI.Computability.NearSquareRoot.CRTPositionDescriptorEval

/-! # Orienting a row schedule for a physical address pullback -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled
noncomputable section

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip

theorem permuteNative_pullback {k : ℕ} (q : Equiv.Perm (Fin k)) :
    PositionProgram.permuteNative q = flatBitPullback q :=
  eq_flatBitPullback _ _ fun y j => congrFun (PositionProgram.permuteNative_bits q y) j

theorem permuteNative_symm_pullback {k : ℕ} (q : Equiv.Perm (Fin k)) :
    (PositionProgram.permuteNative q).symm = flatBitPullback q.symm :=
  eq_flatBitPullback _ _ fun y j => congrFun (PositionProgram.permuteNative_symm_bits q y) j

end
namespace ReserveProgram

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open Reflections (Table table next next_table)

private def applyPair (u : (Table × Table) × Tally) := next (u.1.1,next (u.1.2,u.2))

/-- To invert the input table, the tape program enumerates its positions and
reads the two computed reflection tables in reverse order. -/
def inverseTable (t : Table) : Table :=
  polyPush applyPair (Reflections.prepare t, Iter.lineup (ruler t))

theorem inverseTable_poly : Poly inverseTable :=
  (Reflections.poly_prepare.pair ((Easy.ruler (Easy.identity (X := Table))).poly.compose Iter.poly_line)).compose
    (Poly.push ([],[]) [] (show Poly applyPair by unfold applyPair; fun_prop))

theorem inverseTable_value {k : ℕ} (q : Equiv.Perm (Fin k)) :
    inverseTable (table q) = table q.symm := by
  have e : ruler (table q) = tally k := by rw [← recover_tally (ruler (table q)),ruler_length]; simp [table]
  unfold inverseTable
  rw [Reflections.prepare_spec,e,Iter.lined]
  change (List.ofFn (fun j : Fin k => tally j.val)).map _ = List.ofFn _
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  simp only [Function.comp_apply,applyPair,next_table]
  have inverse := congrArg Equiv.symm (Reflections.factor q)
  exact congrArg (fun e : Equiv.Perm (Fin k) => tally (e j).val) inverse

theorem inverseTable_has {I : Type*} {r : Regime I} {k : I → ℕ}
    (q : ∀ i, Equiv.Perm (Fin (k i))) (tab : r.Has (fun i => table (q i))) :
    r.Has (fun i => table (q i).symm) := by
  simpa only [inverseTable_value] using tab.thenDo inverseTable_poly

end ReserveProgram
end Controlled

end NearSquareRoot
end Computability
end OAI
