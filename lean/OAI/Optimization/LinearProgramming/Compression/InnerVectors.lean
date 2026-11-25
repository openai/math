import OAI.Optimization.LinearProgramming.Compression.NativeCache
import OAI.Optimization.LinearProgramming.Compression.InnerWire
import OAI.Optimization.LinearProgramming.Lattice.BitProjectorProcedures

/-! Exact list arithmetic inside the finite minor-service machine, once a physical rounding
session returns its integral homogeneous row. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner

open OracleSpec ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure
open Lattice.Bit
open scoped BigOperators

abbrev Ints := List ℤ
abbrev Rats := List ℚ
abbrev GraphResult := Bool × (Rats × ℚ)

/-- Native graph row, success flag, and affine offset in the graph session's output order. -/
def graphResultCode : GraphResult → Word := prodCode boolCode (prodCode Projector.rowCode ratCode)

def beforeLast (z : Ints) : Ints := z.reverse.tail.reverse

def lastOrZero (z : Ints) : ℤ := z.reverse.headD 0

def normalizeRow (z : Ints) : Rats := (beforeLast z).map fun a : ℤ => (a:ℚ)/(lastOrZero z:ℚ)

def padRow (z : Ints) : Ints := beforeLast z ++ [0,lastOrZero z]

private noncomputable def beforeLastP : Procedure intRowCode intRowCode beforeLast :=
  (listReverse intCode 0).comp ((listTail intCode).comp (listReverse intCode 0))

private noncomputable def lastOrZeroP : Procedure intRowCode intCode lastOrZero :=
  (listHead intCode 0).comp (listReverse intCode 0)

noncomputable def normalizeRowP : Procedure intRowCode Projector.rowCode normalizeRow := by
  let ctx := second unaryCode intRowCode
  let i := unaryToBits.comp (first unaryCode intRowCode)
  let value := (nthDP intCode 0).comp (i.pair (beforeLastP.comp ctx))
  let div := ratDiv.comp ((intToRat.comp value).pair ((intToRat.comp lastOrZeroP).comp ctx))
  refine (tabulateAlongP (f := fun z : Ints => fun i => (((beforeLast z)[i]?.getD 0 : ℤ) : ℚ) / (lastOrZero z : ℚ))
    (0 : ℤ) (0 : ℚ) beforeLastP div).congrFun ?_
  intro z
  apply List.ext_getElem
  · simp [normalizeRow]
  · intro i _ hi
    have h : i < (beforeLast z).length := by simpa only [normalizeRow,List.length_map] using hi
    simp [normalizeRow,List.getElem?_eq_getElem h]

noncomputable def padRowP : Procedure intRowCode intRowCode padRow := by
  let tail := (listCons intCode).comp (lastOrZeroP.pair (constant intRowCode intRowCode ([]:Ints)))
  let right := (listCons intCode).comp ((constant intRowCode intCode (0:ℤ)).pair tail)
  exact (listAppend intCode 0).comp (beforeLastP.pair right)

private theorem packedSnoc {α : Type*} {g : ℕ} (v : Fin g → α) (x : α) :
    List.ofFn (Fin.snoc v x) = List.ofFn v ++ [x] := by
  rw [List.ofFn_succ']; simp [List.concat_eq_append]

private theorem beforeLast_pack {g : ℕ} (z : Fin (g+1) → ℤ) :
    beforeLast (List.ofFn z) = List.ofFn (fun i : Fin g => z i.castSucc) := by
  rw [List.ofFn_succ' z]
  simp [beforeLast,List.concat_eq_append]

private theorem lastOrZero_pack {g : ℕ} (z : Fin (g+1) → ℤ) :
    lastOrZero (List.ofFn z) = z (Fin.last g) := by
  rw [List.ofFn_succ' z]
  simp [lastOrZero,List.concat_eq_append]

theorem normalizeRow_pack {g : ℕ} (z : Fin (g+1) → ℤ) :
    normalizeRow (List.ofFn z) = List.ofFn (normalizeCommit z) := by
  unfold normalizeRow
  rw [beforeLast_pack,lastOrZero_pack]
  exact List.map_ofFn

theorem padRow_pack {g : ℕ} (z : Fin (g+1) → ℤ) :
    padRow (List.ofFn z)=List.ofFn (padEpochQuery z) := by
  unfold padRow padEpochQuery
  rw [beforeLast_pack,lastOrZero_pack,packedSnoc,packedSnoc]
  simp [List.append_assoc]

def affineResult (gamma : Rats) (out : GraphResult) : Option ℚ :=
  if out.1 then some (Projector.dot out.2.1 gamma + out.2.2) else none

def combinedAnswer (x : Input) (gamma : Rats) (out : GraphResult) : Option ℚ :=
  if x.2.1 then some (readAt 0 gamma x.2.2) else affineResult gamma out

noncomputable def someWordP : Procedure ratCode (id : Word → Word) (fun q => outputWord (some q)) := by
  let p : Procedure ratCode Games.RecoveryMachine.answerCode (fun q => some q) :=
    (Procedure.prepend ratCode [true]).result (fun _ => rfl)
  exact Games.RecoveryMachine.writeAnswer.comp p

noncomputable def affineResultP : Procedure (prodCode Projector.rowCode graphResultCode)
    (id : Word → Word) (fun x => outputWord (affineResult x.1 x.2)) := by
  let gamma := first Projector.rowCode graphResultCode
  let o := second Projector.rowCode graphResultCode
  let flag := (first boolCode (prodCode Projector.rowCode ratCode)).comp o
  let terms := (second boolCode (prodCode Projector.rowCode ratCode)).comp o
  let a := (first Projector.rowCode ratCode).comp terms
  let c := (second Projector.rowCode ratCode).comp terms
  let v := ratAdd.comp ((Projector.dotP.comp (a.pair gamma)).pair c)
  refine (conditional flag (someWordP.comp v) (constant _ (id : Word → Word) [false])).congrFun ?_
  rintro ⟨xs,flag,as,c⟩
  cases flag <;> rfl

theorem affineResult_pack {g : ℕ} (gamma a : Fin g → ℚ) (c : ℚ) :
    affineResult (List.ofFn gamma) (true,List.ofFn a,c) = some (∑ i, a i * gamma i + c) := by
  simp [affineResult,Projector.dot_pack,dotProduct]

end Inner
end Compression
end LinearProgramming
end Optimization
end OAI
