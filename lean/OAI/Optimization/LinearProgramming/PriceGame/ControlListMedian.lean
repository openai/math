import OAI.Optimization.LinearProgramming.PriceGame.ControlListMedianOrder
import OAI.Optimization.LinearProgramming.PriceGame.LearningGroupingSort
import OAI.Optimization.LinearProgramming.PriceGame.ControlAssemblyValue

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram
open Learning.BitMachine

private theorem codeLength_of_perm (xs ys : List ℚ) (h : xs.Perm ys) :
    (listCode ratCode xs).length = (listCode ratCode ys).length := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [listCode_length_cons, ih]
  | swap x y xs => simp only [listCode_length_cons]; omega
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

private noncomputable def insertMedianP : Procedure (prodCode ratCode (listCode ratCode))
    (listCode ratCode) (fun x : ℚ × List ℚ => insertMedianValue x.1 x.2) := by
  let sw := Procedure.swap ratCode (listCode ratCode)
  let below := (filterWithP 0 (OracleSpec.Arithmetic.ratLe.comp (Procedure.swap ratCode ratCode))).comp sw
  let above := (filterWithP 0 OracleSpec.Arithmetic.ratLt).comp sw
  let value := Procedure.first ratCode (listCode ratCode)
  exact (Procedure.listAppend ratCode 0).comp
    (below.pair ((Procedure.listCons ratCode).comp (value.pair above)))

/-- Its polynomial clock charges each rational comparison and each sweep of the two
partitions. Permutation preserves total encoded length at every insertion prefix. -/
noncomputable def sortMedianValuesP : Procedure (listCode ratCode) (listCode ratCode) sortMedianValues := by
  let fold := Procedure.foldList 0 insertMedianP Polynomial.X (by
    intro xs acc i
    simp only [Polynomial.eval_X]
    have h := codeLength_of_perm _ _ (medianFold_perm (xs.take i) acc)
    have ha := listCode_length_append ratCode (xs.take i) acc
    have ht := listCode_length_take_le ratCode i xs
    omega)
  exact fold.comp ((Procedure.identity _).pair (Procedure.constant (listCode ratCode) (listCode ratCode) []))

/-- A physical sequential binary-stack program for the median with multiplicities. -/
noncomputable def medianRatList : Procedure (listCode ratCode) ratCode listMedian := by
  let half : Procedure Nat.bits Nat.bits Nat.div2 :=
    (Procedure.tail.precompose Nat.bits).result (fun n => (Nat.div2_bits_eq_tail n).symm)
  exact (Procedure.listGet ratCode 0).comp ((half.comp (Procedure.listLength ratCode 0)).pair sortMedianValuesP)

/-- The packed assembly's median operation is realized on all encoded lists. -/
noncomputable def medianValueP : Procedure (listCode ratCode) ratCode medianValue := by
  apply medianRatList.congrFun
  intro xs
  calc
    listMedian xs = listMedian (List.ofFn xs.get) := congrArg listMedian (List.ofFn_get xs).symm
    _ = medianValue xs := listMedian_ofFn xs.get

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
