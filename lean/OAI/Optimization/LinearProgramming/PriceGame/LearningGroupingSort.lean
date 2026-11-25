import OAI.Optimization.LinearProgramming.PriceGame.LearningGroupingList
import OAI.Optimization.LinearProgramming.PriceGame.MarketContextMap

/-! Polynomial-time sorting without repeated keys. Every running accumulator uses at
most the encoded sizes of the original list and its initial accumulator together. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace BitMachine

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure (boolCode)

noncomputable def filterWithP {C α : Type} {ec : C → List Bool} {ea : α → List Bool}
    (d : α) {test : C × α → Bool} (p : Procedure (prodCode ec ea) boolCode test) :
    Procedure (prodCode (listCode ea) ec) (listCode ea)
      (fun x : List α × C => x.1.filter fun a => test (x.2,a)) := by
  let marked := Market.GridMachine.mapWithContext d (false,d) (p.pair (Procedure.second ec ea))
  apply ((selectedP ea d).comp marked).congrFun
  intro x
  exact selected_map _ _

private theorem filtered_partition_length {α : Type} [LinearOrder α]
    (ea : α → List Bool) (a : α) (xs : List α) :
    (listCode ea (xs.filter fun b => decide (b<a))).length +
      (listCode ea (xs.filter fun b => decide (a<b))).length ≤ (listCode ea xs).length+1 := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    rcases lt_trichotomy b a with h|rfl|h
    · have h' := not_lt_of_ge h.le
      simp only [List.filter_cons, decide_eq_true h, decide_eq_false h', ite_true, Bool.false_eq_true,
        ite_false,listCode_length_cons]
      omega
    · simp only [List.filter_cons,lt_self_iff_false,decide_false,Bool.false_eq_true,ite_false,listCode_length_cons]
      omega
    · have h' := not_lt_of_ge h.le
      simp only [List.filter_cons, decide_eq_true h, decide_eq_false h', ite_true, Bool.false_eq_true,
        ite_false,listCode_length_cons]
      omega

private theorem insertKey_length {α : Type} [LinearOrder α] (ea : α → List Bool) (a : α) (xs : List α) :
    (listCode ea (insertKey a xs)).length ≤ (listCode ea xs).length + 2*(ea a).length + 2 := by
  have hp := filtered_partition_length ea a xs
  have h := listCode_length_append ea (xs.filter fun b => decide (b<a))
    (a :: xs.filter fun b => decide (a<b))
  rw [listCode_length_cons] at h
  unfold insertKey
  omega

private theorem foldKeys_length {α : Type} [LinearOrder α] (ea : α → List Bool) (xs ys : List α) :
    (listCode ea (xs.foldl (fun acc a => insertKey a acc) ys)).length + 1 ≤
      (listCode ea xs).length + (listCode ea ys).length := by
  induction xs generalizing ys with
  | nil => simp [listCode]
  | cons a xs ih =>
    have h := ih (insertKey a ys)
    have h' := insertKey_length ea a ys
    simp only [List.foldl_cons,listCode_length_cons]
    omega

private noncomputable def insertKeyP {α : Type} [LinearOrder α] (ea : α → List Bool) (d : α)
    (ltP : Procedure (prodCode ea ea) boolCode (fun x => decide (x.1<x.2))) :
    Procedure (prodCode ea (listCode ea)) (listCode ea) (fun x => insertKey x.1 x.2) := by
  let sw := Procedure.swap ea (listCode ea)
  let below := (filterWithP d (ltP.comp (Procedure.swap ea ea))).comp sw
  let above := (filterWithP d ltP).comp sw
  let val := Procedure.first ea (listCode ea)
  exact (Procedure.listAppend ea d).comp
    (below.pair ((Procedure.listCons ea).comp (val.pair above)))

noncomputable def sortedUniqueP {α : Type} [LinearOrder α] (ea : α → List Bool) (d : α)
    (ltP : Procedure (prodCode ea ea) boolCode (fun x => decide (x.1<x.2))) :
    Procedure (listCode ea) (listCode ea) sortedUnique := by
  let fold := Procedure.foldList d (insertKeyP ea d ltP) Polynomial.X (by
    intro xs acc i
    simp only [Polynomial.eval_X]
    have h := foldKeys_length ea (xs.take i) acc
    have h' := listCode_length_take_le ea i xs
    omega)
  exact fold.comp ((Procedure.identity _).pair (Procedure.constant (listCode ea) (listCode ea) []))

/-- The exact increasing list of an arbitrary set of binary rational thresholds. -/
noncomputable def sortRationalP :
    Procedure (listCode ratCode) (listCode ratCode) (fun xs : List ℚ => xs.toFinset.sort) :=
  (sortedUniqueP ratCode 0 OracleSpec.Arithmetic.ratLt).congrFun sortedUnique_eq_sort

/-- The exact increasing list of distinct binary coordinate IDs. -/
noncomputable def sortKeysP :
    Procedure (listCode Nat.bits) (listCode Nat.bits) (fun xs : List ℕ => xs.toFinset.sort) :=
  (sortedUniqueP Nat.bits 0 Procedure.binaryLt).congrFun sortedUnique_eq_sort

end BitMachine
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
