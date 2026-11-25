import OAI.Optimization.LinearProgramming.OracleSpec.Arithmetic
import OAI.Optimization.LinearProgramming.PriceGame.LearningSkeleton
import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Sort

/-! A polynomial bit program for the one-based index of a compact cost and its
correspondence with the sorted support order isomorphism. Index zero is the dummy. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace BitMachine

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure (boolCode)

def supportIndex (x : ℕ × List ℕ) : ℕ :=
  if x.1 ∈ x.2 then x.2.idxOf x.1 + 1 else 0

def canonicalSupport {N : ℕ} (s : Skeleton N) : List ℕ := s.sources.sort.map Fin.val

private theorem val_idxOf {N : ℕ} (xs : List (Fin N)) (i : Fin N) :
    (xs.map Fin.val).idxOf i.val = xs.idxOf i := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases h : a=i
    · subst a; simp
    · have hn : a.val ≠ i.val := fun he => h (Fin.ext he)
      simp only [List.map_cons, List.idxOf_cons_ne _ hn, List.idxOf_cons_ne _ h, ih]

theorem supportIndex_canonical {N : ℕ} (s : Skeleton N) (i : Fin N) :
    supportIndex (i.val,canonicalSupport s) = (Compact.index s i).val := by
  have hm : i.val ∈ canonicalSupport s ↔ i ∈ s.sources := by
    constructor
    · intro hi
      obtain ⟨j,hj,hji⟩ := List.mem_map.mp hi
      have e : j=i := Fin.ext hji
      simpa [e] using hj
    · intro hi
      exact List.mem_map.mpr ⟨i,by simpa using hi,rfl⟩
  by_cases h : i∈s.sources
  · rw [supportIndex, ite_eq_left (hm.mpr h)]
    simp only [canonicalSupport, val_idxOf, Compact.index, dite_eq_left h, Fin.val_succ,
      Finset.orderIsoOfFin_symm_apply]
  · simp [supportIndex,hm,Compact.index,h]

private abbrev IndexState := ℕ × Bool × ℕ
private abbrev indexStateCode := prodCode Nat.bits (prodCode boolCode unaryCode)

private def indexStep : ℕ × IndexState → IndexState
  | (a,k,found,c) => (k, found || decide (a=k), if found || decide (a=k) then c else c+1)

private theorem index_fold (ks : List ℕ) (k : ℕ) (found : Bool) (c : ℕ) :
    ks.foldl (fun st a => indexStep (a,st)) (k,found,c) =
      (k,found || decide (k∈ks), c + if found then 0 else ks.idxOf k) := by
  induction ks generalizing found c with
  | nil => simp
  | cons a ks ih =>
    rw [List.foldl_cons]
    change ks.foldl _ (k,found || decide (a=k),if found || decide (a=k) then c else c+1) = _
    rw [ih]
    by_cases h : a=k
    · subst a
      cases found <;> simp
    · have h' : k≠a := Ne.symm h
      cases found <;> simp [h,h',List.idxOf_cons_ne _ h]
      omega

noncomputable def equalIndexP : Procedure (prodCode Nat.bits Nat.bits) boolCode
    (fun p : ℕ×ℕ => decide (p.1=p.2)) := by
  apply (Procedure.boolAnd.comp (Procedure.binaryLe.pair
    (Procedure.binaryLe.comp (Procedure.swap Nat.bits Nat.bits)))).congrFun
  intro x
  apply Bool.eq_iff_iff.mpr
  simp [le_antisymm_iff]

private noncomputable def indexStepP :
    Procedure (prodCode Nat.bits indexStateCode) indexStateCode indexStep := by
  let item := Procedure.first Nat.bits indexStateCode
  let st := Procedure.second Nat.bits indexStateCode
  let key := (Procedure.first Nat.bits (prodCode boolCode unaryCode)).comp st
  let rest := (Procedure.second Nat.bits (prodCode boolCode unaryCode)).comp st
  let hit := (Procedure.first boolCode unaryCode).comp rest
  let count := (Procedure.second boolCode unaryCode).comp rest
  let found := Procedure.boolOr.comp (hit.pair (equalIndexP.comp (item.pair key)))
  exact key.pair (found.pair (Procedure.conditional found count (Procedure.unarySuccessor.comp count)))

/-- Scan input IDs in order, counting until the first equality. Rejected costs get the dummy
index, while present indices are returned in binary after a single unary increment. -/
noncomputable def supportIndexP : Procedure (prodCode Nat.bits (listCode Nat.bits)) Nat.bits supportIndex := by
  let st := prodCode Nat.bits (prodCode boolCode unaryCode)
  let fold := Procedure.foldList 0 indexStepP (Polynomial.X+Polynomial.C 4) (by
    rintro xs ⟨k,found,c⟩ i
    rw [index_fold]
    have hidx := List.idxOf_le_length (l := xs.take i) (a := k)
    have hlen := list_length_le_code Nat.bits xs
    have ht : (xs.take i).length ≤ xs.length := by simp
    simp only [indexStateCode,prodCode,pairBits_length,boolCode,List.length_singleton,
      unaryCode,List.length_replicate,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
    split <;> omega)
  let inp := prodCode Nat.bits (listCode Nat.bits)
  let key := Procedure.first Nat.bits (listCode Nat.bits)
  let ids := Procedure.second Nat.bits (listCode Nat.bits)
  let state := key.pair ((Procedure.constant inp boolCode false).pair (Procedure.constant inp unaryCode 0))
  let result := fold.comp (ids.pair state)
  let tail := (Procedure.second Nat.bits (prodCode boolCode unaryCode)).comp result
  let found := (Procedure.first boolCode unaryCode).comp tail
  let count := (Procedure.second boolCode unaryCode).comp tail
  apply (Procedure.conditional found (Procedure.unaryToBits.comp (Procedure.unarySuccessor.comp count))
    (Procedure.constant inp Nat.bits 0)).congrFun
  rintro ⟨key,ids⟩
  change (if (ids.foldl (fun st a => indexStep (a,st)) (key,false,0)).2.1 then
      (ids.foldl (fun st a => indexStep (a,st)) (key,false,0)).2.2+1 else 0) = _
  simp [index_fold,supportIndex]

end BitMachine
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
