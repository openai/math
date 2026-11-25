import OAI.Optimization.LinearProgramming.PriceGame.LearningGroupingSort
import OAI.Optimization.LinearProgramming.PriceGame.LearningGroupingIndex
import OAI.Optimization.LinearProgramming.PriceGame.LearningPackedTestMachine

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace BitMachine

open Control Control.Wire States.Mass ExactQuantumFactoring.BitStackProgram

/-- Original addresses occurring in the ordered tuple or in the optional path pivot. -/
def supportAddresses (e : PackedExpert) : List ℕ :=
  (e.tuple.map fun i => i >>> e.level) ++
    (e.pivot.toList.map fun p => p.2 >>> p.1)

def packedSupport (e : PackedExpert) : List ℕ := (supportAddresses e).toFinset.sort

private theorem addresses_pack {N : ℕ} (e : Expert N) :
    supportAddresses (packExpert e) = (List.ofFn fun j => (e.skeleton.origin j).val) ++
      (e.skeleton.pivot.toList.map fun p => (rootVertex N p.1 p.2).val) := by
  cases hp : e.skeleton.pivot with
  | none => simp [supportAddresses,packExpert,root_address,Skeleton.origin,hp]
  | some p =>
    obtain ⟨k,i⟩ := p
    simp [supportAddresses,packExpert,root_address,Skeleton.origin,hp]

theorem packedSupport_pack {N : ℕ} (e : Expert N) :
    packedSupport (packExpert e) = canonicalSupport e.skeleton := by
  apply (Finset.sortedLT_sort _).pairwise.eq_of_mem_iff
  · change (e.skeleton.sources.sort.map Fin.val).Pairwise (· < ·)
    rw [List.pairwise_map]
    exact e.skeleton.sources.sortedLT_sort.pairwise
  · intro a
    simp only [Finset.mem_sort, List.mem_toFinset, addresses_pack,
      List.mem_append, List.mem_ofFn, List.mem_map, canonicalSupport, Skeleton.sources,
      Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    cases hp : e.skeleton.pivot with
    | none => simp
    | some p => simp

/-- A real machine for the increasing list of all distinct original cost addresses. -/
noncomputable def packedSupportP : Procedure packedExpertCode (listCode Nat.bits) packedSupport := by
  let tuple := (Market.GridMachine.mapWithContext 0 0 (rootAddressP.comp (Procedure.swap Nat.bits Nat.bits))).comp
    (expertTupleP.pair expertLevelP)
  let cell := rootAddressP.comp (Procedure.swap Nat.bits Nat.bits)
  let lone := (Procedure.listCons Nat.bits).comp
    (cell.pair (Procedure.constant (prodCode Nat.bits Nat.bits) (listCode Nat.bits) []))
  let piv := (optionCasesP [] lone).comp expertPivotP
  let all := (Procedure.listAppend Nat.bits 0).comp (tuple.pair piv)
  apply (sortKeysP.comp all).congrFun
  intro e
  cases h : e.pivot with
  | none => simp [packedSupport,supportAddresses,h]
  | some p => obtain ⟨k,i⟩ := p; simp [packedSupport,supportAddresses,h]

end BitMachine
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
