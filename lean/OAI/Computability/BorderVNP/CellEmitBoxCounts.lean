import OAI.Computability.BorderVNP.CellEmitBoxes
import OAI.Computability.BorderVNP.CellGadgetSteps
import OAI.Computability.QuantumFactoring.BitStackListIndex
import OAI.Computability.QuantumFactoring.BitStackMultiplier
import Mathlib.Data.List.DropRight

/-! # Physical visit counts and global offsets for the sparse box printer

The source packet contains multiplicities in binary. Each resolved reference contributes
its multiplicity times the number of factors in one copy. Prefix sums use those binary
products directly and do not enumerate the corresponding repeated occurrences.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram

/-- Number of original factor occurrences at one resolved box descriptor. -/
noncomputable def blockMultiplicity : Procedure blockCode Nat.bits (fun b => b.copies * b.factors.length) :=
  Procedure.binaryMul.comp (blockCopies.pair ((Procedure.listLength Typed.factor (.truth [] [])).comp blockFactors))

private noncomputable def oneWeight :
    Procedure (prodCode emptyCode blockCode) Nat.bits
      (fun x : Unit × BoxBlock => x.2.copies*x.2.factors.length) :=
  blockMultiplicity.comp (Procedure.second emptyCode blockCode)

private noncomputable def weights : Procedure Typed.directory Typed.naturals
    (fun d => d.blocks.map fun b => b.copies*b.factors.length) :=
  (Procedure.listMapWith (f := fun (_ : Unit) (b : BoxBlock) => b.copies*b.factors.length)
    (⟨0,0,0,[]⟩ : BoxBlock) 0 oneWeight).comp
    ((Procedure.constant Typed.directory emptyCode ()).pair getBlocks)

private theorem fold_sum (xs : List ℕ) (n : ℕ) :
    xs.foldl (fun acc x => x+acc) n = xs.sum+n := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih => simp [ih]; omega

private theorem sum_length (xs : List ℕ) (n : ℕ) :
    (xs.sum+n).bits.length ≤ (listCode Nat.bits xs).length+n.bits.length := by
  induction xs generalizing n with
  | nil => simp [listCode]
  | cons x xs ih =>
    have h := ih (x+n)
    have hx := bits_length_add x n
    rw [listCode_length_cons]
    simpa only [List.sum_cons, Nat.add_right_comm x xs.sum n, Nat.add_comm (x+n) xs.sum] using
      (show (xs.sum+(x+n)).bits.length ≤ 2*x.bits.length+2+(listCode Nat.bits xs).length+n.bits.length by omega)

private noncomputable def sumBinary : Procedure Typed.naturals Nat.bits List.sum := by
  let fold := Procedure.foldList 0 Procedure.binaryAdd Polynomial.X (by
    intro xs n i
    change ((xs.take i).foldl (fun acc x => x+acc) n).bits.length ≤ _
    rw [fold_sum,Polynomial.eval_X]
    exact (sum_length _ _).trans (Nat.add_le_add_right (listCode_length_take_le Nat.bits i xs) _))
  exact (fold.comp ((Procedure.identity Typed.naturals).pair (Procedure.constant _ Nat.bits 0))).congrFun
    (fun xs => by change xs.foldl _ 0 = _; rw [fold_sum,Nat.add_zero])

/-- The actual typed packet computes the total visit count without expanding any site copy. -/
noncomputable def getVisitCount : Procedure Typed.directory Nat.bits Directory.visitCount :=
  sumBinary.comp weights

private noncomputable def takeWeights : Procedure (prodCode Typed.naturals Nat.bits) Typed.naturals
    (fun x => x.1.take x.2) := by
  let xs := Procedure.first Typed.naturals Nat.bits
  let i := Procedure.second Typed.naturals Nat.bits
  let n := (Procedure.listLength Nat.bits 0).comp xs
  let left := Procedure.binarySub.comp (n.pair i)
  let rev := Procedure.listReverse Nat.bits 0
  let keep := (Procedure.listDrop Nat.bits).comp (left.pair (rev.comp xs))
  apply (rev.comp keep).congrFun
  rintro ⟨l,j⟩
  change (l.reverse.drop (l.length-j)).reverse = l.take j
  rw [← List.rdrop_eq_reverse_drop_reverse, List.rdrop]
  by_cases h : j ≤ l.length
  · rw [Nat.sub_sub_self h]
  · rw [Nat.sub_eq_zero_of_le (by omega : l.length ≤ j),Nat.sub_zero,
      List.take_length,List.take_of_length_le (by omega)]

/-- Original global row number of the first factor in the indexed box. The input box index
may exceed the number of descriptors, in which case the full prefix sum is returned. -/
noncomputable def getBlockStart : Procedure (prodCode Typed.directory Nat.bits) Nat.bits
    (fun x => ((x.1.blocks.take x.2).map (fun b => b.copies*b.factors.length)).sum) := by
  let w := weights.comp (Procedure.first Typed.directory Nat.bits)
  let i := Procedure.second Typed.directory Nat.bits
  exact (sumBinary.comp (takeWeights.comp (w.pair i))).congrFun (fun x => by
    change (((x.1.blocks.map _).take x.2).sum) = _
    rw [List.map_take])

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
