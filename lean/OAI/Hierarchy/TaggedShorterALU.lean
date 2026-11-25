import OAI.Hierarchy.TaggedShorterBoolBatch
import OAI.ThreeFlat.Diagonal.TracePairInputs

namespace OAI
/-! # A shared linear-size transcript checking every bit of a CPU add or subtract result -/

noncomputable section
namespace Hierarchy.TaggedShorterALU

open ThreeFlat Diagonal TraceWords
open Computability.VPVNP.BurstRAM PrivateRAM
open ExactQuantumFactoring ExactQuantumFactoring.BooleanNetwork
open scoped Classical

variable {F : Type*} {w r p : ℕ}

def batch (op : BinaryOp) (a b : Fin r) : TraceCompose.Batch (TracePair.Raw w r) (Fin w) :=
  TaggedShorterBoolBatch.wordBatch (TracePair.operandInput a b) (TraceBinaryOps.network op w)

theorem batch_eval (op : BinaryOp) (a b : Fin r) (raw : TracePair.Raw w r → Bool)
    (x y : Word w) (left : ∀ j : Fin w, raw (false,Fin.natAdd 5 a,j.castSucc)=bits x j)
    (right : ∀ j : Fin w, raw (false,Fin.natAdd 5 b,j.castSucc)=bits y j) (j : Fin w) :
    (batch op a b).eval raw j = bits (op.eval x y) j := by
  unfold batch
  rw [TaggedShorterBoolBatch.wordBatch_eval]
  have operands : (fun i => (TracePair.operandInput a b i).elim raw id)=Fin.append (bits x) (bits y) := by
    funext i
    induction i using Fin.addCases with
    | left t => simpa [TracePair.operandInput] using left t
    | right t => simpa only [TracePair.operandInput, Fin.addCases_right, Fin.append_right, Sum.elim_inl] using right t
  rw [operands,TraceBinaryOps.network_correct]

def network [Zero F] [One F] (op : BinaryOp) (a b : Fin r)
    (input : TracePair.Raw w r → Fin p) (expected : Fin w → Fin p) : BitNetwork F p :=
  TaggedShorterBoolBatch.network (batch op a b) input expected

theorem eval [CommRing F] (op : BinaryOp) (a b : Fin r) (input : TracePair.Raw w r → Fin p)
    (expected : Fin w → Fin p) (pin : Fin p → Bool) (x y z : Word w)
    (left : ∀ j : Fin w, pin (input (false,Fin.natAdd 5 a,j.castSucc))=bits x j)
    (right : ∀ j : Fin w, pin (input (false,Fin.natAdd 5 b,j.castSucc))=bits y j)
    (out : ∀ j, pin (expected j)=bits z j) :
    (network (F:=F) op a b input expected).eval pin = if op.eval x y = z then 1 else 0 := by
  rw [network,TaggedShorterBoolBatch.eval]
  have tests : (∀ j,(batch op a b).eval (pin ∘ input) j=pin (expected j)) ↔ op.eval x y = z := by
    simp only [batch_eval op a b (pin ∘ input) x y left right,out,←funext_iff,bits_injective.eq_iff]
  by_cases h : op.eval x y = z
  · rw [ite_eq_left (tests.2 h),ite_eq_left h]
  · rw [ite_eq_right (fun a => h (tests.1 a)),ite_eq_right h]

theorem bitAnd_count (w : ℕ) : (TraceBinaryOps.network .bitAnd w).net.count ≤ w := by
  change (vector (fun j : Fin w => (bit (j.castAdd w)).band (bit (Fin.natAdd w j)))).net.count ≤ w
  simp

theorem size [Zero F] [One F] (op : BinaryOp) (cheap : op=.add ∨ op=.sub ∨ op=.bitAnd) (a b : Fin r)
    (input : TracePair.Raw w r → Fin p) (expected : Fin w → Fin p) :
    (network (F:=F) op a b input expected).cells + (network (F:=F) op a b input expected).internal
      ≤ 317*w+12 := by
  rw [network,TaggedShorterBoolBatch.size]
  change 2*(TraceBinaryOps.network op w).net.count+w ≤ 317*w+12
  rcases cheap with rfl | rfl | rfl
  · have := BitArithmetic.add_count w
    change 2*(BitArithmetic.add w).net.count+w ≤ _
    omega
  · have := BitArithmetic.sub_count w
    change 2*(BitArithmetic.sub w).net.count+w ≤ _
    omega
  · have := bitAnd_count w
    omega

end Hierarchy.TaggedShorterALU

end
end OAI
