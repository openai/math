import OAI.Hierarchy.DescentExteriorChunks
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI
/-! # Static inter-pass wiring and exact multiplicity of the two exterior witnesses -/
namespace Hierarchy.DescentExterior
open DescentGL
open scoped Classical BigOperators
noncomputable section

variable {A B T : Type}

def ChunkPermutation.equiv (c : ChunkPermutation A B) : (B×A) ≃ (B×A) where
  toFun := c.apply
  invFun y :=
    let a:=c.row.symm y.2
    ((c.slot a).symm y.1,a)
  left_inv x := by simp [ChunkPermutation.apply]
  right_inv y := by simp [ChunkPermutation.apply]

/-- A selected row header gives the single source address for the whole
destination chunk. Only the small immutable lookup reorders slots. -/
def rowRead (c : ChunkPermutation A B) (x : B×A→T) (a : A) (b : B) : T :=
  let src:=c.row.symm a
  x ((c.slot src).symm b,src)

theorem rowRead_source (c : ChunkPermutation A B) (x : B×A→T) (a : A) (b : B) :
    rowRead c x (c.row a) (c.slot a b)=x (b,a) := by simp [rowRead]

def push (c : ChunkPermutation A B) (x : B×A→T) : B×A→T := x ∘ c.equiv.symm

theorem push_wire (c : ChunkPermutation A B) (x : B×A→T) (i : B×A) :
    push c x i=rowRead c x i.2 i.1 := rfl

theorem push_apply (c : ChunkPermutation A B) (x : B×A→T) (i : B×A) :
    push c x (c.apply i)=x i := congrArg x (c.equiv.symm_apply_apply i)

abbrev Plane (j r : ℕ) := Bits j × Rows j r

/-- Both reads of each guessed bit have literally the same physical pin.
Read the proposed output in ordinary order and the next input after the
fixed exchange of the two j-bit coordinate fields. -/
def swapWire {j r : ℕ} (x : Plane j r→T) : Plane j r→T := x ∘ flip

theorem swapWire_flip {j r : ℕ} (x : Plane j r→T) (i : Plane j r) :
    swapWire x (flip i)=x i := rfl

def stagesOK {j r : ℕ} (M : Layout (j+(j+r))) (x a b : Plane j r→T) : Prop :=
  (∀i,a i=rowRead (plan M).first x i.2 i.1) ∧
  (∀i,b i=rowRead (plan M).middle (swapWire a) i.2 i.1)

theorem stages_iff {j r : ℕ} (M : Layout (j+(j+r))) (x a b : Plane j r→T) :
    stagesOK M x a b ↔ a=push (plan M).first x ∧ b=push (plan M).middle (swapWire a) := by
  simp only [stagesOK,funext_iff,push_wire]

def output {j r : ℕ} (M : Layout (j+(j+r))) (b : Plane j r→T) : Plane j r→T :=
  push (plan M).last (swapWire b)

theorem output_wire {j r : ℕ} (M : Layout (j+(j+r))) (x a b : Plane j r→T)
    (ok : stagesOK M x a b) (i : Bits (j+(j+r))) :
    output M b (coords j r (M i))=x (coords j r i) := by
  obtain ⟨rfl,rfl⟩:=(stages_iff M x a b).mp ok
  rw [plan_apply,output,push_apply]
  simp only [swapWire_flip,push_apply]

/-- Closing the two guessed planes contributes exactly once, over any
coefficient field and for any continuation that reads the final array. -/
theorem sum_proposals {j r : ℕ} [Fintype T] {F : Type} [CommSemiring F]
    (M : Layout (j+(j+r))) (x : Plane j r→T) (finish : (Plane j r→T)→F) :
    (∑a : Plane j r→T,∑b : Plane j r→T,
        if stagesOK M x a b then finish (output M b) else 0)=
      finish (fun h=>x (coords j r (M.symm ((coords j r).symm h)))) := by
  simp_rw [stages_iff,ite_and]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  apply congrArg finish
  funext h
  let a:=push (plan M).first x
  let b:=push (plan M).middle (swapWire a)
  have exactPos:=output_wire M x a b ((stages_iff ..).mpr ⟨rfl,rfl⟩)
    (M.symm ((coords j r).symm h))
  simpa only [LinearEquiv.apply_symm_apply,a,b] using exactPos

theorem proposal_bits (j r stackBits : ℕ) :
    Fintype.card ((Bool×Plane j r)×Fin stackBits)=2*2^(j+(j+r))*stackBits := by
  simp [Plane,Rows,pow_add,Nat.mul_assoc]

end
end Hierarchy.DescentExterior

end OAI
