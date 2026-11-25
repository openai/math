import OAI.Computability.NearSquareRoot.KernelPassComputableShape
import OAI.Computability.NearSquareRoot.KernelComputableSelector
import OAI.Computability.NearSquareRoot.KernelComputableDyadicCoefficient
import OAI.Computability.NearSquareRoot.KernelComputableMatrix

/-! # Interpreting raw prefix instructions as typed programs -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.ComputableSyntax

open KernelComputableDyadic KernelComputableAddress

structure Packed (A : ℕ) where
  i : ℕ
  o : ℕ
  plan : Plan A i o

namespace Packed

variable {A : ℕ}

def shape (p : Packed A) : Shape := ((p.i,p.o),p.plan.calls,p.plan.stateBound)

abbrev Represents (h : ℕ) (p : Packed A) (t : KernelComputableMatrix.Table) : Prop :=
  KernelComputableMatrix.Represents (p.i * (4^A)^h) (KernelComputableMatrix.bankIndex (pack A h))
    (KernelComputableMatrix.bankIndex (pack A h)) t (p.plan.eval h)

def empty (A : ℕ) : Packed A := ⟨0,0,.mix (fun _ _ => (0,0))⟩
def zeroRow (A : ℕ) : Packed A := ⟨1,1,.mix (fun _ _ => (0,0))⟩

def leaf (A : ℕ) (op : Op) : Packed A :=
  if op.1 = 0 then
    ⟨arg op 0,arg op 1,.mix (fun b a => coefficient (op.2.2.getD (b.val*arg op 0+a.val) zero))⟩
  else if op.1 = 1 then
    if ha : arg op 0 < A then
      if hb : arg op 1 < A then ⟨1,1,.xor (⟨_,ha⟩,⟨_,hb⟩)⟩ else zeroRow A
    else zeroRow A
  else if op.1 = 2 then
    ⟨1,1,.scale (arg op 0) (KernelComputableSelector.test A (arg op 0) op.2.1.tail)
      (KernelComputableSelector.table op.2.2)⟩
  else if op.1 = 3 then
    if ha : arg op 0 < A then ⟨1,1,.child ⟨_,ha⟩⟩ else zeroRow A
  else empty A

def seq (p q : Packed A) : Packed A :=
  if hj : q.o = p.i then ⟨q.i,p.o,p.plan.seq (hj ▸ q.plan)⟩ else empty A

def parallel (p q : Packed A) : Packed A :=
  ⟨p.i+q.i,p.o+q.o,p.plan.parallel q.plan⟩

def algebra (A : ℕ) : Algebra (Packed A) := ⟨empty A,leaf A,seq,parallel⟩

def decode (A : ℕ) (ops : List Op) : Packed A := (algebra A).parse ops

theorem leaf_shape (A : ℕ) (op : Op) : (leaf A op).shape = Shape.leaf A op := by
  unfold leaf Shape.leaf
  split_ifs <;> rfl

theorem seq_shape (p q : Packed A) : (seq p q).shape = Shape.seq p.shape q.shape := by
  obtain ⟨i,o,p⟩ := p
  obtain ⟨k,j,q⟩ := q
  by_cases h : j = i
  · subst i
    have hs : seq (mk j o p) (mk k j q) = mk k o (p.seq q) := by
      simp only [seq, dite_eq_ite, ite_true]
    rw [hs]
    change _ = if j = j then _ else _
    rw [ite_eq_left rfl]
    rfl
  · have hs : seq (mk i o p) (mk k j q) = empty A := dite_eq_right h
    rw [hs]
    change _ = if j = i then _ else _
    rw [ite_eq_right h]
    rfl

theorem decode_shape (A : ℕ) (ops : List Op) :
    (decode A ops).shape = (Shape.algebra A).parse ops :=
  parse_map shape rfl (leaf_shape A) seq_shape (fun _ _ => rfl) ops

end Packed
end KernelPass.ComputableSyntax

end NearSquareRoot
end Computability
end OAI
