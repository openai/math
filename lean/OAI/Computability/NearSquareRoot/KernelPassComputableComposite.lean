import OAI.Computability.NearSquareRoot.KernelPassComputableLeaves
import OAI.Computability.NearSquareRoot.KernelPassComputablePacked
import OAI.Computability.NearSquareRoot.KernelPassComputableRelation
import OAI.Computability.NearSquareRoot.KernelComputableMatrixProduct
import OAI.Computability.NearSquareRoot.KernelComputableMatrixBlock

/-! # Primitive-recursive execution of raw template descriptions at one width

The stack stores inferred row counts together with dense dyadic matrices.
The numeric and typed interpreters both map an invalid serial composition to
the empty bank. The evaluator therefore has semantics for every instruction list. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.ComputableSyntax

open KernelComputableMatrix KernelComputableAddress

private abbrev State := Shape × Table

private def stackSeq (n : ℕ) (l r : State) : State :=
  (Shape.seq l.1 r.1,
    if r.1.1.2 = l.1.1.1 then
      product (l.1.1.2*n) (l.1.1.1*n) (r.1.1.1*n) l.2 r.2 else [])

private def stackParallel (n : ℕ) (l r : State) : State :=
  (Shape.parallel l.1 r.1,
    block (l.1.1.2*n) (r.1.1.2*n) (l.1.1.1*n) (r.1.1.1*n) l.2 r.2)

private def denseAlgebra (A h : ℕ) : Algebra State where
  empty := (Shape.empty, [])
  leaf op := (Shape.leaf A op, leafTable A h op)
  seq := stackSeq ((4^A)^h)
  parallel := stackParallel ((4^A)^h)

/-- Dense dyadic matrix of the decoded plan at a given width. -/
def compiledTable (A h : ℕ) (ops : List Op) : Table := ((denseAlgebra A h).parse ops).2

private theorem primrec_stackSeq {X : Type*} [Primcodable X] {n : X → ℕ} {l r : X → State}
    (hn : Primrec n) (hl : Primrec l) (hr : Primrec r) :
    Primrec fun x => stackSeq (n x) (l x) (r x) := by
  have sl := Primrec.fst.comp hl
  have sr := Primrec.fst.comp hr
  have li := Primrec.fst.comp (Primrec.fst.comp sl)
  have lo := Primrec.snd.comp (Primrec.fst.comp sl)
  have ri := Primrec.fst.comp (Primrec.fst.comp sr)
  have ro := Primrec.snd.comp (Primrec.fst.comp sr)
  exact (Shape.primrec_seq.comp sl sr).pair (Primrec.ite (Primrec.eq.comp ro li)
    (primrec_product (Primrec.nat_mul.comp lo hn) (Primrec.nat_mul.comp li hn) (Primrec.nat_mul.comp ri hn)
      (Primrec.snd.comp hl) (Primrec.snd.comp hr)) (.const []))

private theorem primrec_stackParallel {X : Type*} [Primcodable X] {n : X → ℕ} {l r : X → State}
    (hn : Primrec n) (hl : Primrec l) (hr : Primrec r) :
    Primrec fun x => stackParallel (n x) (l x) (r x) := by
  have sl := Primrec.fst.comp hl
  have sr := Primrec.fst.comp hr
  have li := Primrec.fst.comp (Primrec.fst.comp sl)
  have lo := Primrec.snd.comp (Primrec.fst.comp sl)
  have ri := Primrec.fst.comp (Primrec.fst.comp sr)
  have ro := Primrec.snd.comp (Primrec.fst.comp sr)
  exact (Shape.primrec_parallel.comp sl sr).pair (primrec_block (Primrec.nat_mul.comp lo hn)
    (Primrec.nat_mul.comp ro hn) (Primrec.nat_mul.comp li hn) (Primrec.nat_mul.comp ri hn)
    (Primrec.snd.comp hl) (Primrec.snd.comp hr))

theorem primrec_compiledTable {X : Type*} [Primcodable X] {A h : X → ℕ} {ops : X → List Op}
    (hA : Primrec A) (hh : Primrec h) (hops : Primrec ops) :
    Primrec fun x => compiledTable (A x) (h x) (ops x) := by
  have hn : Primrec fun x => (4 ^ A x) ^ h x :=
    Generator.primrecNatPow.comp (Generator.primrecNatPow.comp (.const 4) hA) hh
  apply Primrec.snd.comp
  apply primrec_parse (fun x => denseAlgebra (A x) (h x)) (Shape.empty,[]) (fun _ => rfl)
  · exact ((Shape.primrec_leaf.comp (hA.comp .fst) .snd).pair
      (primrec_leafTable (hA.comp .fst) (hh.comp .fst) .snd)).to₂
  · exact (primrec_stackSeq (hn.comp .fst) (Primrec.fst.comp .snd) (Primrec.snd.comp .snd)).to₂
  · exact (primrec_stackParallel (hn.comp .fst) (Primrec.fst.comp .snd) (Primrec.snd.comp .snd)).to₂
  · exact hops

private def Rel {A : ℕ} (h : ℕ) (p : Packed A) (s : State) : Prop :=
  p.shape = s.1 ∧ Packed.Represents h p s.2

private theorem empty_rel (A h : ℕ) : Rel h (Packed.empty A) (Shape.empty,[]) := by
  refine ⟨rfl, ?_⟩
  intro r
  exact Fin.elim0 r.1

private theorem seq_rel {A h : ℕ} (p q : Packed A) (l r : State)
    (hl : Rel h p l) (hr : Rel h q r) :
    Rel h (Packed.seq p q) (stackSeq ((4^A)^h) l r) := by
  rcases l with ⟨lshape,l⟩
  rcases r with ⟨rshape,r⟩
  rcases hl with ⟨rfl,hl⟩
  rcases hr with ⟨rfl,hr⟩
  refine ⟨Packed.seq_shape _ _, ?_⟩
  rcases p with ⟨pi,po,p⟩
  rcases q with ⟨qi,qo,q⟩
  by_cases hmatch : qo = pi
  · subst qo
    have heq : Packed.seq (⟨pi,po,p⟩ : Packed A) ⟨qi,pi,q⟩ = ⟨qi,po,p.seq q⟩ := by
      unfold Packed.seq
      split
      · rfl
      · contradiction
    rw [heq]
    simpa [Packed.shape, Packed.Represents, Plan.eval, stackSeq] using
      represents_bank_product (pack A h) (p.eval h) (q.eval h) l r hl hr
  · simpa [Packed.seq, Packed.shape, stackSeq, hmatch] using
      (empty_rel A h).2

private theorem parallel_rel {A h : ℕ} (p q : Packed A) (l r : State)
    (hl : Rel h p l) (hr : Rel h q r) :
    Rel h (Packed.parallel p q) (stackParallel ((4^A)^h) l r) := by
  rcases l with ⟨lshape,l⟩
  rcases r with ⟨rshape,r⟩
  rcases hl with ⟨rfl,hl⟩
  rcases hr with ⟨rfl,hr⟩
  exact ⟨rfl, block_represents (pack A h) l r (p.plan.eval h) (q.plan.eval h) hl hr⟩

/-- Every in-range block and address of the computed table has the entry of
the decoded typed plan, for arbitrary raw bytecode and width. -/
theorem compiledTable_represents (A h : ℕ) (ops : List Op) :
    Packed.Represents h (Packed.decode A ops) (compiledTable A h ops) := by
  have hrel : Rel h ((Packed.algebra A).parse ops) ((denseAlgebra A h).parse ops) :=
    Algebra.parse_rel (Rel h) (empty_rel A h)
      (fun op => ⟨Packed.leaf_shape A op, leafTable_represents A h op⟩) seq_rel parallel_rel ops
  exact hrel.2

end KernelPass.ComputableSyntax

end NearSquareRoot
end Computability
end OAI
