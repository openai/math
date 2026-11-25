import OAI.Computability.NearSquareRoot.KernelPassComputableSyntax

/-! # Dimensions, child-call counts and finite validation bounds in the bytecode -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.ComputableSyntax

abbrev Shape := (ℕ × ℕ) × ℕ × ℕ

namespace Shape

def empty : Shape := ((0,0),0,1)

def leaf (A : ℕ) (op : Op) : Shape :=
  if op.1 = 0 then ((arg op 0,arg op 1),0,1) else
  if op.1 = 1 then ((1,1),0,1) else
  if op.1 = 2 then ((1,1),0,2^(arg op 0)) else
  if op.1 = 3 then ((1,1),if arg op 0 < A then 1 else 0,1) else empty

def seq (l r : Shape) : Shape :=
  if r.1.2 = l.1.1 then ((r.1.1,l.1.2),l.2.1+r.2.1,l.1.1*(l.2.2*r.2.2)+1) else empty

def parallel (l r : Shape) : Shape :=
  ((l.1.1+r.1.1,l.1.2+r.1.2),l.2.1+r.2.1,max 1 (max l.2.2 r.2.2))

def algebra (A : ℕ) : Algebra Shape := ⟨empty,leaf A,seq,parallel⟩

theorem primrec_leaf : Primrec₂ leaf := by
  have op : Primrec (fun p : ℕ × Op => p.2) := Primrec.snd
  have tag := Primrec.fst.comp op
  have a := primrec_arg.comp op (Primrec.const 0)
  have b := primrec_arg.comp op (Primrec.const 1)
  exact (Primrec.ite (Primrec.eq.comp tag (.const 0)) ((a.pair b).pair (.const (0,1)))
    (Primrec.ite (Primrec.eq.comp tag (.const 1)) (.const ((1,1),0,1))
      (Primrec.ite (Primrec.eq.comp tag (.const 2))
        ((Primrec.const (1,1)).pair ((Primrec.const 0).pair (Generator.primrecNatPow.comp (.const 2) a)))
        (Primrec.ite (Primrec.eq.comp tag (.const 3))
          ((Primrec.const (1,1)).pair
            ((Primrec.ite (Primrec.nat_lt.comp a Primrec.fst) (.const 1) (.const 0)).pair (.const 1)))
          (.const empty))))).to₂

theorem primrec_seq : Primrec₂ seq := by
  let X := Shape × Shape
  have li : Primrec (fun p : X => p.1.1.1) := (Primrec.fst.comp Primrec.fst).comp Primrec.fst
  have lo : Primrec (fun p : X => p.1.1.2) := (Primrec.snd.comp Primrec.fst).comp Primrec.fst
  have ri : Primrec (fun p : X => p.2.1.1) := (Primrec.fst.comp Primrec.fst).comp Primrec.snd
  have ro : Primrec (fun p : X => p.2.1.2) := (Primrec.snd.comp Primrec.fst).comp Primrec.snd
  have bound := Primrec.nat_mul.comp li (Primrec.nat_mul.comp
    ((Primrec.snd.comp Primrec.snd).comp (Primrec.fst (α := Shape) (β := Shape)))
    ((Primrec.snd.comp Primrec.snd).comp Primrec.snd))
  have cost := Primrec.nat_add.comp ((Primrec.fst.comp Primrec.snd).comp (Primrec.fst (α := Shape) (β := Shape)))
    ((Primrec.fst.comp Primrec.snd).comp Primrec.snd)
  exact (Primrec.ite (Primrec.eq.comp ro li)
    ((ri.pair lo).pair (cost.pair (Primrec.succ.comp bound))) (.const empty)).to₂

private theorem pmax : Primrec₂ (max : ℕ → ℕ → ℕ) := by
  have h : Primrec (fun p : ℕ × ℕ => if p.1 ≤ p.2 then p.2 else p.1) :=
    Primrec.ite (Primrec.nat_le.comp Primrec.fst Primrec.snd) Primrec.snd Primrec.fst
  apply (Primrec.to₂ (f := fun p : ℕ × ℕ => max p.1 p.2))
  apply h.of_eq
  intro p
  by_cases hle : p.1 ≤ p.2 <;> simp [hle, Nat.le_of_not_ge]

theorem primrec_parallel : Primrec₂ parallel := by
  let X := Shape × Shape
  have addProj (f : Shape → ℕ) (hf : Primrec f) : Primrec
      (fun p : X => f p.1 + f p.2) := Primrec.nat_add.comp (hf.comp Primrec.fst) (hf.comp Primrec.snd)
  have dim := (addProj _ (Primrec.fst.comp Primrec.fst)).pair (addProj _ (Primrec.snd.comp Primrec.fst))
  have co := addProj _ (Primrec.fst.comp Primrec.snd)
  have bound := pmax.comp (.const 1) (pmax.comp
    ((Primrec.snd.comp Primrec.snd).comp (Primrec.fst (α := Shape) (β := Shape)))
    ((Primrec.snd.comp Primrec.snd).comp Primrec.snd))
  exact (dim.pair (co.pair bound)).to₂

theorem primrec_algebra : Primrec₂ fun A (ops : List Op) => (algebra A).parse ops := by
  exact (primrec_parse (fun p : ℕ × List Op => algebra p.1) empty (fun _ => rfl)
    ((primrec_leaf.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂)
    ((primrec_seq.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂)
    ((primrec_parallel.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂)
    Prod.snd Primrec.snd).to₂

end Shape
end KernelPass.ComputableSyntax

end NearSquareRoot
end Computability
end OAI
