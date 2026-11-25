import OAI.Computability.NearSquareRoot.KernelPassComputablePacked
import OAI.Computability.NearSquareRoot.KernelComputableSelector
import OAI.Computability.NearSquareRoot.KernelComputableAddressXor
import OAI.Computability.NearSquareRoot.KernelComputableAddressLeaves
import OAI.Computability.NearSquareRoot.KernelComputableMatrix

/-! # Primitive recursive dense matrices for the binary template leaves -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.ComputableSyntax
open KernelComputableAddress KernelComputableMatrix

/-- Each numerical leaf acts on a pair of bank rows and a pair of packed addresses. -/
def leafScalar (A h : ℕ) (op : Op) (b i y x : ℕ) : Scalar :=
  if op.1 = 0 then if x = y then entry (arg op 0) op.2.2 b i else KernelComputableDyadic.zero else
  if op.1 = 1 then if arg op 0 < A ∧ arg op 1 < A then
    xorEntry A h (arg op 0) (arg op 1) y x else KernelComputableDyadic.zero else
  if op.1 = 2 then KernelComputableSelector.entry A h (arg op 0) op.2.1.tail op.2.2 y x else
  if op.1 = 3 ∧ arg op 0 < A then child A h (arg op 0) y x else KernelComputableDyadic.zero

/-- Materialize a row-major table with the dimensions of the verified leaf parser. -/
def leafTable (A h : ℕ) (op : Op) : Table :=
  let n := (4^A)^h
  let sh := Shape.leaf A op
  make (sh.1.2*n) (sh.1.1*n) fun r s =>
    leafScalar A h op (r/n) (s/n) (r%n) (s%n)

variable {X : Type*} [Primcodable X]

theorem primrec_leafScalar {A h b i y x : X → ℕ} {op : X → Op}
    (hA : Primrec A) (hh : Primrec h) (hop : Primrec op) (hb : Primrec b)
    (hi : Primrec i) (hy : Primrec y) (hx : Primrec x) :
    Primrec (fun t => leafScalar (A t) (h t) (op t) (b t) (i t) (y t) (x t)) := by
  have tag := Primrec.fst.comp hop
  have param (j : ℕ) := primrec_arg.comp hop (Primrec.const j)
  have vs := (Primrec.snd.comp Primrec.snd).comp hop
  have tests := Primrec.list_tail.comp ((Primrec.fst.comp Primrec.snd).comp hop)
  have hm := Primrec.ite (Primrec.eq.comp hx hy)
    (KernelComputableMatrix.primrec_entry (param 0) vs hb hi) (Primrec.const KernelComputableDyadic.zero)
  have hg := Primrec.ite ((Primrec.nat_lt.comp (param 0) hA).and (Primrec.nat_lt.comp (param 1) hA))
    (primrec_xorEntry hA hh (param 0) (param 1) hy hx) (Primrec.const KernelComputableDyadic.zero)
  have hs := KernelComputableSelector.primrec_entry hA hh (param 0) tests vs hy hx
  have hc := Primrec.ite ((Primrec.eq.comp tag (Primrec.const 3)).and (Primrec.nat_lt.comp (param 0) hA))
    (primrec_child hA hh (param 0) hy hx) (Primrec.const KernelComputableDyadic.zero)
  exact Primrec.ite (Primrec.eq.comp tag (Primrec.const 0)) hm
    (Primrec.ite (Primrec.eq.comp tag (Primrec.const 1)) hg
      (Primrec.ite (Primrec.eq.comp tag (Primrec.const 2)) hs hc))

theorem primrec_leafTable {A h : X → ℕ} {op : X → Op}
    (hA : Primrec A) (hh : Primrec h) (hop : Primrec op) :
    Primrec (fun t => leafTable (A t) (h t) (op t)) := by
  have hn := primrec_pow (primrec_pow (Primrec.const 4) hA) hh
  have sh := Shape.primrec_leaf.comp hA hop
  have hi := (Primrec.fst.comp Primrec.fst).comp sh
  have ho := (Primrec.snd.comp Primrec.fst).comp sh
  let Y := X × ℕ × ℕ
  have r : Primrec (fun t : Y => t.2.1) := Primrec.fst.comp Primrec.snd
  have s : Primrec (fun t : Y => t.2.2) := Primrec.snd.comp Primrec.snd
  have n := hn.comp (Primrec.fst (β := ℕ × ℕ))
  exact primrec_make (f := fun u r s =>
      let n := (4^A u)^h u
      leafScalar (A u) (h u) (op u) (r/n) (s/n) (r%n) (s%n))
    (Primrec.nat_mul.comp ho hn) (Primrec.nat_mul.comp hi hn)
    (primrec_leafScalar (hA.comp Primrec.fst) (hh.comp Primrec.fst) (hop.comp Primrec.fst)
      (Primrec.nat_div.comp r n) (Primrec.nat_div.comp s n) (Primrec.nat_mod.comp r n) (Primrec.nat_mod.comp s n))

theorem entry_leafTable {A h : ℕ} (op : Op) {R I : ℕ} (hout : (Shape.leaf A op).1.2 = R)
    (hin : (Shape.leaf A op).1.1 = I) (b : Fin R) (i : Fin I) (y x : Addr A h) :
    entry (I*((4^A)^h)) (leafTable A h op) (bankIndex (pack A h) (b,y)) (bankIndex (pack A h) (i,x)) =
      leafScalar A h op b i (pack A h y) (pack A h x) := by
  let n := (4^A)^h
  have pos : 0 < n := by dsimp [n]; positivity
  have ltidx {K : ℕ} (k : Fin K) (z : Fin n) : k.val*n + z.val < K*n :=
    (Nat.add_lt_add_left z.isLt _).trans_le (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right n k.isLt)
  have dividx {K : ℕ} (k : Fin K) (z : Fin n) : (k.val*n+z.val)/n = k.val := by
    rw [Nat.mul_comm k.val n, Nat.mul_add_div pos, Nat.div_eq_of_lt z.isLt, Nat.add_zero]
  have modidx {K : ℕ} (k : Fin K) (z : Fin n) : (k.val*n+z.val)%n = z.val := by simp [Nat.mod_eq_of_lt z.isLt]
  simp only [leafTable, hout, hin, bankIndex]
  rw [entry_make _ (ltidx b (pack A h y)) (ltidx i (pack A h x)),
    dividx, dividx, modidx, modidx]

private def LeafCorrect {A h : ℕ} (op : Op) (y x : Addr A h) (p : Packed A) : Prop :=
  ∀ (b : Fin p.o) (i : Fin p.i), KernelComputableDyadic.value
    (leafScalar A h op b i (pack A h y) (pack A h x)) = p.plan.eval h (b,y) (i,x)

private theorem value_leafScalar (A h : ℕ) (op : Op) (y x : Addr A h) :
    LeafCorrect op y x (Packed.leaf A op) := by
  unfold Packed.leaf
  split_ifs with mix gor a b scale child ca <;> unfold LeafCorrect
  · intro u v
    simp [leafScalar, mix, Plan.eval, Fin.val_inj, apply_ite KernelComputableDyadic.value, entry]
  · intro u v
    simpa [leafScalar, gor, a, b, Plan.eval] using
      value_xorEntry (⟨_,a⟩ : Fin A) (⟨_,b⟩ : Fin A) y x
  · intro u v
    simp [leafScalar, gor, b, Packed.zeroRow, Plan.eval, value]
  · intro u v
    simp [leafScalar, gor, a, Packed.zeroRow, Plan.eval, value]
  · intro u v
    simpa [leafScalar, scale, Plan.eval] using
      KernelComputableSelector.entry_eval (q := arg op 0) op.2.1.tail op.2.2 y x
  · intro u v
    simpa [leafScalar, child, ca, Plan.eval] using
      value_child (⟨_,ca⟩ : Fin A) y x
  · intro u v
    simp [leafScalar, mix, gor, scale, ca, Packed.zeroRow, Plan.eval, value]
  · intro u
    exact Fin.elim0 u

theorem leafTable_represents (A h : ℕ) (op : Op) :
    (Packed.leaf A op).Represents h (leafTable A h op) := by
  rintro ⟨b,y⟩ ⟨i,x⟩
  have hshape := (Packed.leaf_shape A op).symm
  exact (congrArg KernelComputableDyadic.value (entry_leafTable op
    (congrArg (fun s : Shape => s.1.2) hshape) (congrArg (fun s : Shape => s.1.1) hshape) b i y x)).trans
    (value_leafScalar A h op y x b i)

end KernelPass.ComputableSyntax

end NearSquareRoot
end Computability
end OAI
