import OAI.Computability.NearSquareRoot.InterchangeOpcodeTypes
import OAI.Computability.NearSquareRoot.InterchangeOpcodeRat

/-!
# Primitive-recursive equality test for raw address words

Number first-wing coordinates from `0` to `n-1` and second-wing coordinates
from `n` to `2*n-1`. The interpreter stores one column at a time. Only the
changed coordinates are overwritten. Equality of the two resulting columns
uses the unreduced rational operands' cross products.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Opcode

def index (n : ℕ) (spot : Bool × ℕ) := bif spot.1 then n + spot.2 else spot.2

def coefficient (o : Op) : Scalar := Scalar.ofRaw (negative o) (numerator o) (denominator o)

def step (n : ℕ) (v : List Scalar) (o : Op) : List Scalar :=
  let i := index n (target o)
  let j := index n (source o)
  let a := v.getD i Scalar.zero
  let b := v.getD j Scalar.zero
  if tag o = 0 then v.set i (Scalar.mul (coefficient o) a)
  else if tag o = 1 then v.set i (Scalar.add a (Scalar.mul (coefficient o) b))
  else (v.set i b).set j a

def basis (n j : ℕ) : List Scalar :=
  (List.range (2*n)).map fun i => if j = i then Scalar.one else Scalar.zero

def column (n : ℕ) (w : Word) (j : ℕ) : List Scalar := w.foldl (step n) (basis n j)

def equal (n : ℕ) (p q : Word) : Bool := (List.range (2*n)).all fun j =>
  let a := column n p j
  let b := column n q j
  (List.range (2*n)).all fun i => Scalar.eqb (a.getD i Scalar.zero) (b.getD i Scalar.zero)

variable {X : Type} [Primcodable X]

private theorem pr_index {n : X → ℕ} {a : X → Bool × ℕ} (hn : Primrec n) (ha : Primrec a) :
    Primrec fun x => index (n x) (a x) :=
  Primrec.cond (Primrec.fst.comp ha) (Primrec.nat_add.comp hn (Primrec.snd.comp ha))
    (Primrec.snd.comp ha)

private theorem pr_step {n : X → ℕ} {v : X → List Scalar} {o : X → Op}
    (hn : Primrec n) (hv : Primrec v) (ho : Primrec o) : Primrec fun x => step (n x) (v x) (o x) := by
  have hi := pr_index hn (Primrec.fst.comp (Primrec.snd.comp ho))
  have rest := Primrec.snd.comp (Primrec.snd.comp ho)
  have hj := pr_index hn (Primrec.fst.comp rest)
  have ha := (Primrec.list_getD Scalar.zero).comp hv hi
  have hb := (Primrec.list_getD Scalar.zero).comp hv hj
  have hc := Scalar.primrec_ofRaw.comp (Primrec.snd.comp rest)
  have put {a : X → List Scalar} {i : X → ℕ} {d : X → Scalar}
      (av : Primrec a) (iv : Primrec i) (dv : Primrec d) : Primrec fun x => (a x).set (i x) (d x) :=
    Primrec.list_set.comp av (iv.pair dv)
  exact Primrec.ite (Primrec.eq.comp (Primrec.fst.comp ho) (Primrec.const 0))
    (put hv hi (Scalar.primrec_mul.comp hc ha))
    (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp ho) (Primrec.const 1))
      (put hv hi (Scalar.primrec_add.comp ha (Scalar.primrec_mul.comp hc hb)))
      (put (put hv hi hb) hj ha))

private theorem pr_dimension {n : X → ℕ} (hn : Primrec n) : Primrec fun x => 2*n x :=
  Primrec.nat_mul.comp (Primrec.const 2) hn

private theorem pr_basis {n j : X → ℕ} (hn : Primrec n) (hj : Primrec j) :
    Primrec fun x => basis (n x) (j x) :=
  Primrec.list_map (Primrec.list_range.comp (pr_dimension hn)) (Primrec.ite
    (Primrec.eq.comp (hj.comp Primrec.fst) Primrec.snd) (Primrec.const Scalar.one)
    (Primrec.const Scalar.zero)).to₂

private theorem pr_column {n j : X → ℕ} {w : X → Word} (hn : Primrec n) (hw : Primrec w) (hj : Primrec j) :
    Primrec fun x => column (n x) (w x) (j x) :=
  Primrec.list_foldl hw (pr_basis hn hj) (pr_step (hn.comp Primrec.fst)
    (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

theorem primrec_range_all {n : X → ℕ} {f : X → ℕ → Bool} (hn : Primrec n) (hf : Primrec₂ f) :
    Primrec fun x => (List.range (n x)).all (f x) := by
  have test : Primrec (fun z : List Bool => z.foldr Bool.and true) := Primrec.list_foldr Primrec.id
    (Primrec.const true) (Primrec.and.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  apply (test.comp (Primrec.list_map (Primrec.list_range.comp hn) hf)).of_eq
  intro x
  induction List.range (n x) with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- Uniform in the number of fields, both lengths, and every signed operand. -/
theorem primrec_equal {n : X → ℕ} {p q : X → Word} (hn : Primrec n) (hp : Primrec p) (hq : Primrec q) :
    Primrec fun x => equal (n x) (p x) (q x) := by
  apply primrec_range_all (pr_dimension hn)
  unfold Primrec₂
  have a := pr_column (hn.comp Primrec.fst) (hp.comp Primrec.fst) (Primrec.snd (α:=X) (β:=ℕ))
  have b := pr_column (hn.comp Primrec.fst) (hq.comp Primrec.fst) (Primrec.snd (α:=X) (β:=ℕ))
  exact primrec_range_all (pr_dimension (hn.comp Primrec.fst)) (Scalar.primrec_eqb.comp
    ((Primrec.list_getD Scalar.zero).comp (a.comp Primrec.fst) Primrec.snd)
    ((Primrec.list_getD Scalar.zero).comp (b.comp Primrec.fst) Primrec.snd)).to₂

end Opcode

end NearSquareRoot
end Computability
end OAI
