import OAI.Computability.NearSquareRoot.KernelComputableDyadic
import OAI.Computability.NearSquareRoot.KernelPassCutoff

/-! # Primitive recursive stack syntax for a finite pass description

An instruction stores its tag, natural operands and dyadic coefficients.
The two binary constructors consume the top two entries on the parse stack.
The list is in prefix order and is read from right to left.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.ComputableSyntax

open KernelComputableDyadic

abbrev Op := ℕ × List ℕ × List Code

def arg (op : Op) (k : ℕ) : ℕ := op.2.1.getD k 0

theorem primrec_arg : Primrec₂ arg :=
  (Primrec.list_getD 0).comp ((Primrec.fst.comp Primrec.snd).comp Primrec.fst) Primrec.snd

structure Algebra (σ : Type*) where
  empty : σ
  leaf : Op → σ
  seq : σ → σ → σ
  parallel : σ → σ → σ

def Algebra.step {σ : Type*} (a : Algebra σ) (op : Op) (stack : List σ) : List σ :=
  let l := stack.getD 0 a.empty
  let r := stack.getD 1 a.empty
  if op.1 = 4 then a.seq l r :: stack.drop 2
  else if op.1 = 5 then a.parallel l r :: stack.drop 2
  else a.leaf op :: stack

def Algebra.parse {σ : Type*} (a : Algebra σ) (ops : List Op) : σ :=
  (ops.foldr a.step []).getD 0 a.empty

theorem foldr_map {σ τ : Type*} {a : Algebra σ} {b : Algebra τ} (f : σ → τ)
    (h₀ : f a.empty = b.empty) (h₁ : ∀ k, f (a.leaf k) = b.leaf k)
    (h₂ : ∀ l r, f (a.seq l r) = b.seq (f l) (f r))
    (h₃ : ∀ l r, f (a.parallel l r) = b.parallel (f l) (f r))
    (ops : List Op) (s : List σ) :
    (ops.foldr a.step s).map f = ops.foldr b.step (s.map f) := by
  induction ops with
  | nil => rfl
  | cons op rest ih =>
    rw [List.foldr_cons, List.foldr_cons, ← ih]
    generalize rest.foldr a.step s = stack
    by_cases h4 : op.1 = 4 <;> by_cases h5 : op.1 = 5 <;>
      cases stack with
      | nil => simp [Algebra.step, *]
      | cons x xs => cases xs <;> simp [Algebra.step, *]

theorem parse_map {σ τ : Type*} {a : Algebra σ} {b : Algebra τ} (f : σ → τ)
    (h₀ : f a.empty = b.empty) (h₁ : ∀ k, f (a.leaf k) = b.leaf k)
    (h₂ : ∀ l r, f (a.seq l r) = b.seq (f l) (f r))
    (h₃ : ∀ l r, f (a.parallel l r) = b.parallel (f l) (f r))
    (ops : List Op) : f (a.parse ops) = b.parse ops := by
  have he := foldr_map f h₀ h₁ h₂ h₃ ops []
  simp only [List.map_nil] at he
  rw [Algebra.parse, Algebra.parse, ← he, ← h₀]
  simp [List.getD, List.getElem?_map, Option.getD_map]

/-- A parameterized numerical stack interpreter has a primitive recursive
result as soon as its three finite operations do. -/
theorem primrec_parse {X σ : Type*} [Primcodable X] [Primcodable σ]
    (a : X → Algebra σ) (z : σ) (hz : ∀ x, (a x).empty = z)
    (h₁ : Primrec₂ fun x k => (a x).leaf k)
    (h₂ : Primrec₂ fun x (p : σ × σ) => (a x).seq p.1 p.2)
    (h₃ : Primrec₂ fun x (p : σ × σ) => (a x).parallel p.1 p.2)
    (ops : X → List Op) (ho : Primrec ops) : Primrec fun x => (a x).parse (ops x) := by
  let S := X × Op × List σ
  have hop : Primrec (fun v : S => v.2.1) := Primrec.fst.comp Primrec.snd
  have hs : Primrec (fun v : S => v.2.2) := Primrec.snd.comp Primrec.snd
  have hd := (Primrec.list_drop (α := σ)).comp (Primrec.const 2) hs
  have hc := ((Primrec.list_getD z).comp hs (Primrec.const 0)).pair
    ((Primrec.list_getD z).comp hs (Primrec.const 1))
  have funLeaf := Primrec.list_cons.comp (h₁.comp Primrec.fst hop) hs
  have funSeq := Primrec.list_cons.comp (h₂.comp Primrec.fst hc) hd
  have funPar := Primrec.list_cons.comp (h₃.comp Primrec.fst hc) hd
  have htag : Primrec (fun v : S => v.2.1.1) := Primrec.fst.comp hop
  have step : Primrec₂ (fun x (v : Op × List σ) => (a x).step v.1 v.2) := by
    simpa only [Algebra.step, hz] using
      (Primrec.ite (Primrec.eq.comp htag (.const 4)) funSeq
        (Primrec.ite (Primrec.eq.comp htag (.const 5)) funPar funLeaf)).to₂
  simpa only [Algebra.parse, hz] using
    (Primrec.list_getD z).comp (Primrec.list_foldr ho (Primrec.const []) step) (Primrec.const 0)

end KernelPass.ComputableSyntax

end NearSquareRoot
end Computability
end OAI
