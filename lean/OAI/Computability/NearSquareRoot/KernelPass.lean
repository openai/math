import OAI.Computability.NearSquareRoot.KernelColumn
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.Block

/-! # Binary normalized stream templates at even child widths

A column letter contains two bits of each fixed axis, so a child call on one axis
uses an even number of bits. A program has a fixed number of input and output rows.
Its finite instructions describe particular stream operations and record the number
of calls on individual rows. All address widths use the same instructions. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass

open Matrix Finset

/-- Signed integer numerator and binary fractional width. -/
abbrev Coefficient := ℤ × ℕ

def value (x : Coefficient) : ℚ := (x.1 : ℚ) / 2^x.2

abbrev Column (A : ℕ) := Fin A → Fin 2 → ZMod 2
abbrev Addr (A h : ℕ) := Fin h → Column A
abbrev RowMatrix (A h I O : ℕ) := Matrix (Fin O × Addr A h) (Fin I × Addr A h) ℚ

/-- Primitive plans on a single work row, row combinations, and assembly of work banks. -/
inductive Plan (A : ℕ) : ℕ → ℕ → Type
  | mix {i o} (coeff : Fin o → Fin i → Coefficient) : Plan A i o
  | xor (g : Fin A × Fin A) : Plan A 1 1
  | scale (q : ℕ) (test : Column A → Fin q → ZMod 2)
      (table : (Fin q → ZMod 2) → Coefficient) : Plan A 1 1
  | child (axis : Fin A) : Plan A 1 1
  | seq {i j o} (p : Plan A j o) (q : Plan A i j) : Plan A i o
  | parallel {i j o u} (p : Plan A i o) (q : Plan A j u) : Plan A (i+j) (o+u)

namespace Plan
variable {A i o : ℕ}

def calls {A i o : ℕ} : Plan A i o → ℕ
  | .mix _ | .xor _ | .scale _ _ _ => 0
  | .child _ => 1
  | .seq p q => calls p + calls q
  | .parallel p q => calls p + calls q

end Plan

def xorColumn {A : ℕ} (g : Fin A × Fin A) (x : Column A) : Column A :=
  fun a j => if g.1 ≠ g.2 ∧ a = g.1 then x a j + x g.2 j else x a j

/-- The entry of two normalized binary Walsh factors is always +1/2 or -1/2. -/
def pairEntry (x y : Fin 2 → ZMod 2) : ℚ :=
  if x 0 * y 0 + x 1 * y 1 = 0 then 1/2 else -(1/2)

def childEntry {A : ℕ} (a : Fin A) (y x : Column A) : ℚ :=
  if ∀ b ≠ a, x b = y b then pairEntry (y a) (x a) else 0

/-- Append two row banks without connecting them. -/
def directSum {i j o u : ℕ} {X : Type} (M : Matrix (Fin o × X) (Fin i × X) ℚ)
    (N : Matrix (Fin u × X) (Fin j × X) ℚ) :
    Matrix (Fin (o+u) × X) (Fin (i+j) × X) ℚ :=
  fun ⟨a,y⟩ ⟨b,x⟩ =>
    Fin.addCases (fun l => Fin.addCases (fun k => M (l,y) (k,x)) (fun _ => 0) b)
      (fun r => Fin.addCases (fun _ => 0) (fun k => N (r,y) (k,x)) b) a

def Plan.eval {A i o : ℕ} (h : ℕ) : Plan A i o → RowMatrix A h i o
  | .mix coeff => fun ⟨b,y⟩ ⟨a,x⟩ => if x = y then value (coeff b a) else 0
  | .xor g => fun ⟨_,y⟩ ⟨_,x⟩ => if y = xorColumn g ∘ x then 1 else 0
  | .scale _ test t => fun ⟨_,y⟩ ⟨_,x⟩ =>
      if x = y then value (t (∑ c, test (x c))) else 0
  | .child a => fun ⟨_,y⟩ ⟨_,x⟩ => ∏ c, childEntry a (y c) (x c)
  | .seq p q => p.eval h * q.eval h
  | .parallel p q => directSum (p.eval h) (q.eval h)

/-- Ideal normalized transform on a bank of independent rows. -/
def target (A W h : ℕ) : RowMatrix A h W W :=
  fun ⟨b,y⟩ ⟨a,x⟩ => if a = b then ∏ c, ∏ j, pairEntry (y c j) (x c j) else 0

/-- Every even child width, with the same rational instructions. -/
def Correct {A W : ℕ} (p : Plan A W W) : Prop := ∀ h, p.eval h = target A W h

end KernelPass

end NearSquareRoot
end Computability
end OAI
