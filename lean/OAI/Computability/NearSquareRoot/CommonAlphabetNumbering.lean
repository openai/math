import OAI.Computability.NearSquareRoot.CommonAlphabetMachine
import OAI.Computability.NearSquareRoot.ScheduleProgramReindexRun
import Mathlib.Algebra.BigOperators.Fin

/-! # Effective numbering for the serialized control and its input rows -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet
open IntegerMultiplication
variable {A Q I : Type}

/-- An explicit enumeration, available to the code generator in both directions. -/
structure Numbering (T : Type) where
  size : ℕ
  equiv : T ≃ Fin size

namespace Numbering

variable {G H : Type}

def fin (n : ℕ) : Numbering (Fin n) := ⟨n,Equiv.refl _⟩

def sum (g : Numbering G) (h : Numbering H) : Numbering (Sum G H) :=
  ⟨_,(Equiv.sumCongr g.equiv h.equiv).trans finSumFinEquiv⟩

def prod (g : Numbering G) (h : Numbering H) : Numbering (G × H) :=
  ⟨_,(Equiv.prodCongr g.equiv h.equiv).trans finProdFinEquiv⟩

def arrow (g : Numbering G) (h : Numbering H) : Numbering (G → H) :=
  ⟨_,(Equiv.arrowCongr g.equiv h.equiv).trans finFunctionFinEquiv⟩

def all (g : Numbering G) : List G := (List.finRange g.size).map g.equiv.symm

theorem mem_all (g : Numbering G) (x : G) : x ∈ g.all :=
  List.mem_map.mpr ⟨g.equiv x, by simp, g.equiv.symm_apply_apply _⟩

def ternary : Numbering (Option Bool) :=
  ⟨3, { toFun := fun | none => 0 | some false => 1 | some true => 2
        invFun := ![none, some false, some true]
        left_inv := by rintro (_ | (_ | _)) <;> rfl
        right_inv := by intro i; fin_cases i <;> rfl }⟩

def move : Numbering TM.Move :=
  ⟨3, { toFun := fun | .left => 0 | .stay => 1 | .right => 2
        invFun := ![.left, .stay, .right]
        left_inv := by intro x; cases x <;> rfl
        right_inv := by intro i; fin_cases i <;> rfl }⟩

def mode : Numbering Mode :=
  ⟨3, { toFun := fun | .write => 0 | .align₁ => 1 | .align₂ => 2
        invFun := ![.write, .align₁, .align₂]
        left_inv := by intro x; cases x <;> rfl
        right_inv := by intro i; fin_cases i <;> rfl }⟩

private def phases (w : ℕ) : PC A Q I w ≃
    (Q × (I → A)) ⊕ (Q × (I → A × TM.Move) × Mode × Fin w) ⊕
    (Q × (I → Letters w) × Fin w) ⊕ (Q × (I → A) × Fin w) where
  toFun
    | .ready q a => .inl (q,a)
    | .work q o m j => .inr (.inl (q,o,m,j))
    | .readBlock q b j => .inr (.inr (.inl (q,b,j)))
    | .rewind q a j => .inr (.inr (.inr (q,a,j)))
  invFun
    | .inl (q,a) => .ready q a
    | .inr (.inl (q,o,m,j)) => .work q o m j
    | .inr (.inr (.inl (q,b,j))) => .readBlock q b j
    | .inr (.inr (.inr (q,a,j))) => .rewind q a j
  left_inv := by intro x; cases x <;> rfl
  right_inv := by rintro (⟨q,a⟩ | ⟨q,o,m,j⟩ | ⟨q,b,j⟩ | ⟨q,a,j⟩) <;> rfl

/-- Product, function and sum numberings give a computable row address for every
possible state, including in-progress reads and writes. -/
def controller (a : Numbering A) (q : Numbering Q) (i : Numbering I) (w : ℕ) :
    Numbering (PC A Q I w) :=
  let pos := fin w
  let cached := i.arrow a
  let actions := i.arrow (a.prod move)
  let buffer := i.arrow (pos.arrow ternary)
  let body := (q.prod cached).sum ((q.prod (actions.prod (mode.prod pos))).sum
    ((q.prod (buffer.prod pos)).sum (q.prod (cached.prod pos))))
  ⟨body.size, (phases w).trans body.equiv⟩

/-- The ROM compiler uses no choice of enumeration. -/
def program (a : Numbering A) (q : Numbering Q) (i : Numbering I) (c : Code A)
    (m : TM.Rule A Q I) (entry : Q) : List (Universal.Tag (Option Bool) I) :=
  Universal.Reindex.encode (controller a q i c.width).equiv
    (readStart c entry) (rule c m) (i.arrow ternary).all

end Numbering
end CommonAlphabet

end NearSquareRoot
end Computability
end OAI
