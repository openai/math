import OAI.Computability.NearSquareRoot.CommonAlphabetNumbering
import OAI.Computability.NearSquareRoot.CommonAlphabetExpand
import OAI.Computability.NearSquareRoot.CommonAlphabetIO
import OAI.Computability.NearSquareRoot.CommonAlphabetAlign

/-! # Constructive row addresses for the public input and output adapters -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet.Numbering

variable {A M J : Type}

/-- Transport row addresses through an explicitly given equivalence. -/
def ofEquiv {X Y : Type} (e : X ≃ Y) (y : Numbering Y) : Numbering X :=
  ⟨y.size,e.trans y.equiv⟩

def unit : Numbering Unit := ⟨1,finOneEquiv.symm⟩

def bool : Numbering Bool := ⟨2,finTwoEquiv.symm⟩

def option {X : Type} (x : Numbering X) : Numbering (Option X) :=
  ⟨x.size+1, (Equiv.optionCongr x.equiv).trans (finSuccEquiv x.size).symm⟩

/-- The four public letters, including the separator in the extra `some none` cell. -/
def publicLetter : Numbering (Option (Option Bool)) := option ternary

private def expandEquiv (w : ℕ) :
    Expand.Phase A w ≃ Option (Option (Option ((A × Fin w) ⊕ Fin w))) where
  toFun
    | .scan => none
    | .back => some none
    | .done => some (some none)
    | .emit x j => some (some (some (.inl (x,j))))
    | .skip j => some (some (some (.inr j)))
  invFun
    | none => .scan
    | some none => .back
    | some (some none) => .done
    | some (some (some (.inl (x,j)))) => .emit x j
    | some (some (some (.inr j))) => .skip j
  left_inv := by intro x; cases x <;> rfl
  right_inv := by rintro (_ | (_ | (_ | (⟨x,j⟩ | j)))) <;> rfl

def expand (a : Numbering A) (w : ℕ) : Numbering (Expand.Phase A w) :=
  ofEquiv (expandEquiv w) ((((a.prod (fin w)).sum (fin w)).option).option.option)

private def compactEquiv (w : ℕ) :
    Compact.Phase w ≃ Option (Option (((Letters w) × Fin w) ⊕ (Option Bool) ⊕ Fin w)) where
  toFun
    | .prev => none
    | .done => some none
    | .scan bits j => some (some (.inl (bits,j)))
    | .emit bit => some (some (.inr (.inl bit)))
    | .back j => some (some (.inr (.inr j)))
  invFun
    | none => .prev
    | some none => .done
    | some (some (.inl (bits,j))) => .scan bits j
    | some (some (.inr (.inl bit))) => .emit bit
    | some (some (.inr (.inr j))) => .back j
  left_inv := by intro x; cases x <;> rfl
  right_inv := by rintro (_ | (_ | (⟨bits,j⟩ | bit | j))) <;> rfl

def compact (w : ℕ) : Numbering (Compact.Phase w) :=
  let pos := fin w
  let bits := pos.arrow ternary
  ofEquiv (compactEquiv w) (((bits.prod pos).sum (ternary.sum pos)).option.option)

private def alignEquiv (Q : Type) : Align.Phase Q ≃ Option (Option ((Q × Bool) ⊕ Bool)) where
  toFun
    | .boot => none
    | .done => some none
    | .run q neg => some (some (.inl (q,neg)))
    | .rewind neg => some (some (.inr neg))
  invFun
    | none => .boot
    | some none => .done
    | some (some (.inl (q,neg))) => .run q neg
    | some (some (.inr neg)) => .rewind neg
  left_inv := by intro x; cases x <;> rfl
  right_inv := by rintro (_ | (_ | (⟨q,b⟩ | b))) <;> rfl

def align {Q : Type} (q : Numbering Q) : Numbering (Align.Phase Q) :=
  ofEquiv (alignEquiv Q) (((q.prod bool).sum bool).option.option)

/-- Physical input and output heads accompany the candidate's tape bank. -/
def publicIndex (j : Numbering J) : Numbering (Bool ⊕ J) := bool.sum j

/-- Row addresses of the expansion, candidate run, and compaction in sequence. -/
def pipeline (a : Numbering A) (m : Numbering M) (w : ℕ) :
    Numbering ((Expand.Phase A w ⊕ M) ⊕ Compact.Phase w) :=
  ((expand a w).sum m).sum (compact w)

end CommonAlphabet.Numbering

end NearSquareRoot
end Computability
end OAI
