import OAI.ThreeFlat.Diagonal.LaneCursorLayout
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI
/-! # A unique public address for each XOR mask -/

namespace ThreeFlat.Diagonal.LaneCursor.RowLayout

variable {F : Type*} {p k low o c : ℕ} {N : BitNetwork F p}
variable (P : RowLayout N k low o c)

/-- This bit depends only on the public offset list. -/
def firstMask (off : Fin o → Row k low) (i : Fin o) : Bool :=
  decide (∀ j : Fin o, j < i → off j ≠ off i)

def firstIndex (off : Fin o → Row k low) (i : Fin o) : Fin o :=
  Fin.find (fun j => off j=off i) ⟨i,rfl⟩

theorem first_eq (off : Fin o → Row k low) (i : Fin o) :
    off (firstIndex off i)=off i :=
  Fin.find_spec (p := fun j => off j = off i) ⟨i,rfl⟩

theorem firstIndex_congr (off : Fin o → Row k low) {i j : Fin o} (h : off i=off j) :
    firstIndex off i=firstIndex off j := by
  unfold firstIndex
  simp only [h]

/-- Repeated masks always use their least index. All geometric addresses
and the actual displacement of every wire stay the same. -/
def canonical : RowLayout N k low o c where
  cellAddress := P.cellAddress
  hiddenRow := P.hiddenRow
  pinRow := P.pinRow
  offset := P.offset
  code a := firstIndex P.offset (P.code a)
  reaches a := by
    rw [first_eq P.offset (P.code a)]
    exact P.reaches a

theorem canonical_code_iff (a : Occurrence N) (j : Fin o) :
    P.canonical.code a=j ↔
      firstMask P.offset j=true ∧ P.offset j=P.offset (P.code a) := by
  let i := P.code a
  have spec : P.offset (firstIndex P.offset i)=P.offset i := first_eq _ _
  change firstIndex P.offset i = j ↔ _
  constructor
  · rintro rfl
    refine ⟨?_,spec⟩
    unfold firstMask
    apply decide_eq_true
    intro h earlier equal
    exact Fin.find_min (p:=fun t => P.offset t=P.offset i) ⟨i,rfl⟩ earlier (equal.trans spec)
  · rintro ⟨minimal,hit⟩
    have le : firstIndex P.offset i ≤ j := Fin.find_le_of_pos (p:=fun t=>P.offset t=P.offset i) ⟨i,rfl⟩ hit
    apply le_antisymm le
    apply le_of_not_gt
    intro lt
    unfold firstMask at minimal
    exact (of_decide_eq_true minimal) _ lt (spec.trans hit.symm)

end ThreeFlat.Diagonal.LaneCursor.RowLayout

end OAI
