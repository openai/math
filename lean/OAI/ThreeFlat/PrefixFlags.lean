import Mathlib.Data.Fintype.Pi

namespace OAI
/-! # Prefix flags for checking the address of a table entry

The flag at position `i` records agreement of all earlier bits. Each flag
after the first can be checked by a three-bit cell.
-/

namespace ThreeFlat.TableCompiler

variable {p : ℕ}

def prefixMatch (x pin : Fin p → Bool) (i : Fin (p + 1)) : Bool :=
  decide (∀ j : Fin p, j.val < i.val → x j = pin j)

@[simp] theorem prefixMatch_zero (x pin : Fin p → Bool) :
    prefixMatch x pin 0 = true := by
  simp [prefixMatch]

theorem prefixMatch_succ (x pin : Fin p → Bool) (j : Fin p) :
    prefixMatch x pin j.succ = (prefixMatch x pin j.castSucc && (pin j == x j)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [prefixMatch, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
    Fin.val_succ, Fin.val_castSucc]
  constructor
  · intro h
    exact ⟨fun k hk ↦ h k (Nat.lt_succ_of_lt hk), (h j (Nat.lt_succ_self _)).symm⟩
  · rintro ⟨h, hj⟩ k hk
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | heq
    · exact h k hlt
    · have hkj : k = j := Fin.ext heq
      simpa only [hkj] using hj.symm

@[simp] theorem prefixMatch_last (x pin : Fin p → Bool) :
    prefixMatch x pin (Fin.last p) = decide (x = pin) := by
  apply Bool.eq_iff_iff.mpr
  simp only [prefixMatch, decide_eq_true_eq, Fin.val_last]
  exact ⟨fun h ↦ funext (fun j ↦ h j j.isLt), fun h j _ ↦ congrFun h j⟩

theorem eq_prefixMatch (x pin : Fin p → Bool) (a : Fin (p + 1) → Bool)
    (hzero : a 0 = true)
    (hsucc : ∀ j : Fin p, a j.succ = (a j.castSucc && (pin j == x j))) :
    a = prefixMatch x pin := by
  funext i
  induction i using Fin.induction with
  | zero => rw [hzero, prefixMatch_zero]
  | succ j ih => rw [hsucc j, prefixMatch_succ, ih]

end ThreeFlat.TableCompiler

end OAI
