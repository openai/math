import OAI.Computability.BorderVNP.PackedSewnFragmentPairGate

/-! # Compatibility test for two physical exterior fragments

The adder may wrap on an inactive slot. Its result is tested as an address
only when the left slot is live and, for source addresses, actually sourced.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.Fragment.PairGate

open VPVNP.VerifierNetwork ParseBatchSort
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open private eqWord_eval from OAI.Computability.BorderVNP.ParseBatchRowFrame

variable {w : ℕ}

private theorem loaded_bit (x : Raw w → Bool) (i : Mid w) :
    (loaded w).eval x i = (loadBit i).eval x := by
  rw [loaded, Frame.step_eval]
  exact congrArg ((loadBit i).eval) (funext (Frame.initial_eval id x))

private theorem flag_value (x : Raw w → Bool) (b t : Bool) :
    (flag b t).eval ((loaded w).eval x) = x (b,.inl t) :=
  loaded_bit x (.inl (b,.inl t))

private theorem raw_value (x : Raw w → Bool) (b : Bool) (k : Fin 4) :
    wordValue ((loaded w).eval x) (rawWord b k) = word (fun j => x (b,j)) k := by
  apply congrArg value
  exact funext fun j => loaded_bit x (.inl (b,.inr (k,j)))

/-- A representable staged sum decodes to the full sum of its two original fields. -/
theorem sum_value (x : Raw w → Bool) (k : Fin 3)
    (h : word (fun j => x (false,j)) k.succ + word (fun j => x (decide (k=1),j)) 2 < 2^w) :
    wordValue ((loaded w).eval x) (sumWord k) =
      word (fun j => x (false,j)) k.succ + word (fun j => x (decide (k=1),j)) 2 := by
  calc
    _ = wordValue x (addWord (inputWord false k.succ) (inputWord (decide (k=1)) 2)) := by
      apply congrArg value
      exact funext fun j => loaded_bit x (.inr (k,j))
    _ = _ := addWord_value x _ _ h

private theorem sameSource_iff (x : Raw w → Bool)
    (fit : (parseRow (fun j => x (false,j))).Fits w) :
    sameSource.eval ((loaded w).eval x) = true ↔
      (parseRow (fun j => x (false,j))).run.source.map
        (· + (parseRow (fun j => x (false,j))).run.width) =
      (parseRow (fun j => x (true,j))).run.source := by
  simp only [sameSource, StatementCircuit.Expr.eval, Bool.or_eq_true, Bool.and_eq_true,
    Bool.not_eq_true', flag_value, eqWord_eval, raw_value, parseRow]
  by_cases hl : x (false,.inl true) = true
  · by_cases hr : x (true,.inl true) = true
    · have hs := fit.2 (word (fun j => x (false,j)) 3) (by simp [parseRow,hl])
      simp [hl,hr,sum_value x 2 hs]
    · simp [hl,hr]
  · by_cases hr : x (true,.inl true) = true <;> simp [hl,hr,Bool.eq_false_iff]

/-- The physical Boolean test recognizes exactly two live compatible fragments. -/
theorem merge_iff (x : Raw w → Bool)
    (fits : ∀ b : Bool, ∀ a ∈ read (fun j => x (b,j)), a.Fits w) :
    merge.eval ((loaded w).eval x) = true ↔
      x (false,.inl false) = true ∧ x (true,.inl false) = true ∧
      (parseRow (fun j => x (false,j))).compatible (parseRow (fun j => x (true,j))) := by
  simp only [merge, StatementCircuit.Expr.eval, Bool.and_eq_true, flag_value, eqWord_eval,
    raw_value]
  by_cases hl : x (false,.inl false) = true
  · have hf := fits false (parseRow (fun j => x (false,j))) (by simp [read,hl])
    rw [sum_value x 0 hf.1, sameSource_iff x hf]
    rfl
  · simp [hl]

end Packing.SewnField.Fragment.PairGate

end BorderVNP
end Computability
end OAI
