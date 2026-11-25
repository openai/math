import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedTapeWindow
import OAI.Computability.QuantumFactoring.BooleanAlgebra

/-! # Boolean circuit for a tape-window cell

Each indicator for the new symbol reads the three possible predecessor
positions. Work tapes write at the old head before moving, and an inactive
work tape returns the blank symbol.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedProgram

open SignedMachine ExactQuantumFactoring

private def selectDirection {a : ℕ} (sel data : Direction → BooleanNetwork a 1) :
    BooleanNetwork a 1 :=
  ((sel .left).band (data .left)).bor
    (((sel .stay).band (data .stay)).bor ((sel .right).band (data .right)))

private theorem eval_selectDirection {a : ℕ} (sel data : Direction → BooleanNetwork a 1)
    (x : Fin a → Bool) (d : Direction)
    (hs : ∀ k, (sel k).eval x 0 = decide (d = k)) :
    (selectDirection sel data).eval x 0 = (data d).eval x 0 := by
  cases d <;> simp [selectDirection, hs]

private theorem count_selectDirection {a C : ℕ} (sel data : Direction → BooleanNetwork a 1)
    (hs : ∀ d, (sel d).net.count ≤ C) (hd : ∀ d, (data d).net.count ≤ C) :
    (selectDirection sel data).net.count ≤ 6 * C + 11 := by
  simp only [selectDirection, BooleanNetwork.count_bor, BooleanNetwork.count_band]
  grind

variable {n a r : ℕ}
    (previous : Option (Fin n) → Cell (r+1) → Symbol → BooleanNetwork a 1)
    (inputMove : Direction → BooleanNetwork a 1)
    (workMove : Fin n → Direction → BooleanNetwork a 1)
    (workWrite : Fin n → Symbol → BooleanNetwork a 1)
    (active : Fin n → BooleanNetwork a 1)

/-- One next-cell indicator, addressed by tape, window index and symbol. -/
def cellUpdateNet (tape : Option (Fin n)) (i : Cell r) (sym : Symbol) :
    BooleanNetwork a 1 :=
  match tape with
  | none => selectDirection inputMove (fun d => previous none (Cell.previous d i) sym)
  | some j =>
    (active j).mux (selectDirection (workMove j) (fun d =>
      if (Cell.previous d i).position = 0 then workWrite j sym
      else previous (some j) (Cell.previous d i) sym)) (.constant (decide (.blank = sym)))

/-- One-hot control and predecessor-cell inputs implement the selected transition. -/
theorem eval_cellUpdateNet (x : Fin a → Bool) (f : Frame n (r+1)) (m : Move n)
    (tapes : Fin (n+1))
    (hp : ∀ t k v, (previous t k v).eval x 0 = decide (f.cells t k = v))
    (hi : ∀ d, (inputMove d).eval x 0 = decide (m.inputMove = d))
    (hm : ∀ j d, (workMove j d).eval x 0 = decide ((m.work j).2 = d))
    (hw : ∀ j v, (workWrite j v).eval x 0 = decide ((m.work j).1 = v))
    (ha : ∀ j, (active j).eval x 0 = decide (j.val < tapes.val))
    (tape : Option (Fin n)) (i : Cell r) (sym : Symbol) :
    (cellUpdateNet previous inputMove workMove workWrite active tape i sym).eval x 0 =
      decide ((f.advance (m.transition tapes)).cells tape i = sym) := by
  cases tape with
  | none =>
    simp only [cellUpdateNet, Frame.advance, Move.transition, eval_selectDirection _ _ x _ hi]
    exact hp none _ sym
  | some j =>
    simp only [cellUpdateNet, BooleanNetwork.eval_mux, BooleanNetwork.eval_constant,
      ha, Frame.advance, Move.transition]
    by_cases hj : j.val < tapes.val
    · simp only [hj, activeList, List.getElem?_ofFn]
      rw [eval_selectDirection _ _ x _ (hm j)]
      simp only [decide_true, ite_true, dite_true, Fin.castLE_mk]
      by_cases hc : i.position + (m.work j).2.offset = 0
      · simpa [hc] using hw j sym
      · simpa [hc] using hp (some j) (Cell.previous (m.work j).2 i) sym
    · simp [hj, activeList]

/-- The cost of one updated cell depends only on the costs of its inputs. -/
theorem count_cellUpdateNet (C : ℕ)
    (hp : ∀ t k v, (previous t k v).net.count ≤ C)
    (hi : ∀ d, (inputMove d).net.count ≤ C)
    (hm : ∀ j d, (workMove j d).net.count ≤ C)
    (hw : ∀ j v, (workWrite j v).net.count ≤ C)
    (ha : ∀ j, (active j).net.count ≤ C)
    (tape : Option (Fin n)) (i : Cell r) (sym : Symbol) :
    (cellUpdateNet previous inputMove workMove workWrite active tape i sym).net.count ≤
      24 * (C + 1) := by
  cases tape with
  | none =>
    have h := count_selectDirection inputMove (fun d => previous none (Cell.previous d i) sym)
      hi (fun _ => hp _ _ _)
    exact h.trans (by omega)
  | some j =>
    let data (d : Direction) := if (Cell.previous d i).position = 0 then workWrite j sym
      else previous (some j) (Cell.previous d i) sym
    have hd (d : Direction) : (data d).net.count ≤ C := by
      by_cases hc : (Cell.previous d i).position = 0
      · have he : data d = workWrite j sym := by simp only [data, hc, ite_true]
        rw [he]
        exact hw j sym
      · have he : data d = previous (some j) (Cell.previous d i) sym := by
          simp only [data, hc, ite_false]
        rw [he]
        exact hp _ _ _
    have h := count_selectDirection (workMove j) data (hm j) hd
    change ((active j).mux (selectDirection (workMove j) data)
      (.constant (decide (Symbol.blank = sym)))).net.count ≤ _
    simp only [BooleanNetwork.count_mux, BooleanNetwork.count_constant]
    have := ha j
    omega

end SignedProgram

end SpectralBooks
end LinearAlgebra
end OAI
