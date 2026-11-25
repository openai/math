import OAI.ThreeFlat.RAM.TickGreedyRow
import OAI.ThreeFlat.Diagonal.TickGreedyNested
import OAI.ThreeFlat.Diagonal.TickGreedyWord

namespace OAI
/-! # The native packing update is the greedy schedule on natural numbers -/

namespace ThreeFlat.RAM.TickGreedyNat

open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.TickGreedyReplay TickGreedyRow
open scoped Fin.CommRing

variable {w : ℕ}

def encode (s : Cursor × Cursor) : State w :=
  ⟨(s.1.1 : Word w),(s.1.2 : Word w),(s.2.1 : Word w),(s.2.2 : Word w)⟩

private theorem cast_lt {x y : ℕ} (hx : x < 2^w) (hy : y < 2^w) :
    (x : Word w) < (y : Word w) ↔ x < y := by
  rw [Fin.lt_def,Fin.val_cast_of_lt hx,Fin.val_cast_of_lt hy]

/-- Valid charges never underflow when selecting a fresh group or slot.
The machine's additions and multiplications are exactly the natural scores
reduced to words, and both comparisons compare faithful natural values. -/
theorem update_eq (g s : Cursor) (work pairs J B W gc sc : ℕ)
    (gcfit : gc < 2^w) (scfit : sc < 2^w)
    (gleft : g.2 ≤ gc) (sleft : s.2 ≤ sc)
    (gcell : J*(B*work+W*pairs) ≤ gc) (scell : work ≤ sc) :
    update (encode (w:=w) (g,s)) work pairs J B W gc sc =
      encode (placeBoth gc sc g s (J*(B*work+W*pairs)) work) := by
  let score := J*(B*work+W*pairs)
  have gcw : g.2 < 2^w := lt_of_le_of_lt gleft gcfit
  have scw : s.2 < 2^w := lt_of_le_of_lt sleft scfit
  have cg : score ≤ gc := gcell
  have cw : score < 2^w := lt_of_le_of_lt gcell gcfit
  have ww : work < 2^w := lt_of_le_of_lt scell scfit
  have xs : (J : Word w)*((B : Word w)*(work : Word w)+(W : Word w)*(pairs : Word w)) =
      (score : Word w) := by simp [score]
  change update (encode (w:=w) (g,s)) work pairs J B W gc sc = encode (placeBoth gc sc g s score work)
  simp only [TickGreedyRow.update,encode,xs,cast_lt gcw cw]
  by_cases restart : g.2 < score
  · have overflow : ¬ score ≤ g.2 := Nat.not_le_of_gt restart
    simp [placeBoth,place,restart,overflow,scell,cast_lt scfit ww,
      Nat.not_lt_of_ge scell,Nat.cast_sub cg,Nat.cast_sub scell,Nat.cast_add]
  · have under : score ≤ g.2 := Nat.le_of_not_gt restart
    by_cases fresh : s.2 < work
    · have spill : ¬work ≤ s.2 := Nat.not_le_of_gt fresh
      simp [placeBoth,place,restart,under,cast_lt scw ww,fresh,spill,
        Nat.cast_sub under,Nat.cast_sub scell,Nat.cast_add]
    · have ok := Nat.le_of_not_gt fresh
      simp [placeBoth,place,restart,under,cast_lt scw ww,fresh,ok,
        Nat.cast_sub under,Nat.cast_sub ok]

theorem remaining_le (g s : Cursor) (score work gc sc : ℕ)
    (gl : g.2 ≤ gc) (sl : s.2 ≤ sc) :
    (placeBoth gc sc g s score work).1.2 ≤ gc ∧
    (placeBoth gc sc g s score work).2.2 ≤ sc := by
  simp only [placeBoth,place]
  split_ifs <;> dsimp only <;> omega

end ThreeFlat.RAM.TickGreedyNat

end OAI
