import OAI.Computability.IntegerMultiplication.Bits.Add
import OAI.Computability.IntegerMultiplication.Partial

/-!
# The data transformation in the schoolbook fallback

The input words are most-significant-bit first. The iteration keeps the unconsumed
multiplier in that order and holds both the multiplicand and the accumulator in
little-endian order for P192's streaming adder. All three boundary operations
are programs of linear cost in the P192 stack language.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Schoolbook

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits

/-- Remaining MSF bits, LE multiplicand, and fixed-width LE accumulator. -/
abbrev State := Word × Word × Word

def start (p : Word × Word) : State :=
  (p.2, p.1.reverse, fill false (ruler (p.1 ++ p.2)))

private def splitWord : Word → Bool × Word
  | [] => (false, [])
  | b :: l => (b, l)

private theorem easy_splitWord : Easy splitWord := by
  have h : splitWord = (fun l => List.casesOn l (false, []) (fun b s => (b,s))) := by
    funext l; cases l <;> rfl
  rw [h]
  exact Easy.listCase (false, []) (Easy.identity (X := Bool × Word))

def next (s : State) : State :=
  let p := splitWord s.1
  let term := bif p.1 then s.2.1 else []
  (p.2, s.2.1, resize (ruler s.2.2, add (false :: s.2.2, term)))

def finish (s : State) : Word := s.2.2.reverse

theorem easy_start : Easy start := by unfold start; fun_prop

theorem easy_next : Easy next := by
  let digitAndTail := fun s : State => splitWord s.1
  have hd : Easy digitAndTail := Easy.fst.compose easy_splitWord
  have term : Easy (fun s : State => bif (digitAndTail s).1 then s.2.1 else []) :=
    (hd.fstCompose.pair (show Easy (fun s : State => s.2.1) by fun_prop)).compose
      (Easy.ifst (Easy.const []) Easy.identity)
  change Easy (fun s : State => ((digitAndTail s).2, s.2.1,
    resize (ruler s.2.2, add (false :: s.2.2, bif (digitAndTail s).1 then s.2.1 else []))))
  exact hd.sndCompose.pair ((show Easy (fun s : State => s.2.1) by fun_prop).pair
    (easy_resize ((show Easy (fun s : State => ruler s.2.2) by fun_prop).pair
      (easy_add ((show Easy (fun s : State => false :: s.2.2) by fun_prop).pair term)))))

theorem easy_finish : Easy finish := by unfold finish; fun_prop

/-- Boundary state after reading the multiplier prefix `p`. -/
def stage (x : Word) (w : ℕ) (p s : Word) : State :=
  (s, x.reverse, phrase w (bitValue x * bitValue p))

private theorem value_bound (x : Word) : bitValue x < 2 ^ x.length := by
  simpa [endianness] using value_lt x.reverse

private theorem product_bound (x p : Word) : bitValue x * bitValue p < 2 ^ (x.length+p.length) := by
  rw [pow_add]
  exact Nat.mul_lt_mul_of_lt_of_le (value_bound x) (value_bound p).le (by positivity)

private theorem product_bound_width (x p : Word) (w : ℕ) (h : x.length+p.length ≤ w) :
    bitValue x * bitValue p < 2 ^ w :=
  (product_bound x p).trans_le (Nat.pow_le_pow_right (by decide) h)

theorem start_eq_stage (x y : Word) : start (x,y) = stage x (x.length+y.length) [] y := by
  unfold start stage
  congr 1
  congr 1
  apply word_inject
  · simp [fill_eq, phrase_length]
  · simp [fill_eq, bitValue]
    rw [value_phrase (by positivity)]

theorem next_stage (x p s : Word) (w : ℕ) (b : Bool)
    (h : x.length + p.length + 1 ≤ w) :
    next (stage x w p (b :: s)) = stage x w (p ++ [b]) s := by
  have h₁ := product_bound_width x p w (by omega)
  have h₂ := product_bound_width x (p ++ [b]) w (by simpa [← Nat.add_assoc] using h)
  unfold next stage splitWord
  dsimp
  congr 1
  congr 1
  have hr (v : Word) : ruler v = tally v.length := by simp [ruler,tally]
  rw [hr,phrase_length]
  change sized w _ = _
  apply word_inject
  · simp [phrase_length]
  · rw [sized_low, value_phrase h₂, add_val, value_cons, value_phrase h₁]
    have hb : bitValue (p ++ [b]) = 2*bitValue p+b.toNat := by simp [bitValue]
    rw [hb] at h₂ ⊢
    rw [endianness x]
    cases b <;> simp [Nat.mul_add, Nat.mul_left_comm, endianness] at h₂ ⊢ <;>
      exact Nat.mod_eq_of_lt (by simpa [Nat.mul_left_comm] using h₂)

/-- Execute any consecutive block of multiplier bits by the same one-step program. -/
theorem iterate_stage (x p block suffix : Word) (w : ℕ)
    (h : x.length + (p.length + block.length) ≤ w) :
    next^[block.length] (stage x w p (block ++ suffix)) =
      stage x w (p ++ block) suffix := by
  induction block generalizing p with
  | nil => simp
  | cons b l ih =>
    simp only [List.cons_append, List.length_cons, Function.iterate_succ_apply]
    rw [next_stage x p _ w b (by simp only [List.length_cons] at h; omega)]
    rw [ih (p := p ++ [b]) (by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h)]
    simp

theorem iterate_start (x y : Word) (k : ℕ) (hk : k ≤ y.length) :
    next^[k] (start (x,y)) = stage x (x.length+y.length) (y.take k) (y.drop k) := by
  have h := iterate_stage x [] (y.take k) (y.drop k) (x.length+y.length)
    (by simp [List.length_take, hk])
  simpa [start_eq_stage, List.length_take, Nat.min_eq_left hk] using h

theorem finished_state (x y : Word) :
    next^[y.length] (start (x,y)) = stage x (x.length+y.length) y [] := by
  rw [start_eq_stage]
  simpa using iterate_stage x [] y [] (x.length+y.length) (by simp)

theorem output_exact (x y : Word) :
    let z := finish (next^[y.length] (start (x,y)))
    z.length = x.length+y.length ∧ bitValue z = bitValue x * bitValue y := by
  simp only [finished_state, finish, stage, List.length_reverse, phrase_length,
    endianness, List.reverse_reverse, true_and]
  exact value_phrase (by simpa [endianness] using product_bound x y)

/-- At every iteration boundary the encoded state occupies at most `8n+5`
symbols for two `n`-bit inputs. -/
theorem size_stage {x p s : Word} {w n : ℕ}
    (hx : x.length ≤ n) (hs : s.length ≤ n) (hw : w ≤ 2*n) :
    Code.size (stage x w p s) ≤ 8*n+5 := by
  simp [stage,size_word,phrase_length]
  omega

theorem size_iterate {x y : Word} {n k : ℕ}
    (hx : x.length ≤ n) (hy : y.length ≤ n) (hk : k ≤ y.length) :
    Code.size (next^[k] (start (x,y))) ≤ 8*n+5 := by
  rw [iterate_start x y k hk]
  exact size_stage hx (by simp; omega) (by omega)

end Schoolbook

end NearSquareRoot
end Computability
end OAI
