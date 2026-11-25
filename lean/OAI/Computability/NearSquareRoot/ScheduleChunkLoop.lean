import OAI.Computability.NearSquareRoot.ScheduleChunkArithmetic
import OAI.Computability.NearSquareRoot.ScheduleChunkCursors

/-!
# Row-major multiplication using a common pair of unary cursors

The accumulator width stays fixed. Each loop body makes one call to a
short multiplier on MSF words extracted from the two little-endian operands.
The iterator below describes the data at successive call boundaries.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ChunkLoop

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits
open ChunkCursor ChunkArithmetic

abbrev Operands := Word × Word
abbrev State := Cursor × Word

/-- Construct the two arguments to the short multiplier. -/
def query (p : Operands × State) : Operands :=
  let c := p.2.1
  (extract (c.1.2,c.2.2.1,p.1.1), extract (c.2.1.2,c.2.2.1,p.1.2))

theorem easy_query : Easy query := by
  unfold query
  exact ((show Easy (fun p : Operands × State => (p.2.1.1.2,p.2.1.2.2.1,p.1.1))
    by fun_prop).compose easy_extract).pair
    ((show Easy (fun p : Operands × State => (p.2.1.2.1.2,p.2.1.2.2.1,p.1.2))
    by fun_prop).compose easy_extract)

/-- Prepare those arguments while keeping the cursor and accumulator. -/
theorem easy_prepare : Easy (fun p : Operands × State => (query p, p.2)) :=
  easy_query.pair Easy.snd

def update (p : State × Word) : State :=
  let c := p.1.1
  (advance c, accumulate (c.1.2 ++ c.2.1.2, p.2, p.1.2))

theorem easy_update : Easy update := by
  unfold update
  exact ((show Easy (fun p : State × Word => p.1.1) by fun_prop).compose easy_advance).pair
    ((show Easy (fun p : State × Word => (p.1.1.1.2 ++ p.1.1.2.1.2,p.2,p.1.2))
    by fun_prop).compose easy_accumulate)

/-- Pure semantics of a single call bracketed by the linear stack programs. -/
def step (shortMul : Operands → Word) (w : Operands) (s : State) : State :=
  update (s, shortMul (query (w,s)))

theorem length_step (shortMul : Operands → Word) (w : Operands) (s : State) :
    (step shortMul w s).2.length = s.2.length := accumulate_length ..

private theorem cursor_iterate (shortMul : Operands → Word) (w : Operands) (s : State) (t : ℕ) :
    ((step shortMul w)^[t] s).1 = advance^[t] s.1 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact congrArg advance ih

theorem length_iterate (shortMul : Operands → Word) (w : Operands) (s : State) (t : ℕ) :
    ((step shortMul w)^[t] s).2.length = s.2.length := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', length_step, ih]

theorem cursor_at_step (shortMul : Operands → Word) (w : Operands) {r : ℕ} (hr : 0 < r)
    (u t : ℕ) (a : Word) :
    ((step shortMul w)^[t] (atPair r u 0 0, a)).1 = atPair r u (t/r) (t%r) := by
  rw [cursor_iterate]
  simpa only [Nat.div_add_mod'] using visit hr u (t/r) (t%r) (Nat.mod_lt t hr)

theorem query_lengths (w : Operands) (s : State) :
    (query (w,s)).1.length = s.1.2.2.1.length ∧
      (query (w,s)).2.length = s.1.2.2.1.length :=
  ⟨extract_length .., extract_length ..⟩

theorem exhausted_iterate (shortMul : Operands → Word) (w : Operands) {r : ℕ}
    (hr : 0 < r) (u t : ℕ) (ht : t ≤ r*r) (a : Word) :
    exhausted ((step shortMul w)^[t] (atPair r u 0 0,a)).1 = decide (t = r*r) := by
  rw [cursor_at_step shortMul w hr u t a]
  apply Bool.eq_iff_iff.mpr
  rw [exhausted_iff, decide_eq_true_eq, Nat.le_div_iff_mul_le hr]
  omega

theorem size_iterate (shortMul : Operands → Word) (w : Operands) {n r t : ℕ}
    (hr : 0 < r) (hrn : r ≤ n) (ht : t ≤ r*r) (a : Word) (ha : a.length ≤ 2*n) :
    Code.size ((step shortMul w)^[t] (atPair r (Uniform.chunkWidth n r) 0 0,a)) ≤ 20*n+13 := by
  let u := Uniform.chunkWidth n r
  have hq : t/r ≤ r := (Nat.div_le_div_right ht).trans (by simp [hr.ne'])
  have hm : t%r ≤ r := (Nat.mod_lt t hr).le
  have hu : u ≤ n :=
    (ceilDiv_le_iff_le_mul hr).2 (Nat.le_mul_of_pos_left n hr)
  have hru : r*u ≤ 2*n := by have := (Uniform.chunkWidth_bounds (n := n) hr).2; dsimp [u]; omega
  have hc := size_atPair hq hm hrn hu hru
  rw [size_prod, cursor_at_step shortMul w hr, size_word, length_iterate]
  dsimp only [u] at hc
  dsimp only
  omega

/-- The additive contribution of digit pair `i,j`. -/
def term (w : Operands) (u i j : ℕ) : ℕ :=
  let b := 2 ^ u
  Uniform.chunkDigit b (value w.1) i * Uniform.chunkDigit b (value w.2) j * b ^ (i+j)

/-- Correctness is only required on the particular common digit width. -/
def ExactAt (shortMul : Operands → Word) (u : ℕ) : Prop :=
  ∀ a b : Word, a.length = u → b.length = u → bitValue (shortMul (a,b)) = bitValue a * bitValue b

theorem value_step_at (shortMul : Operands → Word) (w : Operands) (r u i j : ℕ) (a : Word)
    (h : ExactAt shortMul u) :
    value (step shortMul w (atPair r u i j,a)).2 = (value a + term w u i j) % 2 ^ a.length := by
  let x := extract (tally (i*u),tally u,w.1)
  let y := extract (tally (j*u),tally u,w.2)
  have hx : x.length = u := (extract_length ..).trans (tally_length u)
  have hy : y.length = u := (extract_length ..).trans (tally_length u)
  have hvx := extract_chunkDigit (tally (i*u)) (tally u) w.1 i (by simp)
  have hvy := extract_chunkDigit (tally (j*u)) (tally u) w.2 j (by simp)
  change value (accumulate (tally (i*u) ++ tally (j*u),shortMul (x,y),a)) = _
  rw [accumulate_value, h x y hx hy]
  change bitValue x = _ at hvx
  change bitValue y = _ at hvy
  rw [hvx,hvy]
  simp only [term,tally_length,List.length_append, ← pow_mul]
  rw [Nat.mul_add u, Nat.mul_comm u i, Nat.mul_comm u j, Nat.mul_comm (2^_)]

/-- Every prefix is accumulated modulo the original word width. -/
theorem value_iterate (shortMul : Operands → Word) (w : Operands) {r : ℕ} (hr : 0 < r)
    (u t : ℕ) (a : Word) (h : ExactAt shortMul u) :
    value ((step shortMul w)^[t] (atPair r u 0 0,a)).2 =
      (value a + ∑ k ∈ Finset.range t, term w u (k/r) (k%r)) % 2 ^ a.length := by
  induction t with
  | zero => simp [Nat.mod_eq_of_lt (value_lt a)]
  | succ t ih =>
    let current := (step shortMul w)^[t] (atPair r u 0 0,a)
    have hc : current.1 = atPair r u (t/r) (t%r) := cursor_at_step shortMul w hr u t a
    have hl : current.2.length = a.length := length_iterate shortMul w _ t
    rw [Function.iterate_succ_apply', Finset.sum_range_succ]
    change value (step shortMul w current).2 = _
    have hs : current = (atPair r u (t/r) (t%r),current.2) := Prod.ext hc rfl
    conv_lhs => rw [hs]
    rw [value_step_at _ _ _ _ _ _ _ h, hl]
    change value current.2 = _ at ih
    rw [ih,Nat.mod_add_mod, Nat.add_assoc]

private theorem sum_rows {r : ℕ} (hr : 0 < r) (f : ℕ → ℕ → ℕ) (i : ℕ) :
    ∑ k ∈ Finset.range (i*r), f (k/r) (k%r) =
      ∑ h ∈ Finset.range i, ∑ j ∈ Finset.range r, f h j := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [Nat.mul_comm i r, Nat.mul_add_div hr, Nat.div_eq_of_lt hj', Nat.add_zero,
      Nat.mul_add_mod, Nat.mod_eq_of_lt hj']

/-- `r²` sequential calls recover the exact unpadded product on the MSF interface. -/
theorem output_exact (shortMul : Operands → Word) (x y : Word) {n r : ℕ}
    (hx : x.length = n) (hy : y.length = n) (hr : 0 < r)
    (h : ExactAt shortMul (Uniform.chunkWidth n r)) :
    let u := Uniform.chunkWidth n r
    let z := ((step shortMul (x.reverse,y.reverse))^[r*r]
      (atPair r u 0 0, List.replicate (2*n) false)).2.reverse
    z.length = 2*n ∧ bitValue z = bitValue x * bitValue y := by
  dsimp only
  have bx : value x.reverse < 2 ^ n := by simpa [hx] using value_lt x.reverse
  have by' : value y.reverse < 2 ^ n := by simpa [hy] using value_lt y.reverse
  obtain ⟨hfull,hbound⟩ := Uniform.padded_product hr bx by'
  constructor
  · simp only [List.length_reverse, length_iterate, List.length_replicate]
  · rw [endianness, List.reverse_reverse, value_iterate _ _ hr _ _ _ h, sum_rows hr]
    simp only [zeroes, zero_add, List.length_replicate, term, hfull, Nat.mod_eq_of_lt hbound]
    rw [endianness, endianness y]

end ChunkLoop

end NearSquareRoot
end Computability
end OAI
