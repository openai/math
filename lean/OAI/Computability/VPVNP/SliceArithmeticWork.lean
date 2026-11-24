import OAI.Computability.VPVNP.SliceArithmeticMul

/-!
# Coefficient streams for multiplication in the advised field

One Horner round scans the accumulator, modulus and multiplier in increasing
degree order. The preceding accumulator limb supplies the shift. Its last limb
supplies the reduction coefficient for the whole round. The scan records the
number of prime-residue additions, multiplications and negations performed.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmetic.Stream

open VPVNP.SliceArithmetic

variable {p e : ℕ} [NeZero p]

/-- Live streams in a Horner round. The output grows in reverse order. -/
structure ScanState (p : ℕ) where
  /-- Remaining low-degree-first coefficients of the monic modulus below its leading term. -/
  modulus : List (Fin p)
  /-- Remaining low-degree-first coefficients of the multiplier. -/
  multiplier : List (Fin p)
  /-- Remaining coefficients of the accumulator from the preceding Horner round. -/
  accumulator : List (Fin p)
  /-- Newly computed coefficients stored in reverse degree order during the scan. -/
  output : List (Fin p)
  /-- Old accumulator limb carried forward for the polynomial shift. -/
  previous : Fin p
  /-- Number of prime-residue operations charged so far in the coefficient scan. -/
  work : ℕ

/-- One row consumes one limb of each input. The two products and two sums
are operations in the prime residue ring. -/
def step (digit reduction : Fin p) (s : ScanState p) : ScanState p :=
  match s.modulus, s.multiplier, s.accumulator with
  | c :: cs, b :: bs, v :: vs =>
      ⟨cs, bs, vs, (s.previous + reduction * c + digit * b) :: s.output, v, s.work + 4⟩
  | _, _, _ => s

/-- A tail-recursive scan with one transition per coefficient. -/
def run (digit reduction : Fin p) : ℕ → ScanState p → ScanState p
  | 0, s => s
  | n + 1, s => run digit reduction n (step digit reduction s)

/-- Count the live limbs of the scan, including the digit and reduction coefficient. -/
def ScanState.limbs (s : ScanState p) : ℕ :=
  s.modulus.length + s.multiplier.length + s.accumulator.length + s.output.length + 3

omit [NeZero p] in
theorem step_limbs_le (digit reduction : Fin p) (s : ScanState p) :
    (step digit reduction s).limbs ≤ s.limbs := by
  rcases s with ⟨c, b, v, out, prev, work⟩
  cases c <;> cases b <;> cases v <;> simp [step, ScanState.limbs]
  omega

omit [NeZero p] in
theorem run_limbs_le (digit reduction : Fin p) (k : ℕ) (s : ScanState p) :
    (run digit reduction k s).limbs ≤ s.limbs := by
  induction k generalizing s with
  | zero => exact le_rfl
  | succ k ih => exact (ih _).trans (step_limbs_le ..)

/-- Coordinates of a shift, seeded with an arbitrary preceding limb. -/
def shift {p : ℕ} (previous : Fin p) : {k : ℕ} → Vector p k → Vector p k
  | 0, v => v
  | _ + 1, v => Fin.cons previous fun j => v j.castSucc

omit [NeZero p] in
private theorem shift_tail {k : ℕ} (previous : Fin p) (v : Vector p (k + 1)) (i : Fin k) :
    shift previous v i.succ = shift (v 0) (fun j : Fin k => v j.succ) i := by
  cases k with
  | zero => exact i.elim0
  | succ k =>
    induction i using Fin.cases with
    | zero => simp [shift]
    | succ i => simp [shift]

omit [NeZero p] in
theorem scan_output {k : ℕ} (digit reduction previous : Fin p)
    (c b v : Vector p k) (out : List (Fin p)) (work : ℕ) :
    let s := run digit reduction k ⟨List.ofFn c, List.ofFn b, List.ofFn v, out, previous, work⟩
    s.output = (List.ofFn fun i => shift previous v i + reduction * c i + digit * b i).reverse ++ out ∧
      s.work = work + 4 * k := by
  induction k generalizing previous out work with
  | zero => simp [run]
  | succ k ih =>
    rw [List.ofFn_succ (f := c), List.ofFn_succ (f := b), List.ofFn_succ (f := v)]
    dsimp only [run, step]
    rw [List.ofFn_succ, List.reverse_cons, List.append_assoc, List.singleton_append]
    rw [show shift previous v 0 = previous from rfl]
    simp only [shift_tail]
    obtain ⟨hrow, hcost⟩ := ih (v 0) (fun i => c i.succ) (fun i => b i.succ)
      (fun i => v i.succ) ((previous + reduction * c 0 + digit * b 0) :: out) (work + 4)
    exact ⟨hrow, by omega⟩

/-- The counters measure prime-residue operations. Each round starts by
negating the last limb and then executes the row scan. -/
structure ProductState (p : ℕ) where
  /-- Current product accumulator, stored as coefficients in increasing degree order between
  Horner rounds. -/
  coefficients : List (Fin p)
  /-- Cumulative prime-residue operation count across completed Horner rounds. -/
  work : ℕ

/-- Process one Horner digit using the negated top accumulator coefficient for reduction, then
reverse the new coefficient list. -/
def round (c b : List (Fin p)) (s : ProductState p) (digit : Fin p) : ProductState p :=
  let scanned := run digit (-s.coefficients.getLastD 0) c.length
    ⟨c, b, s.coefficients, [], 0, s.work + 1⟩
  ⟨scanned.output.reverse, scanned.work⟩

theorem round_correct (c b v : Vector p e) (digit : Fin p) (work : ℕ) :
    round (List.ofFn c) (List.ofFn b) ⟨List.ofFn v, work⟩ digit =
      ⟨List.ofFn (add (companion c v) (scale digit b)), work + (4 * e + 1)⟩ := by
  unfold round
  rw [List.length_ofFn]
  obtain ⟨hout, hwork⟩ := scan_output digit (-(List.ofFn v).getLastD 0) 0 c b v [] (work + 1)
  dsimp only
  rw [hout, hwork, List.append_nil, List.reverse_reverse]
  congr 1
  · congr 1
    funext i
    cases e with
    | zero => exact i.elim0
    | succ k =>
      have hlast : (List.ofFn v).getLastD 0 = v (Fin.last k) := by
        rw [List.ofFn_succ']
        simp
      rw [hlast]
      rfl
  · omega

/-- The machine reads Horner digits from the highest degree down. -/
def product (c a b : List (Fin p)) : ProductState p :=
  a.reverse.foldl (round c b) ⟨List.replicate c.length 0, 0⟩

private theorem fold_digits (c b : Vector p e) (digits : List (Fin p)) :
    digits.reverse.foldl (round (List.ofFn c) (List.ofFn b)) ⟨List.ofFn (zero p e), 0⟩ =
      ⟨List.ofFn (horner c b digits), digits.length * (4 * e + 1)⟩ := by
  induction digits with
  | nil => simp [horner]
  | cons digit digits ih =>
    rw [List.reverse_cons, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, round_correct, List.length_cons, Nat.succ_mul]
    rfl

/-- The complete stream multiplier returns the Horner product, performing
exactly `e * (4 * e + 1)` prime-residue operations. -/
theorem product_correct (c a b : Vector p e) :
    product (List.ofFn c) (List.ofFn a) (List.ofFn b) =
      ⟨List.ofFn (mul c a b), e * (4 * e + 1)⟩ := by
  unfold product
  have hz : List.ofFn (zero p e) = List.replicate e (0 : Fin p) := List.ofFn_const e 0
  rw [List.length_ofFn, ← hz, mul]
  simpa only [List.length_ofFn] using fold_digits c b (List.ofFn a)

/-- Count the three persistent input lists conservatively in addition to all
live scan limbs. The bound holds after any number of steps of any round. -/
theorem scan_bits_le (c b v : Vector p e) (remaining : List (Fin p)) (h : remaining.length ≤ e)
    (digit reduction : Fin p) (k work : ℕ) :
    ((List.ofFn c).length + (List.ofFn b).length + remaining.length +
      (run digit reduction k ⟨List.ofFn c, List.ofFn b, List.ofFn v, [], 0, work⟩).limbs) *
      Nat.clog 2 p ≤ (6 * e + 3) * Nat.clog 2 p := by
  apply Nat.mul_le_mul_right
  have hscan := run_limbs_le digit reduction k
    (⟨List.ofFn c, List.ofFn b, List.ofFn v, [], 0, work⟩ : ScanState p)
  simp only [ScanState.limbs, List.length_ofFn, List.length_nil] at hscan ⊢
  omega

end SliceArithmetic.Stream

end VPVNP
end Computability
end OAI
