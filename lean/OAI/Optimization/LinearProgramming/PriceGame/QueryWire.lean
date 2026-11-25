import OAI.Optimization.LinearProgramming.RAM.Basic
import OAI.Optimization.LinearProgramming.PriceGame.StatesCost
import Mathlib.Tactic

/-! A concrete self-delimiting binary serialization of designated price queries. The
price encoding keeps the sign, the reduced numerator magnitude, and the positive denominator. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Wire

open States.Cost

/-- Exactly `w` digits in low-to-high order. -/
def digits : ℕ → ℕ → List Bool
  | 0, _ => []
  | w+1, n => decide (n % 2 = 1) :: digits w (n / 2)

def unbits : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * unbits bs

@[simp] theorem digits_length (w n : ℕ) : (digits w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [digits, ih]

theorem digits_roundtrip (w n : ℕ) (hn : n < 2 ^ w) : unbits (digits w n) = n := by
  induction w generalizing n with
  | zero => simp_all [digits, unbits]
  | succ w ih =>
    rw [pow_succ] at hn
    have hd : n / 2 < 2 ^ w := by omega
    simp only [digits, unbits, ih _ hd]
    by_cases h : n % 2 = 1 <;> simp [h] <;> omega

@[simp] theorem unbits_selfWidth (n : ℕ) : unbits (digits (n.log2 + 1) n) = n :=
  digits_roundtrip _ _ Nat.lt_log2_self

/-- Read the leading unary width, then split off precisely that many data bits. -/
def unframeAux : ℕ → List Bool → Option (List Bool × List Bool)
  | _, [] => none
  | k, true :: bs => unframeAux (k + 1) bs
  | k, false :: bs => if k ≤ bs.length then some (bs.take k, bs.drop k) else none

private theorem unframeAux_replicate (n k : ℕ) (bs : List Bool) :
    unframeAux k (List.replicate n true ++ false :: bs) =
      if k + n ≤ bs.length then some (bs.take (k+n), bs.drop (k+n)) else none := by
  induction n generalizing k with
  | zero => simp [unframeAux]
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, unframeAux, ih]
    simp [Nat.add_assoc, Nat.add_comm 1 n]

@[simp] theorem unframe_frame_append (xs ys : List Bool) :
    unframeAux 0 (frame xs ++ ys) = some (xs, ys) := by
  simp [frame, List.append_assoc, unframeAux_replicate]

/-- A reduced rational's numerator and denominator are framed separately. -/
def rational (q : ℚ) : List Bool :=
  decide (q.num < 0) :: (frame (digits (q.num.natAbs.log2+1) q.num.natAbs) ++
    frame (digits (q.den.log2+1) q.den))

/-- Decode one rational as its two reduced integer data and leave following fields untouched. -/
def readRational : List Bool → Option ((ℤ × ℕ) × List Bool)
  | [] => none
  | neg :: rest => do
    let (nb, rest) ← unframeAux 0 rest
    let (db, rest) ← unframeAux 0 rest
    let mag := (unbits nb : ℤ)
    return ((if neg then -mag else mag, unbits db), rest)

theorem rational_roundtrip (q : ℚ) (tail : List Bool) :
    readRational (rational q ++ tail) = some ((q.num, q.den), tail) := by
  have signMagnitude (z : ℤ) : (if z < 0 then -(z.natAbs : ℤ) else (z.natAbs : ℤ)) = z := by
    split <;> omega
  simp [rational, readRational, List.append_assoc]
  simpa using signMagnitude q.num

theorem rational_length (q : ℚ) : (rational q).length = 2 * RAM.ratBits q + 1 := by
  simp [rational, frame, RAM.ratBits]
  omega

/-- Read `n` rational fields. -/
def readMany : ℕ → List Bool → Option (List (ℤ × ℕ) × List Bool)
  | 0, bits => some ([], bits)
  | n+1, bits => do
    let (q, bits) ← readRational bits
    let (qs, bits) ← readMany n bits
    return (q :: qs, bits)

private theorem readMany_roundtrip (xs : List ℚ) (tail : List Bool) :
    readMany xs.length (xs.flatMap rational ++ tail) =
      some (xs.map (fun q => (q.num, q.den)), tail) := by
  induction xs generalizing tail with
  | nil => rfl
  | cons x xs ih =>
    simp [readMany, List.flatMap_cons, List.append_assoc, rational_roundtrip, ih]

/-- The dimension is public, so its root index has fixed width. -/
def query {N : ℕ} (q : Query N) : List Bool :=
  (List.ofFn q.prices).flatMap rational ++ digits (N.log2+1) q.index.val

def readQuery (N : ℕ) (bits : List Bool) : Option (List (ℤ × ℕ) × ℕ) := do
  let (prices, index) ← readMany N bits
  return (prices, unbits index)

theorem query_roundtrip {N : ℕ} (q : Query N) :
    readQuery N (query q) = some ((List.ofFn q.prices).map (fun x => (x.num, x.den)), q.index.val) := by
  have hr := readMany_roundtrip (List.ofFn q.prices) (digits (N.log2+1) q.index.val)
  rw [List.length_ofFn] at hr
  simp [readQuery, query, hr, digits_roundtrip _ _ (q.index.isLt.trans Nat.lt_log2_self)]

/-- The wire format distinguishes all queries, including the designation at equal prices. -/
theorem query_injective (N : ℕ) : Function.Injective (query (N := N)) := by
  intro q r heq
  have decoded := congrArg (readQuery N) heq
  rw [query_roundtrip, query_roundtrip] at decoded
  obtain ⟨hvec, hidx⟩ := Prod.mk.inj (Option.some.inj decoded)
  have hinj : Function.Injective (fun x : ℚ => (x.num, x.den)) :=
    fun _ _ e => Rat.ext (congrArg Prod.fst e) (congrArg Prod.snd e)
  have hp := List.ofFn_injective ((List.map_injective_iff.mpr hinj) hvec)
  have hi : q.index = r.index := Fin.ext hidx
  cases q
  cases r
  cases hp
  cases hi
  rfl

private theorem flatMap_rational_bound (xs : List ℚ) (B : ℕ) (h : ∀ x ∈ xs, RAM.ratBits x ≤ B) :
    (xs.flatMap rational).length ≤ xs.length * (2 * B + 1) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hxs := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    have hx := h x List.mem_cons_self
    change (rational x ++ xs.flatMap rational).length ≤ (xs.length + 1) * (2 * B + 1)
    rw [List.length_append, Nat.succ_mul, Nat.add_comm (xs.length * (2 * B + 1))]
    exact Nat.add_le_add (by rw [rational_length]; omega) hxs

theorem query_length_le {N : ℕ} (q : Query N) (B : ℕ) (h : ∀ i, RAM.ratBits (q.prices i) ≤ B) :
    (query q).length ≤ N * (2 * B + 1) + (N.log2 + 1) := by
  have hs := flatMap_rational_bound (List.ofFn q.prices) B (fun r hr => by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    exact h i)
  simp only [query, List.length_append, digits_length, List.length_ofFn] at hs ⊢
  omega

end Wire
end PriceGame
end LinearProgramming
end Optimization
end OAI
