import OAI.Computability.VPVNP.RankQueryStackWords
import OAI.Computability.VPVNP.RankQueryStackField
import OAI.Computability.VPVNP.UniversalCountStackBounds

/-!
# Encoding a Schur continuation as ten registers

The direction distinguishes waiting for the left or right operand. Six registers
hold the parent query, followed by the remaining summand index and two packed
extension-field scalars. The unused left operand in a waiting-left frame is
zero. All numeric registers are little-endian words of a common width.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack

open UniversalCountStack

namespace SchurKey

variable {n U Z : ℕ}

private def bounded (m a : ℕ) : Option (Fin m) := if h : a < m then some ⟨a, h⟩ else none

private theorem bounded_val {m : ℕ} (a : Fin m) : bounded m a.val = some a := by simp [bounded]

/-- Decode the tag, checking all index, block and degree bounds. -/
def readWords (a : Fin 6 → ℕ) : Option (K n U Z) := do
  match a 0 with
  | 0 =>
    let d ← bounded (Nat.clog 2 n + 1) (a 1)
    let u ← bounded (U+1) (a 4)
    let z ← bounded (Z+1) (a 5)
    if h : a 2 + a 3 ≤ n then return .product d ⟨a 2,a 3,h⟩ u z else none
  | 1 => return .factor (← bounded n (a 1)) (← bounded (U+1) (a 4)) (← bounded (Z+1) (a 5))
  | 2 | 3 | 4 =>
    let v ← bounded n (a 1)
    let i ← bounded (n-v.val-1) (a 2)
    let j ← bounded (n-v.val-1) (a 3)
    let h ← bounded (U+1) (a 4)
    let z ← bounded (Z+1) (a 5)
    return if a 0 = 2 then .outer v h i j z else if a 0 = 3 then .inner v h i j z
      else .power v ⟨h,i,j,z⟩
  | 5 => return .scalar (decide (a 3 = 1)) (← bounded n (a 1)) (← bounded n (a 2)) (← bounded (Z+1) (a 5))
  | 6 => return .one
  | _ => none

theorem readWords_words (q : K n U Z) : readWords q.words = some q := by
  cases q with
  | product d b u z => cases b; simp [readWords, words, bounded_val, *]
  | factor | outer | inner | one => simp [readWords, words, bounded_val]
  | power a q => cases q; simp [readWords, words, bounded_val]
  | scalar b i j z => cases b <;> simp [readWords, words, bounded_val]

theorem words_injective : Function.Injective (words (n := n) (U := U) (Z := Z)) := by
  intro a b h
  simpa only [readWords_words, Option.some.injEq] using congrArg (readWords (n := n) (U := U) (Z := Z)) h

/-- One uniform bound on all six query registers, including the empty matrix. -/
theorem words_le (q : K n U Z) (idx : Fin 6) : q.words idx ≤ n + U + Z + 6 := by
  have hd : Nat.clog 2 n ≤ n := Nat.clog_le_of_le_pow (Nat.lt_pow_self (by decide : 1 < 2)).le
  cases q with
  | product d b u z =>
    have := d.isLt; have := b.fits; have := u.isLt; have := z.isLt
    fin_cases idx <;> simp [words] <;> omega
  | factor a u z =>
    have := a.isLt; have := u.isLt; have := z.isLt
    fin_cases idx <;> simp [words] <;> omega
  | outer a h i j z | inner a h i j z =>
    have := a.isLt; have := h.isLt; have := i.isLt; have := j.isLt; have := z.isLt
    fin_cases idx <;> simp [words] <;> omega
  | power a q =>
    have := a.isLt; have := q.exponent.isLt; have := q.row.isLt; have := q.col.isLt; have := q.degree.isLt
    fin_cases idx <;> simp [words] <;> omega
  | scalar b x y z =>
    have := x.isLt; have := y.isLt; have := z.isLt
    cases b <;> fin_cases idx <;> simp [words] <;> omega
  | one => fin_cases idx <;> simp [words]

end SchurKey

namespace Frame

variable {n U Z p e : ℕ} {c : SliceArithmetic.Vector p e}

/-- Evaluator frame specialized to a Schur query key and an encoded extension-field scalar. -/
abbrev SchurFrame (n U Z : ℕ) (c : SliceArithmetic.Vector p e) :=
  Frame (SchurKey n U Z) (Scalar c)

/-- Fields in order: direction, query, remaining summands, accumulator, saved left operand. -/
def words : SchurFrame n U Z c → Fin 10 → ℕ
  | .left q k a => Fin.cons 0 (Fin.append q.words ![k, a.code.val, 0])
  | .right q k a v => Fin.cons 1 (Fin.append q.words ![k, a.code.val, v.code.val])

/-- Remaining product-scan index saved in either kind of Schur frame. -/
def remaining : SchurFrame n U Z c → ℕ
  | .left _ k _ | .right _ k _ _ => k

/-- Width conditions for the exact scalar and control words, with a separate
bound for the summand index supplied by the arity estimate. -/
theorem words_fit (f : SchurFrame n U Z c) (width : ℕ)
    (hq : n + U + Z + 6 < 2^width) (hk : f.remaining < 2^width) (hs : p^e ≤ 2^width) :
    ∀ i, f.words i < 2^width := by
  intro i
  cases f with
  | left q k a =>
    refine Fin.cases (by change 0 < 2^width; exact pow_pos (by decide) _)  (fun j => ?_) i
    refine Fin.addCases (motive := fun i => Fin.append q.words ![k, a.code.val, 0] i < 2^width) (fun x : Fin 6 => ?_) (fun x : Fin 3 => ?_) j
    · simpa [words] using (SchurKey.words_le q x).trans_lt hq
    · have ha := a.code.isLt
      change k < 2^width at hk
      rw [Fin.append_right]
      fin_cases x <;> simp <;> omega
  | right q k a b =>
    refine Fin.cases (by change 1 < 2^width; omega) (fun j => ?_) i
    refine Fin.addCases (motive := fun i => Fin.append q.words ![k, a.code.val, b.code.val] i < 2^width) (fun x : Fin 6 => ?_) (fun x : Fin 3 => ?_) j
    · simpa [words] using (SchurKey.words_le q x).trans_lt hq
    · have ha := a.code.isLt; have hb := b.code.isLt
      change k < 2^width at hk
      rw [Fin.append_right]
      fin_cases x <;> simp <;> omega

/-- All registers use the same width; the tag occupies a register too. -/
def bits (width : ℕ) (f : SchurFrame n U Z c) (i : Fin 10) : List Bool :=
  digits width (f.words i)

theorem bits_value (width : ℕ) (f : SchurFrame n U Z c) (i : Fin 10) (h : f.words i < 2^width) :
    TapeWord.value (f.bits width i) = f.words i := by rw [bits, value_digits, Nat.mod_eq_of_lt h]

theorem words_injective : Function.Injective (words (n := n) (U := U) (Z := Z) (c := c)) := by
  intro a b h
  have tag := congrFun h 0
  have key : ∀ i : Fin 6, a.words (Fin.castAdd 3 i).succ = b.words (Fin.castAdd 3 i).succ := fun i => congrFun h _
  have tail : ∀ j : Fin 3, a.words (Fin.natAdd 6 j).succ = b.words (Fin.natAdd 6 j).succ := fun j => congrFun h _
  cases a <;> cases b <;> simp only [words, Fin.cons_zero, Fin.cons_succ, Fin.append_left, Fin.append_right] at tag key tail
  all_goals first | contradiction | skip
  all_goals
    have eqK := SchurKey.words_injective (funext key)
    have h0 := tail 0
    have h1 := tail 1
    have h2 := tail 2
    simp at h0 h1 h2
    cases eqK; cases h0
    have eqScalar (x y : Scalar c) (h : x.code.val = y.code.val) : x = y := by
      cases x; cases y; congr 1; exact Fin.ext h
    congr 1 <;> first | exact eqScalar _ _ h1 | exact eqScalar _ _ h2

theorem bits_injective_on (width : ℕ) {a b : SchurFrame n U Z c}
    (ha : ∀ i, a.words i < 2^width) (hb : ∀ i, b.words i < 2^width) (h : a.bits width = b.bits width) : a = b := by
  apply words_injective
  funext i
  rw [← bits_value width a i (ha i), ← bits_value width b i (hb i), h]

end Frame

end RankQuery.Stack

end VPVNP
end Computability
end OAI
