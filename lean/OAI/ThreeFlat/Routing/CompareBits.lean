import OAI.ThreeFlat.BitNetworkGlue
import OAI.ThreeFlat.LocalTableNetwork
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

namespace OAI
/-! # A linear-size bit network checking the strict order of two unsigned words -/

namespace ThreeFlat.Routing

open TableCompiler
open scoped BigOperators Classical

/-- Value of the low `k` digits of a little-endian stream. -/
def prefixValue (x : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | k + 1 => prefixValue x k + (x k).toNat * 2 ^ k

private theorem prefixValue_lt (x : ℕ → Bool) (k : ℕ) : prefixValue x k < 2 ^ k := by
  induction k with
  | zero => simp [prefixValue]
  | succ k ih =>
    simp only [prefixValue, pow_succ]
    cases x k <;> simp <;> omega

private theorem prefixLT_succ (x y : ℕ → Bool) (k : ℕ) :
    decide (prefixValue x (k + 1) < prefixValue y (k + 1)) =
      (if x k = y k then decide (prefixValue x k < prefixValue y k) else y k) := by
  have hx := prefixValue_lt x k
  have hy := prefixValue_lt y k
  cases X : x k <;> cases Y : y k <;> simp [prefixValue, X, Y] <;> omega

/-- The little-endian word, extended with zero bits above its declared width. -/
def wordDigits {w : ℕ} (x : Fin w → Bool) (i : ℕ) : Bool :=
  if hi : i < w then x ⟨i, hi⟩ else false

/-- The unsigned value of a fixed length word. -/
def wordValue {w : ℕ} (x : Fin w → Bool) : ℕ := prefixValue (wordDigits x) w

/-- The strict comparison bit of a little-endian prefix. -/
def prefixLT {w : ℕ} (x y : Fin w → Bool) (i : Fin (w + 1)) : Bool :=
  decide (prefixValue (wordDigits x) i.val < prefixValue (wordDigits y) i.val)

theorem prefixLT_step {w : ℕ} (x y : Fin w → Bool) (i : Fin w) :
    prefixLT x y i.succ = (if x i = y i then prefixLT x y i.castSucc else y i) := by
  simpa [prefixLT, wordDigits, i.isLt] using prefixLT_succ (wordDigits x) (wordDigits y) i.val

private abbrev CompareGate (w : ℕ) := Option (Option (Fin w))

private def wire {w : ℕ} : CompareGate w → Fin 4 → BitSource (w + 1) (w + w)
  | none => fun _ => .hidden 0
  | some none => fun _ => .hidden (Fin.last w)
  | some (some i) =>
      ![.hidden i.castSucc, .pin (Fin.castAdd w i), .pin (Fin.natAdd w i), .hidden i.succ]

private def compareTable {K : Type*} [Zero K] [One K] {w : ℕ} :
    CompareGate w → (Fin 4 → Bool) → K
  | none, b => if b 0 = false then 1 else 0
  | some none, b => if b 0 = true then 1 else 0
  | some (some _), b => if b 3 = (if b 1 = b 2 then b 0 else b 2) then 1 else 0

/-- One constant-size transition module per bit, with two endpoint tests.
The first word occupies the low block of pins, the second the high block. -/
noncomputable def compareBits (K : Type*) [Zero K] [One K] (w : ℕ) : BitNetwork K (w + w) :=
  BitNetwork.glue (fun g : CompareGate w => localTableNetwork (compareTable g)) wire

theorem compareBits_cells (K : Type*) [Zero K] [One K] (w : ℕ) :
    (compareBits K w).cells = (w + 2) * 96 := by
  simp [compareBits, localTableNetwork_cells, CompareGate]

theorem compareBits_internal (K : Type*) [Zero K] [One K] (w : ℕ) :
    (compareBits K w).internal = (w + 1) + (w + 2) * 80 := by
  simp [compareBits, localTableNetwork_internal, CompareGate]

theorem valid_carries {w : ℕ} (x y : Fin w → Bool) (a : Fin (w+1) → Bool)
    (h0 : a 0 = false)
    (hs : ∀ i : Fin w, a i.succ = (if x i = y i then a i.castSucc else y i)) :
    a = prefixLT x y := by
  funext j
  induction j using Fin.induction with
  | zero => simpa [prefixLT, prefixValue] using h0
  | succ i ih => rw [hs, ih, prefixLT_step]

theorem compareBits_eval {K : Type*} [CommSemiring K] (w : ℕ) (pin : Fin (w+w) → Bool) :
    let x := fun i : Fin w => pin (Fin.castAdd w i)
    let y := fun i : Fin w => pin (Fin.natAdd w i)
    (compareBits K w).eval pin = if wordValue x < wordValue y then 1 else 0 := by
  classical
  dsimp only
  let x := fun i : Fin w => pin (Fin.castAdd w i)
  let y := fun i : Fin w => pin (Fin.natAdd w i)
  rw [compareBits, BitNetwork.glue_eval]
  simp only [localTableNetwork_eval, Fintype.prod_option]
  rw [Finset.sum_eq_single_of_mem (prefixLT x y) (Finset.mem_univ _)]
  · have steps : ∀ i : Fin w, compareTable (some (some i))
          (fun k => (wire (some (some i)) k).read (prefixLT x y) pin) = (1 : K) := by
      intro i
      have h := prefixLT_step x y i
      simpa [compareTable, wire, BitSource.read, x, y] using
        (ite_eq_left h : (if prefixLT x y i.succ =
          (if x i = y i then prefixLT x y i.castSucc else y i) then (1 : K) else 0) = 1)
    simp only [steps, Finset.prod_const_one]
    simp [compareTable, wire, BitSource.read, x, y, prefixLT, wordValue, prefixValue]
  · intro a _ hne
    by_cases hz : a 0 = false
    · obtain ⟨i, hi⟩ : ∃ i : Fin w, a i.succ ≠
          (if x i = y i then a i.castSucc else y i) := by
        by_contra! all
        exact hne (valid_carries x y a hz all)
      have vanish : (∏ j : Fin w, compareTable (some (some j))
          (fun k => (wire (some (some j)) k).read a pin) : K) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simpa [compareTable, wire, BitSource.read, x, y] using
          (ite_eq_right hi : (if a i.succ = (if x i = y i then a i.castSucc else y i) then (1 : K) else 0) = 0)
      simp only [vanish, mul_zero]
    · simp [compareTable, wire, BitSource.read, hz]

end ThreeFlat.Routing

end OAI
