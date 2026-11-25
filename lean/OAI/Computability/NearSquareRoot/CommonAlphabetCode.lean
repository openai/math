import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.OfFn

/-! # Fixed-width encoding of finite tape alphabets

Every source symbol occupies a nonempty block over the three-symbol tape
alphabet `Option Bool`. A source blank occupies an entirely blank block.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet

structure Code (A : Type) where
  width : ℕ
  pos : 0 < width
  enc : A → Fin width → Option Bool
  dec : (Fin width → Option Bool) → A
  decode_encode : ∀ x, dec (enc x) = x

private def mark {A : Type} {n : ℕ} (e : A ≃ Fin n) (blank x : A)
    (i : Fin n) : Option Bool :=
  if e x ≠ e blank ∧ i = e x then some true else none

/-- An executable one-hot code given addresses for the source symbols. The
decoder scans for a marked position, returning the blank if none is present. -/
def oneHot {A : Type} {n : ℕ} (e : A ≃ Fin n) (blank : A) : Code A where
  width := n
  pos := Nat.zero_lt_of_lt (e blank).isLt
  enc := mark e blank
  dec := fun bits =>
    (((List.finRange n).find? fun i => bits i == some true).map e.symm).getD blank
  decode_encode := by
    intro x
    cases h : (List.finRange n).find? (fun i => mark e blank x i == some true) with
    | none =>
      have hx : x = blank := by
        by_contra hx
        have hn := List.find?_eq_none.mp h (e x) (by simp)
        simp [mark, e.injective.ne hx] at hn
      simpa using hx.symm
    | some i =>
      have hi := List.find?_some h
      have he : i = e x := by
        by_contra hne
        simp [mark, hne] at hi
      simp [he]

@[simp] theorem oneHot_blank {A : Type} {n : ℕ} (e : A ≃ Fin n) (blank : A) :
    (oneHot e blank).enc blank = fun _ => none := by
  funext i
  simp [oneHot, mark]

theorem exists_code {A : Type} [Finite A] (blank : A) :
    ∃ c : Code A, c.enc blank = fun _ => none := by
  let : Fintype A := Fintype.ofFinite A
  exact ⟨oneHot (Fintype.equivFin A) blank, oneHot_blank _ _⟩

namespace Code

/-- The cells occupied by one symbol, in increasing physical address order. -/
def block {A : Type} (c : Code A) (x : A) : List (Option Bool) := List.ofFn (c.enc x)

/-- Concatenate the fixed-width blocks, preserving source order. -/
def encodeList {A : Type} (c : Code A) (xs : List A) : List (Option Bool) :=
  xs.flatMap c.block

variable {A : Type} (c : Code A)

@[simp] theorem length_block (x : A) : (c.block x).length = c.width := by simp [block]

@[simp] theorem encodeList_nil : c.encodeList [] = [] := rfl

@[simp] theorem encodeList_cons (x : A) (xs : List A) :
    c.encodeList (x :: xs) = c.block x ++ c.encodeList xs := rfl

@[simp] theorem encodeList_append (xs ys : List A) :
    c.encodeList (xs ++ ys) = c.encodeList xs ++ c.encodeList ys := by simp [encodeList]

@[simp] theorem length_encodeList (xs : List A) :
    (c.encodeList xs).length = xs.length * c.width := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.succ_mul, Nat.add_comm]

theorem block_blank (blank : A) (hb : c.enc blank = fun _ => none) :
    c.block blank = List.replicate c.width none := by rw [block, hb, List.ofFn_const]

/-- Physical address `q * width + j` carries digit `j` of source symbol `q`. -/
theorem getElem?_encodeList (xs : List A) (q : ℕ) (hq : q < xs.length) (j : Fin c.width) :
    (c.encodeList xs)[q * c.width + j.val]? = some (c.enc xs[q] j) := by
  induction xs generalizing q with
  | nil => simp at hq
  | cons x xs ih =>
    cases q with
    | zero =>
      simp only [encodeList_cons, Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero,
        List.getElem?_append_left (by simp : j.val < (c.block x).length)]
      simp [block]
    | succ q =>
      have ge : (c.block x).length ≤ (q+1) * c.width + j.val := by
        rw [length_block, Nat.succ_mul]
        omega
      rw [encodeList_cons, List.getElem?_append_right ge, length_block,
        Nat.succ_mul, show q * c.width + c.width + j.val - c.width = q * c.width + j.val by omega]
      exact ih _ (Nat.lt_of_succ_lt_succ hq)

/-- Reading the whole physical block and decoding recovers the source symbol. -/
theorem decodeAt_encodeList (xs : List A) (q : ℕ) (hq : q < xs.length) :
    c.dec (fun j => ((c.encodeList xs)[q*c.width+j.val]?).getD none) = xs[q] := by
  simp only [getElem?_encodeList _ _ _ hq, Option.getD_some]
  exact c.decode_encode _

end Code
end CommonAlphabet

end NearSquareRoot
end Computability
end OAI
