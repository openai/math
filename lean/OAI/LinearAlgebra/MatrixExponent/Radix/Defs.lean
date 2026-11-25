import OAI.LinearAlgebra.MatrixExponent.Lookup.Defs
import OAI.LinearAlgebra.MatrixExponent.CompareExchange

/-!
# Stable radix passes with spare slots

A set presence flag denotes an empty slot. Each block receives a
pack's worth of separators for every digit. Stability places these
after the real rows of that digit.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Radix

def Stable {α : Type} {s : ℕ} (d : α → Val (word s)) (xs ys : List α) : Prop :=
  ys.Perm xs ∧ ys.Pairwise (fun i j => d i ≤ d j) ∧
    ∀ k, ys.filter (fun x => d x = k) = xs.filter (fun x => d x = k)

abbrev slot (a : Wire) := Wire.pair .bit a
abbrev aug (s : ℕ) (a : Wire) := Wire.pair (word (s + 1)) (slot a)

def real {α : Type} (xs : List (Bool × α)) : List α :=
  (xs.filter (fun r => !r.1)).map Prod.snd

theorem real_append {α : Type} (xs ys : List (Bool × α)) :
    real (xs ++ ys) = real xs ++ real ys := by simp [real]

def decorate {α : Type} {s : ℕ} (d : α → Val (word s)) (x : Bool × α) :
    Val (word (s + 1)) × (Bool × α) := ((x.1, d x.2), x)

def filler {α : Type} {s : ℕ} (junk : α) (keys : List (Val (word s))) (P e : ℕ) :
    List (Val (word (s + 1)) × (Bool × α)) :=
  keys.flatMap (fun k => List.replicate P ((false, k), true, junk)) ++
    List.replicate e ((true, Lookup.zero s), true, junk)

def homogeneous {α : Type} {s : ℕ} (d : α → Val (word s)) (xs : List α) : Prop :=
  ∀ x ∈ xs, ∀ y ∈ xs, d x = d y

def live {α : Type} (b : List (Bool × α)) : Bool := !(real b).isEmpty

end OAI.LinearAlgebra.MatrixExponent.Radix
