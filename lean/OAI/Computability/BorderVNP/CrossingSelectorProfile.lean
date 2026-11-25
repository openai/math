import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Histogram wiring for a sum of network tensors

For a fixed histogram, each term has its own bank of copies. Within that
bank both ends of each cable use the increasing order of occurrences.
A binary selector specifies the word once and is copied on every spoke
from the origin. This section verifies the contraction of this wiring
in Definition 3.1 and Lemma 3.3 of the border-circuit manuscript.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Profile

variable {A j : ℕ} {P : Type*}

/-- Copies assigned to the selected term. -/
def positions (w : Fin j → Fin A) (a : Fin A) : Finset (Fin j) :=
  Finset.univ.filter fun i => w i = a

/-- Multiplicity of each term in the selector word. -/
def histogram (w : Fin j → Fin A) (a : Fin A) : ℕ := (positions w a).card

/-- The external slots for term `a`, indexed in increasing occurrence order.
All internal ports of this term use the same ordinal indices. -/
def slots (w : Fin j → Fin A) (a : Fin A) {p : Fin A → ℕ} (h : histogram w = p) :
    Fin (p a) ≃o positions w a :=
  (positions w a).orderIsoOfFin (congrFun h a)

/-- The total width of any family of term cables is an integral linear
function of the specified histogram. -/
theorem cableWidth (w : Fin j → Fin A) {p : Fin A → ℕ} (h : histogram w = p)
    (width : Fin A → ℕ) :
    ∑ i, width (w i) = ∑ a, p a * width a := by
  subst p
  simpa [histogram, positions, nsmul_eq_mul] using
    (Finset.sum_fiberwise' Finset.univ w width).symm

/-- A fixed-width selector code using ordinary binary digits. -/
def encode (a : Fin A) : Fin (Nat.clog 2 A) → Fin 2 :=
  finFunctionFinEquiv.symm (a.castLE (Nat.le_pow_clog (by decide : 1 < 2) A))

/-- Reject a word if any block decodes to an unused term number. -/
def decode (s : Fin j → Fin (Nat.clog 2 A) → Fin 2) : Option (Fin j → Fin A) :=
  if h : ∀ i, (finFunctionFinEquiv (s i)).val < A then
    some (fun i => ⟨_, h i⟩)
  else none

/-- Each word has a unique valid fixed-width bit encoding. -/
theorem decode_eq_some_iff (s : Fin j → Fin (Nat.clog 2 A) → Fin 2) (w : Fin j → Fin A) :
    decode s = some w ↔ s = fun i => encode (w i) := by
  constructor
  · intro hs
    unfold decode at hs
    split at hs
    next h =>
      have heq := Option.some.inj hs
      funext i
      apply finFunctionFinEquiv.injective
      apply Fin.ext
      simpa [encode] using congrArg Fin.val (congrFun heq i)
    next => contradiction
  · rintro rfl
    simp [decode, encode]

/-- Broadcast the same valid bit word from the origin to every terminal. -/
def broadcast (w : Fin j → Fin A) : P → Fin j → Fin (Nat.clog 2 A) → Fin 2 :=
  fun _ i => encode (w i)

/-- The origin checks equality of the selector spokes and decodes one of them. -/
def readSpokes [Fintype P] (first : P) (s : P → Fin j → Fin (Nat.clog 2 A) → Fin 2) :
    Option (Fin j → Fin A) :=
  if ∀ u, s u = s first then decode (s first) else none

/-- The origin accepts precisely one assignment of selector bits per word. -/
theorem readSpokes_eq_some_iff [Fintype P] (first : P)
    (s : P → Fin j → Fin (Nat.clog 2 A) → Fin 2) (w : Fin j → Fin A) :
    readSpokes first s = some w ↔ s = broadcast w := by
  constructor
  · intro h
    unfold readSpokes at h
    split at h
    next hs => exact funext fun u => (hs u).trans ((decode_eq_some_iff _ _).mp h)
    next => contradiction
  · rintro rfl
    rw [readSpokes, ite_eq_left (show ∀ u, broadcast w u = broadcast w first from fun _ => rfl)]
    exact (decode_eq_some_iff _ _).mpr rfl

open scoped Classical in
/-- Contraction over all binary spokes sums each word once, even when
some field-valued local weights cancel. Unused codes contribute zero. -/
theorem sum_readSpokes [Fintype P] {R : Type*} [AddCommMonoid R] (first : P)
    (weight : (Fin j → Fin A) → R) :
    (∑ s, (readSpokes first s).elim 0 weight) = ∑ w, weight w := by
  classical
  have heq (s : P → Fin j → Fin (Nat.clog 2 A) → Fin 2) :
      (readSpokes first s).elim 0 weight =
        ∑ w : Fin j → Fin A, if s = broadcast w then weight w else 0 := by
    cases h : readSpokes first s with
    | none =>
      have hn (w : Fin j → Fin A) : s ≠ broadcast w := fun hs =>
        (by simpa [h] using (readSpokes_eq_some_iff first s w).2 hs)
      simp [hn]
    | some w =>
      have htest (u : Fin j → Fin A) : s = broadcast u ↔ w = u := by
        rw [← readSpokes_eq_some_iff first, h, Option.some.injEq]
      simp [htest]
  simp_rw [heq]
  rw [Finset.sum_comm]
  simp

variable {X R : Type*} [CommSemiring R]

/-- With a fixed histogram each bank contracts its own internal assignments
using the external slots selected by the ordered occurrences. -/
def bankContraction {I : Fin A → Type*} [∀ a, Fintype (I a)] (p : Fin A → ℕ)
    (x : Fin j → X) (table : ∀ a, X → I a → R) (w : Fin j → Fin A) : R :=
  if h : histogram w = p then
    ∑ z : ∀ a, Fin (p a) → I a, ∏ a, ∏ i, table a (x (slots w a h i)) (z a i)
  else 0

/-- The contraction equals the ordinary product of the `j` selected
network tensors on their original external slots. -/
theorem bankContraction_eq {I : Fin A → Type*} [∀ a, Fintype (I a)] (p : Fin A → ℕ)
    (x : Fin j → X) (table : ∀ a, X → I a → R) (w : Fin j → Fin A) :
    bankContraction p x table w =
      if histogram w = p then ∏ i, ∑ z, table (w i) (x i) z else 0 := by
  classical
  unfold bankContraction
  split
  next h =>
    rw [← Fintype.prod_sum (fun (a : Fin A) (z : Fin (p a) → I a) =>
      ∏ i, table a (x (slots w a h i)) (z i))]
    calc
      _ = ∏ a, ∏ i, ∑ z, table a (x (slots w a h i)) z := by
        apply Finset.prod_congr rfl
        intro a _
        exact (Fintype.prod_sum _).symm
      _ = ∏ a, ∏ i ∈ (positions w a), ∑ z, table (w i) (x i) z := by
        apply Finset.prod_congr rfl
        intro a _
        rw [← Finset.prod_coe_sort (positions w a) (fun i => ∑ z, table (w i) (x i) z)]
        apply Fintype.prod_equiv (slots w a h).toEquiv
        intro i
        have hw : w (slots w a h i) = a := (Finset.mem_filter.mp (slots w a h i).property).2
        exact congrArg (fun b => ∑ z, table b (x (slots w a h i)) z) hw.symm
      _ = _ := Finset.prod_fiberwise Finset.univ w _
  next => rfl

open scoped Classical in
/-- The histogram network, including all binary selector spokes and the
ordinal banks of internal assignments, realizes the profile tensor of
Definition 3.1 with no multiplicity factors. -/
theorem profileContraction [Fintype P] {I : Fin A → Type*} [∀ a, Fintype (I a)]
    (first : P) (p : Fin A → ℕ) (x : Fin j → X) (table : ∀ a, X → I a → R) :
    (∑ s, (readSpokes first s).elim 0 (bankContraction p x table)) =
      ∑ w : Fin j → Fin A with histogram w = p, ∏ i, ∑ z, table (w i) (x i) z := by
  rw [sum_readSpokes]
  simp_rw [bankContraction_eq]
  rw [Finset.sum_filter]

end Crossing.Profile

end BorderVNP
end Computability
end OAI
