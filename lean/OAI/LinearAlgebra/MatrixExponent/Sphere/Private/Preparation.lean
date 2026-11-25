import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset
import OAI.LinearAlgebra.MatrixExponent.Sphere.Interpolation
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import OAI.LinearAlgebra.MatrixExponent.Spectral.Placements

section
/-!
# Fermionic pairing sums

The recursion pairs the first generator with one of the remaining ones.
Moving the partner left by one position changes its sign. Cancellation
of repeated generators uses a square-zero contraction, even in characteristic two.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere

variable {α R : Type*} [CommRing R]

/-- Sum over deletions of one generator, with alternating signs. -/
def contract (f : α → R) (P : List α → R) : List α → R
  | [] => 0
  | x :: xs => f x * P xs - contract f (fun ys => P (x :: ys)) xs

@[simp] theorem contract_nil (f : α → R) (P : List α → R) : contract f P [] = 0 := rfl

theorem contract_cons (f : α → R) (P : List α → R) (x : α) (xs : List α) :
    contract f P (x :: xs) = f x * P xs - contract f (fun ys => P (x :: ys)) xs := rfl

theorem contract_congr {P Q : List α → R} (f : α → R) (xs : List α)
    (h : ∀ ys : List α, ys.length + 1 = xs.length → P ys = Q ys) :
    contract f P xs = contract f Q xs := by
  induction xs generalizing P Q with
  | nil => rfl
  | cons x xs ih =>
    rw [contract_cons, contract_cons, h xs rfl]
    congr 1
    apply ih
    intro ys hy
    exact h _ (by simp [hy])

private def wickAux (k : α → α → R) : ℕ → List α → R
  | _, [] => 1
  | 0, _ :: _ => 0
  | n + 1, x :: xs => contract (k x) (wickAux k n) xs

/-- The signed perfect matching sum in list order. -/
def wick (k : α → α → R) (xs : List α) : R := wickAux k xs.length xs

private theorem wickAux_eq (k : α → α → R) (n : ℕ) (xs : List α) (hn : xs.length ≤ n) :
    wickAux k n xs = wick k xs := by
  induction n using Nat.strong_induction_on generalizing xs with
  | h n ih =>
    cases xs with
    | nil => simp [wickAux, wick]
    | cons x xs =>
      cases n with
      | zero => simp at hn
      | succ n =>
        simp only [wick, List.length_cons, wickAux]
        apply contract_congr
        intro ys hy
        simp only [List.length_cons] at hn
        rw [ih n (by omega) ys (by omega), ih xs.length (by omega) ys (by omega)]

@[simp] theorem wick_nil (k : α → α → R) : wick k [] = 1 := rfl

theorem wick_cons (k : α → α → R) (x : α) (xs : List α) :
    wick k (x :: xs) = contract (k x) (wick k) xs := by
  change contract (k x) (wickAux k xs.length) xs = _
  exact contract_congr _ _ fun ys hy => wickAux_eq k _ ys (by omega)

@[simp] theorem contract_zero (f : α → R) (xs : List α) :
    contract f (fun _ => 0) xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [contract_cons, ih]

theorem contract_scale (f : α → R) (P : List α → R) (c : R) (xs : List α) :
    contract f (fun ys => c * P ys) xs = c * contract f P xs := by
  induction xs generalizing P with
  | nil => simp
  | cons x xs ih =>
    rw [contract_cons, contract_cons, ih (fun ys => P (x :: ys))]
    ring

theorem contract_sub (f : α → R) (P Q : List α → R) (xs : List α) :
    contract f (fun ys => P ys - Q ys) xs = contract f P xs - contract f Q xs := by
  induction xs generalizing P Q with
  | nil => simp
  | cons x xs ih =>
    rw [contract_cons, contract_cons, contract_cons, ih (fun ys => P (x :: ys)) (fun ys => Q (x :: ys))]
    ring

private theorem contract_neg (f : α → R) (P : List α → R) (xs : List α) :
    contract f (fun ys => -P ys) xs = -contract f P xs := by
  simpa using contract_scale f P (-1) xs

private theorem contract_twice (f g : α → R) (P : List α → R) (x : α) (xs : List α) :
    contract f (contract g P) (x :: xs) =
      f x * contract g P xs - g x * contract f P xs +
        contract f (contract g (fun ys => P (x :: ys))) xs := by
  simp only [contract_cons, contract_sub, contract_scale]
  ring

theorem contract_square (f : α → R) (P : List α → R) (xs : List α) :
    contract f (contract f P) xs = 0 := by
  induction xs generalizing P with
  | nil => rfl
  | cons x xs ih => simp only [contract_twice, ih, sub_self, add_zero]

theorem contract_anticomm (f g : α → R) (P : List α → R) (xs : List α) :
    contract f (contract g P) xs = -contract g (contract f P) xs := by
  induction xs generalizing P with
  | nil => simp
  | cons x xs ih => rw [contract_twice, contract_twice, ih]; ring

variable {k : α → α → R}

theorem wick_odd {xs : List α} (h : xs.length % 2 = 1) : wick k xs = 0 := by
  induction hn : xs.length using Nat.strong_induction_on generalizing xs with
  | h n ih =>
    cases xs with
    | nil => simp at h
    | cons x xs =>
      rw [wick_cons, ← contract_zero (k x) xs]
      apply contract_congr
      intro ys hy
      simp only [List.length_cons] at h hn
      exact ih ys.length (by omega) (by omega) rfl

private theorem wick_two (x y : α) (xs : List α) :
    wick k (x :: y :: xs) =
      k x y * wick k xs - contract (k x) (contract (k y) (wick k)) xs := by
  rw [wick_cons, contract_cons, show (fun ys => wick k (y :: ys)) = _ from funext (wick_cons k y)]

private theorem contract_swap (f : α → R) (P : List α → R) (x y : α) (p s : List α)
    (h : ∀ q : List α, q.length ≤ p.length → ∀ t, P (q ++ y :: x :: t) = -P (q ++ x :: y :: t)) :
    contract f P (p ++ y :: x :: s) = -contract f P (p ++ x :: y :: s) := by
  induction p generalizing P with
  | nil =>
    have e : (fun t => P (y :: x :: t)) = (fun t => -P (x :: y :: t)) :=
      funext (h [] le_rfl)
    simp only [List.nil_append, contract_cons, e, contract_neg]
    ring
  | cons z p ih =>
    have e := ih (fun t => P (z :: t)) (fun q hq t => h (z :: q) (by simpa using hq) t)
    simp only [List.cons_append, contract_cons, h p (by simp), e]
    ring

theorem wick_swap (skew : ∀ x y, k y x = -k x y) (p s : List α) (x y : α) :
    wick k (p ++ y :: x :: s) = -wick k (p ++ x :: y :: s) := by
  induction hn : p.length using Nat.strong_induction_on generalizing p s with
  | h n ih =>
    cases p with
    | nil =>
      simp only [List.nil_append, wick_two]
      rw [skew x y, contract_anticomm]
      ring
    | cons z p =>
      simp only [List.cons_append, wick_cons]
      apply contract_swap
      intro q hq t
      exact ih q.length (by simp only [List.length_cons] at hn; omega) q t rfl

private theorem contract_repeat (f : α → R) (P : List α → R) (x : α) (p s : List α)
    (h : ∀ q : List α, q.length ≤ p.length → ∀ t, P (q ++ x :: x :: t) = 0) :
    contract f P (p ++ x :: x :: s) = 0 := by
  induction p generalizing P with
  | nil =>
    have e : (fun t => P (x :: x :: t)) = (fun _ => 0) := funext (h [] le_rfl)
    simp only [List.nil_append, contract_cons, e, contract_zero, sub_zero, sub_self]
  | cons z p ih =>
    have e := ih (fun t => P (z :: t)) (fun q hq t => h (z :: q) (by simpa using hq) t)
    simp only [List.cons_append, contract_cons, h p (by simp), e, mul_zero, sub_self]

private theorem wick_adjacent_repeat (diag : ∀ x, k x x = 0) (p s : List α) (x : α) :
    wick k (p ++ x :: x :: s) = 0 := by
  induction hn : p.length using Nat.strong_induction_on generalizing p s with
  | h n ih =>
    cases p with
    | nil => simp only [List.nil_append, wick_two, diag, zero_mul, contract_square, sub_self]
    | cons z p =>
      simp only [List.cons_append, wick_cons]
      apply contract_repeat
      intro q hq t
      exact ih q.length (by simp only [List.length_cons] at hn; omega) q t rfl

private theorem wick_move (skew : ∀ x y, k y x = -k x y) (p q s : List α) (x : α) :
    wick k (p ++ x :: (q ++ s)) = (-1 : R) ^ q.length * wick k (p ++ (q ++ x :: s)) := by
  induction q generalizing p with
  | nil => simp
  | cons y q ih =>
    have e := ih (p ++ [y])
    simp only [List.append_assoc, List.singleton_append] at e
    rw [List.cons_append, wick_swap skew, e, List.length_cons, pow_succ, List.cons_append]
    ring

theorem wick_repeat (skew : ∀ x y, k y x = -k x y) (diag : ∀ x, k x x = 0)
    (p q s : List α) (x : α) :
    wick k (p ++ x :: (q ++ x :: s)) = 0 := by
  rw [wick_move skew, ← List.append_assoc, wick_adjacent_repeat diag, mul_zero]

theorem wick_swap_blocks (skew : ∀ x y, k y x = -k x y) (p a b s : List α) :
    wick k (p ++ a ++ b ++ s) =
      (-1 : R) ^ (a.length * b.length) * wick k (p ++ b ++ a ++ s) := by
  induction a generalizing p with
  | nil => simp
  | cons x a ih =>
    have e := ih (p ++ [x])
    simp only [List.append_assoc, List.singleton_append] at e
    simp only [List.cons_append] at e
    simp only [List.append_assoc, List.cons_append, List.length_cons, Nat.add_mul, one_mul, pow_add]
    rw [e, wick_move skew, mul_assoc]

/-- Reversing a list exchanges its first and last element, then its second
and penultimate element, and so on. -/
theorem wick_reverse_sign (skew : ∀ x y, k y x = -k x y) (p xs s : List α) :
    wick k (p ++ xs.reverse ++ s) = (-1 : R) ^ (xs.length / 2) * wick k (p ++ xs ++ s) := by
  match xs with
  | [] => simp
  | [_] => simp
  | x :: y :: zs =>
    have e := wick_swap_blocks skew p zs.reverse [y, x] s
    have t := wick_reverse_sign skew (p ++ [y, x]) zs s
    have signo : (-1 : R) ^ (zs.reverse.length * [y, x].length) = 1 := by
      change (-1 : R) ^ (zs.reverse.length * 2) = _
      rw [Nat.mul_comm, pow_mul, neg_one_sq, one_pow]
    rw [signo, one_mul, t] at e
    simp only [List.append_assoc, List.cons_append, List.nil_append] at e
    simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append,
      List.length_cons, show (zs.length + 1 + 1) / 2 = zs.length / 2 + 1 by omega, pow_succ]
    rw [e, wick_swap skew]
    ring

private theorem contract_scale_left (f : α → R) (P : List α → R) (c : R) (xs : List α) :
    contract (fun y => c * f y) P xs = c * contract f P xs := by
  induction xs generalizing P with
  | nil => simp
  | cons x xs ih => rw [contract_cons, contract_cons, ih]; ring

theorem wick_scale_kernel (k : α → α → R) (c : R) (xs : List α) :
    wick (fun x y => c * k x y) xs = c ^ (xs.length / 2) * wick k xs := by
  induction hn : xs.length using Nat.strong_induction_on generalizing xs with
  | h n ih =>
    match xs with
    | [] => subst n; simp
    | [x] => simp [wick_cons]
    | x :: y :: zs =>
      simp only [List.length_cons] at hn
      rw [wick_cons, wick_cons, contract_scale_left]
      have e : contract (k x) (wick (fun x y => c * k x y)) (y :: zs) =
          contract (k x) (fun us => c ^ (zs.length / 2) * wick k us) (y :: zs) := by
        apply contract_congr
        intro us hu
        simp only [List.length_cons] at hu
        exact ih zs.length (by omega) us (by omega)
      rw [e, contract_scale, show n / 2 = zs.length / 2 + 1 by omega, pow_succ', mul_assoc]

theorem wick_reverse (skew : ∀ x y, k y x = -k x y) (xs : List α) :
    wick k xs.reverse = wick (fun x y => -k x y) xs := by
  simpa using (wick_reverse_sign skew [] xs []).trans (by
    simpa using (wick_scale_kernel k (-1) xs).symm)

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

section
/-!
# Splitting a Wick pairing sum

A partial matching contracts some pairs and applies a residual weight to
the unmatched generators in their original order. The decomposition only
uses commutative ring operations.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere

variable {α R : Type*} [CommRing R]

private def partialAux (k : α → α → R) : ℕ → (List α → R) → List α → R
  | 0, P, xs => P xs
  | _ + 1, P, [] => P []
  | n + 1, P, x :: xs => partialAux k n (fun ys => P (x :: ys)) xs +
      contract (k x) (partialAux k n P) xs

/-- Signed sum over partial matchings, weighted by the residual list. -/
def partialWick (k : α → α → R) (P : List α → R) (xs : List α) : R :=
  partialAux k xs.length P xs

private theorem partialAux_eq (k : α → α → R) (P : List α → R)
    (n : ℕ) (xs : List α) (hn : xs.length ≤ n) :
    partialAux k n P xs = partialWick k P xs := by
  induction n using Nat.strong_induction_on generalizing xs P with
  | h n ih =>
    cases xs with
    | nil => cases n <;> rfl
    | cons x xs =>
      cases n with
      | zero => simp at hn
      | succ n =>
        simp only [List.length_cons] at hn
        simp only [partialWick, List.length_cons, partialAux]
        rw [ih n (by omega) _ xs (by omega)]
        congr 1
        apply contract_congr
        intro ys hy
        rw [ih n (by omega) P ys (by omega), ih xs.length (by omega) P ys (by omega)]

@[simp] theorem partialWick_nil (k : α → α → R) (P : List α → R) :
    partialWick k P [] = P [] := rfl

theorem partialWick_cons (k : α → α → R) (P : List α → R) (x : α) (xs : List α) :
    partialWick k P (x :: xs) = partialWick k (fun ys => P (x :: ys)) xs +
      contract (k x) (partialWick k P) xs := by
  change partialWick k _ xs + contract (k x) (partialAux k xs.length P) xs = _
  congr 1
  exact contract_congr _ _ fun ys hy => partialAux_eq k _ _ ys (by omega)

private theorem contract_add (f : α → R) (P Q : List α → R) (xs : List α) :
    contract f (fun ys => P ys + Q ys) xs = contract f P xs + contract f Q xs := by
  induction xs generalizing P Q with
  | nil => simp
  | cons x xs ih =>
    rw [contract_cons, contract_cons, contract_cons,
      ih (fun ys => P (x :: ys)) (fun ys => Q (x :: ys))]
    ring

private theorem contract_add_left (f g : α → R) (P : List α → R) (xs : List α) :
    contract (fun x => f x + g x) P xs = contract f P xs + contract g P xs := by
  induction xs generalizing P with
  | nil => simp
  | cons x xs ih =>
    rw [contract_cons, contract_cons, contract_cons, ih]
    ring

theorem partialWick_linear (k : α → α → R) (P Q : List α → R) (c : R) (xs : List α) :
    partialWick k (fun t => c * P t - Q t) xs =
      c * partialWick k P xs - partialWick k Q xs := by
  induction hn : xs.length using Nat.strong_induction_on generalizing xs P Q with
  | h n ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      simp only [List.length_cons] at hn
      have e := ih xs.length (by omega) (fun t => P (x :: t)) (fun t => Q (x :: t)) xs rfl
      have h : contract (k x) (partialWick k (fun t => c * P t - Q t)) xs =
          contract (k x) (fun t => c * partialWick k P t - partialWick k Q t) xs :=
        contract_congr _ _ fun t ht => ih t.length (by omega) P Q t rfl
      simp only [partialWick_cons, e, h, contract_sub, contract_scale]
      ring

/-- Deletion commutes with the partial matching sum because each contracted
pair crosses an unmatched generator with sign one. -/
theorem partialWick_contract (k : α → α → R) (f : α → R) (P : List α → R) (xs : List α) :
    partialWick k (contract f P) xs = contract f (partialWick k P) xs := by
  induction hn : xs.length using Nat.strong_induction_on generalizing xs P with
  | h n ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      simp only [List.length_cons] at hn
      have e := ih xs.length (by omega) (fun t => P (x :: t)) xs rfl
      have h : contract (k x) (partialWick k (contract f P)) xs =
          contract (k x) (contract f (partialWick k P)) xs :=
        contract_congr _ _ fun t ht => ih t.length (by omega) P t rfl
      simp only [partialWick_cons, contract_cons, partialWick_linear, e, h, contract_add]
      rw [contract_anticomm]
      ring

/-- Choose which pairs use the first kernel. All other pairs use the second. -/
theorem wick_add (k l : α → α → R) (xs : List α) :
    wick (fun x y => k x y + l x y) xs = partialWick k (wick l) xs := by
  induction hn : xs.length using Nat.strong_induction_on generalizing xs with
  | h n ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      simp only [List.length_cons] at hn
      have e (f : α → R) : contract f (wick (fun x y => k x y + l x y)) xs =
          contract f (partialWick k (wick l)) xs :=
        contract_congr _ _ fun t ht => ih t.length (by omega) t rfl
      rw [wick_cons, partialWick_cons, contract_add_left, e, e,
        show (fun t => wick l (x :: t)) = _ from funext (wick_cons l x), partialWick_contract,
        add_comm]

theorem contract_vanish (f : α → R) (P : List α → R) (xs : List α)
    (h : ∀ x ∈ xs, f x = 0) : contract f P xs = 0 := by
  induction xs generalizing P with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.forall_mem_cons] at h
    rw [contract_cons, h.1, zero_mul, ih _ h.2, sub_self]

theorem contract_append (f : α → R) (P : List α → R) (xs ys : List α)
    (h : ∀ y ∈ ys, f y = 0) :
    contract f P (xs ++ ys) = contract f (fun t => P (t ++ ys)) xs := by
  induction xs generalizing P with
  | nil => exact contract_vanish f P ys h
  | cons x xs ih => rw [List.cons_append, contract_cons, contract_cons, ih]; rfl

theorem contract_sublist_congr {P Q : List α → R} (f : α → R) (xs : List α)
    (h : ∀ ys : List α, ys.Sublist xs → ys.length + 1 = xs.length → P ys = Q ys) :
    contract f P xs = contract f Q xs := by
  induction xs generalizing P Q with
  | nil => rfl
  | cons x xs ih =>
    rw [contract_cons, contract_cons, h xs (by simp) rfl]
    congr 1
    apply ih
    intro ys hy he
    exact h _ (hy.cons_cons x) (by simp [he])

/-- When no contraction crosses a boundary, the two partial matchings
can be chosen independently. The remaining generators stay in site order. -/
theorem partialWick_append (k : α → α → R) (P : List α → R) (xs ys : List α)
    (h : ∀ x ∈ xs, ∀ y ∈ ys, k x y = 0) :
    partialWick k P (xs ++ ys) =
      partialWick k (fun s => partialWick k (fun t => P (s ++ t)) ys) xs := by
  induction hn : xs.length using Nat.strong_induction_on generalizing xs P with
  | h n ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      simp only [List.length_cons] at hn
      simp only [List.forall_mem_cons] at h
      rw [List.cons_append, partialWick_cons, partialWick_cons,
        ih xs.length (by omega) _ xs h.2 rfl, contract_append _ _ _ _ h.1]
      congr 1
      apply contract_sublist_congr
      intro t ht he
      exact ih t.length (by omega) P t (fun z hz => h.2 z (ht.subset hz)) rfl

theorem partialWick_vanish (k : α → α → R) (P : List α → R) (xs : List α)
    (h : ∀ x ∈ xs, ∀ y ∈ xs, k x y = 0) : partialWick k P xs = P xs := by
  induction xs generalizing P with
  | nil => rfl
  | cons x xs ih =>
    rw [partialWick_cons, contract_vanish, add_zero, ih]
    · exact fun z hz y hy => h z (by simp [hz]) y (by simp [hy])
    · exact fun y hy => h x (by simp) y (by simp [hy])

/-- Expand only the internal contractions of a single cluster. -/
theorem wick_add_append (k l : α → α → R) (xs ys : List α) (h : ∀ x y, y ∈ ys → k x y = 0) :
    wick (fun x y => k x y + l x y) (xs ++ ys) = partialWick k (fun s => wick l (s ++ ys)) xs := by
  rw [wick_add, partialWick_append _ _ _ _ (fun x _ => h x)]
  simp_rw [partialWick_vanish k _ ys (fun x _ => h x)]

/-- The residual generator list always has the original parity. -/
theorem partialWick_congr (k : α → α → R) {P Q : List α → R} (xs : List α)
    (h : ∀ ys : List α, ys.Sublist xs → ys.length % 2 = xs.length % 2 → P ys = Q ys) :
    partialWick k P xs = partialWick k Q xs := by
  induction hn : xs.length using Nat.strong_induction_on generalizing xs P Q with
  | h n ih =>
    cases xs with
    | nil => exact h [] (by simp) rfl
    | cons x xs =>
      simp only [List.length_cons] at hn
      rw [partialWick_cons, partialWick_cons]
      congr 1
      · apply ih xs.length (by omega) xs _ rfl
        intro ys hy he
        exact h _ (hy.cons_cons x) (by simp only [List.length_cons]; omega)
      · apply contract_sublist_congr
        intro ys hy he
        apply ih ys.length (by omega) ys _ rfl
        intro zs hz ht
        exact h zs ((hz.trans hy).cons x) (by simp only [List.length_cons]; omega)

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere

variable {α β ι R : Type*} [CommRing R]

private theorem contract_map (f : α → β) (q : β → R) (P : List β → R) (xs : List α) :
    contract q P (xs.map f) =
      contract (fun x => q (f x)) (fun ys => P (ys.map f)) xs := by
  induction xs generalizing P with
  | nil => rfl
  | cons x xs ih =>
    rw [List.map_cons, contract_cons, contract_cons, ih]
    rfl

theorem wick_map (k : β → β → R) (f : α → β) (xs : List α) :
    wick k (xs.map f) = wick (fun x y => k (f x) (f y)) xs := by
  induction h : xs.length using Nat.strong_induction_on generalizing xs with
  | h n ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      rw [List.map_cons, wick_cons, wick_cons, contract_map]
      apply contract_congr
      intro ys hy
      exact ih ys.length (by simp only [List.length_cons] at h; omega) ys rfl

private theorem contract_linear (s : Finset ι) (c : ι → R) (g : ι → α → R)
    (P : List α → R) (xs : List α) :
    contract (fun x => ∑ i ∈ s, c i * g i x) P xs =
      ∑ i ∈ s, c i * contract (g i) P xs := by
  induction xs generalizing P with
  | nil => simp
  | cons x xs ih =>
    simp only [contract_cons, ih, Finset.sum_mul, mul_sub, Finset.sum_sub_distrib, mul_assoc]

/-- Linearity in one row and its corresponding column. -/
theorem wick_linear {k : α → α → R} (skew : ∀ x y, k y x = -k x y)
    {x : α} {s : Finset ι} {c : ι → R} {g : ι → α}
    (hx : ∀ y, k x y = ∑ i ∈ s, c i * k (g i) y) (p q : List α) :
    wick k (p ++ x :: q) = ∑ i ∈ s, c i * wick k (p ++ g i :: q) := by
  have front (y : α) : wick k (p ++ y :: q) =
      (-1 : R) ^ p.length * wick k (y :: (p ++ q)) := by
    simpa using wick_swap_blocks skew [] p [y] q
  simp only [front, wick_cons]
  rw [funext hx, contract_linear, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => mul_left_comm _ _ _)

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

section
/-! Additive degrees of perfect pairing monomials. -/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere

variable {A R S : Type*} [CommRing R] [CommRing S] {r : ℕ}

abbrev weight (xs : List (A × Mode r)) := energy (xs.map Prod.snd)

theorem weight_cons (x : A × Mode r) (xs : List (A × Mode r)) :
    weight (x :: xs) = 2 * x.2.2 + 1 + weight xs := rfl

private theorem wick_graded (D : ℕ → R → S → Prop)
    (h₀ : ∀ n, D n 0 0) (h₁ : D 0 1 1)
    (hsub : ∀ {n x y z w}, D n x y → D n z w → D n (x - z) (y - w))
    (hmul : ∀ {n m x y z w}, D n x y → D m z w → D (n + m) (x * z) (y * w))
    (k : A × Mode r → A × Mode r → R) (l : A × Mode r → A × Mode r → S)
    (h : ∀ x y, D (x.2.2 + y.2.2 + 1) (k x y) (l x y)) (xs : List (A × Mode r)) :
    D (weight xs / 2) (wick k xs) (wick l xs) := by
  have recu (x : A × Mode r) (ys : List (A × Mode r)) (d : ℕ)
      (P : List (A × Mode r) → R) (Q : List (A × Mode r) → S)
      (hp : ∀ zs : List (A × Mode r), zs.length + 1 = ys.length →
        D ((d + weight zs) / 2) (P zs) (Q zs)) :
      D ((d + weight (x :: ys)) / 2) (contract (k x) P ys) (contract (l x) Q ys) := by
    induction ys generalizing d P Q with
    | nil => exact h₀ _
    | cons y ys ih =>
      rw [contract_cons, contract_cons]
      apply hsub
      · rw [show (d + weight (x :: y :: ys)) / 2 =
          x.2.2 + y.2.2 + 1 + (d + weight ys) / 2 by rw [weight_cons, weight_cons]; omega]
        exact hmul (h x y) (hp ys rfl)
      · rw [show d + weight (x :: y :: ys) = d + (2 * y.2.2 + 1) + weight (x :: ys) by
          simp only [weight_cons]; omega]
        refine ih _ _ _ fun zs hz => ?_
        simpa only [weight_cons, add_assoc] using hp (y :: zs) (by simp [hz])
  induction hn : xs.length using Nat.strong_induction_on generalizing xs with
  | h n ih =>
    cases xs with
    | nil => simpa [weight, energy] using h₁
    | cons x xs =>
      rw [wick_cons, wick_cons, ← zero_add (weight (x :: xs))]
      refine recu _ _ _ _ _ fun ys hy => ?_
      rw [zero_add]
      exact ih ys.length (by simp only [List.length_cons] at hn; omega) ys rfl

theorem wick_scale_energy (k : A × Mode r → A × Mode r → R) (c : R) (xs : List (A × Mode r)) :
    wick (fun x y => c ^ (x.2.2 + y.2.2 + 1) * k x y) xs =
      c ^ (weight xs / 2) * wick k xs := by
  refine wick_graded (fun n a b => a = c ^ n * b) (by simp) (by simp) ?_ ?_ _ k
    (fun _ _ => rfl) xs
  · rintro n _ _ _ _ rfl rfl
    rw [mul_sub]
  · rintro n m _ _ _ _ rfl rfl
    rw [pow_add, mul_mul_mul_comm]

open Polynomial

/-- Two charts of a homogeneous binary form of degree `n`. -/
def BinaryForm (n : ℕ) (p q : R[X]) : Prop := p.natDegree ≤ n ∧ p.reflect n = q

theorem BinaryForm.zero (n : ℕ) : BinaryForm n (0 : R[X]) 0 := by
  simp [BinaryForm]

theorem BinaryForm.const (a : R) : BinaryForm 0 (C a) (C a) := by
  simp [BinaryForm, reflect_C]

theorem BinaryForm.mul {n m : ℕ} {a b p q : R[X]} (h : BinaryForm n a b)
    (h' : BinaryForm m p q) : BinaryForm (n + m) (a * p) (b * q) :=
  ⟨natDegree_mul_le.trans (Nat.add_le_add h.1 h'.1),
    by rw [reflect_mul a p h.1 h'.1, h.2, h'.2]⟩

theorem BinaryForm.pow {n : ℕ} {a b : R[X]} (h : BinaryForm n a b) (k : ℕ) :
    BinaryForm (n * k) (a ^ k) (b ^ k) := by
  induction k with
  | zero => simpa using BinaryForm.const (1 : R)
  | succ k ih => simpa [mul_add, pow_succ] using ih.mul h

theorem wick_form (k l : A × Mode r → A × Mode r → R[X]) (m : ℕ)
    (h : ∀ x y, BinaryForm (m * (x.2.2 + y.2.2 + 1)) (k x y) (l x y)) (xs : List (A × Mode r)) :
    BinaryForm (m * (weight xs / 2)) (wick k xs) (wick l xs) := by
  refine wick_graded (fun n => BinaryForm (m * n)) (fun _ => BinaryForm.zero _)
    (by simpa using BinaryForm.const (1 : R)) ?_ ?_ k l h xs
  · intro n x y z w h₁ h₂
    exact ⟨(natDegree_sub_le x z).trans (max_le h₁.1 h₂.1),
      by rw [reflect_sub, h₁.2, h₂.2]⟩
  · intro n p x y z w h₁ h₂
    rw [mul_add]
    exact h₁.mul h₂

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

section
/-!
# Ordered wedge coordinates

Adjacent swaps contribute minus signs. Vanishing on repeated generators is a
separate condition so normalization is valid also in characteristic two.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere

def Wedge (r : ℕ) := {x : List (Mode r) // x.Pairwise (fun a b => toLex a < toLex b)}

variable {R : Type*} [CommRing R] {r : ℕ}

/-- Every mode contributes an odd amount of doubled energy. -/
theorem energy_mod_two (x : List (Mode r)) : energy x % 2 = x.length % 2 := by
  induction x with
  | nil => rfl
  | cons a x ih =>
    change (2 * a.2 + 1 + energy x) % 2 = (x.length + 1) % 2
    omega

theorem Wedge.nodup (w : Wedge r) : w.val.Nodup :=
  w.property.imp (fun h h' => (ne_of_lt h) (congrArg toLex h'))

def Alternates (φ : List (Mode r) → R) : Prop :=
  (∀ p x y s, φ (p ++ x :: y :: s) = -φ (p ++ y :: x :: s)) ∧
  (∀ p q s x, φ (p ++ x :: (q ++ x :: s)) = 0)

private theorem Alternates.repeat {φ : List (Mode r) → R} (h : Alternates φ)
    (x : List (Mode r)) (hx : ¬x.Nodup) (p : List (Mode r)) : φ (p ++ x) = 0 := by
  induction x generalizing p with
  | nil => exact (hx List.nodup_nil).elim
  | cons a x ih =>
    by_cases ha : a ∈ x
    · obtain ⟨q, s, rfl⟩ := List.append_of_mem ha
      exact h.2 p q s a
    · simpa using ih (fun ht => hx (ht.cons ha)) (p ++ [a])

private theorem perm_sign {x y : List (Mode r)} (h : x.Perm y) :
    ∃ c : R, ∀ φ : List (Mode r) → R, Alternates φ → ∀ p, φ (p ++ x) = c * φ (p ++ y) := by
  induction h with
  | nil => exact ⟨1, fun _ _ _ => (one_mul _).symm⟩
  | cons a _ ih =>
    obtain ⟨c, hc⟩ := ih
    exact ⟨c, fun φ hφ p => by simpa using hc φ hφ (p ++ [a])⟩
  | swap a b s =>
    exact ⟨-1, fun φ hφ p => by rw [neg_one_mul, hφ.1 p b a s]⟩
  | trans _ _ ih ij =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨d, hd⟩ := ij
    exact ⟨c * d, fun φ hφ p => by rw [hc φ hφ, hd φ hφ, mul_assoc]⟩

/-- The same ordered basis coordinates work for every alternating evaluation. -/
theorem normalize (R : Type*) [CommRing R] {r : ℕ} (x : List (Mode r)) :
    ∃ A : Wedge r →₀ R, (∀ y ∈ A.support, x.Perm y.val) ∧
      ∀ φ : List (Mode r) → R, Alternates φ →
        φ x = Finsupp.linearCombination R (fun y : Wedge r => φ y.val) A := by
  classical
  by_cases hx : x.Nodup
  · let rel (a b : Mode r) := toLex a ≤ toLex b
    have : Std.Total rel := ⟨fun _ _ => le_total _ _⟩
    have : IsTrans _ rel := ⟨fun _ _ _ => le_trans⟩
    have hp := (List.perm_insertionSort rel x).symm
    let w : Wedge r := ⟨_, ((List.pairwise_insertionSort rel x).and (hp.nodup_iff.mp hx)).imp
      (fun h => lt_of_le_of_ne h.1 (toLex.injective.ne h.2))⟩
    obtain ⟨c, hc⟩ := perm_sign (R := R) hp
    refine ⟨Finsupp.single w c, ?_, ?_⟩
    · intro y hy
      rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hy)]
      exact hp
    · intro φ hφ
      rw [Finsupp.linearCombination_single, smul_eq_mul]
      exact hc φ hφ []
  · refine ⟨0, by simp, ?_⟩
    intro φ hφ
    rw [map_zero]
    exact hφ.repeat x hx []

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

section
/-!
# Factoring a Wick sum through an ordered wedge basis

After contracting a partial matching inside a cluster, each remaining
row is a finite linear combination of the center rows. The coefficients
of the resulting ordered wedges are uniform in the exterior list.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere

variable {R α ι : Type*} [CommRing R] {r : ℕ}

private theorem contract_mem (M : Submodule R (ι → R)) (f : α → R) (P : ι → List α → R)
    (xs : List α) (h : ∀ ys : List α, ys.Sublist xs → ys.length + 1 = xs.length →
      (fun i => P i ys) ∈ M) :
    (fun i => contract f (P i) xs) ∈ M := by
  induction xs generalizing P with
  | nil => exact M.zero_mem
  | cons x xs ih =>
    have hc := ih (fun i s => P i (x :: s))
      (fun ys hy he => h (x :: ys) (hy.cons_cons x) (by simp [he]))
    exact M.sub_mem (M.smul_mem (f x) (h xs (by simp) rfl)) hc

theorem partial_mem (M : Submodule R (ι → R)) (k : α → α → R) (P : ι → List α → R)
    (xs : List α) (h : ∀ ys : List α, ys.Sublist xs → (fun i => P i ys) ∈ M) :
    (fun i => partialWick k (P i) xs) ∈ M := by
  induction hn : xs.length using Nat.strong_induction_on generalizing xs P with
  | h n ih =>
    cases xs with
    | nil => exact h [] (by simp)
    | cons x xs =>
      simp only [List.length_cons] at hn
      have hu := ih xs.length (by omega) (fun i s => P i (x :: s)) xs
        (fun ys hy => h (x :: ys) (hy.cons_cons x)) rfl
      have hc := contract_mem M (k x) (fun i => partialWick k (P i)) xs
        (fun ys hy he => ih ys.length (by omega) P ys
          (fun zs hz => h zs ((hz.trans hy).cons x)) rfl)
      simp only [partialWick_cons]
      exact M.add_mem hu hc

variable {l : α → α → R}

theorem alternates_map (skew : ∀ x y, l y x = -l x y) (diag : ∀ x, l x x = 0)
    (c : Mode r → α) (ys : List α) :
    Alternates (fun xs => wick l (xs.map c ++ ys)) := by
  constructor
  · intro p x y s
    simpa using wick_swap skew (p.map c) (s.map c ++ ys) (c y) (c x)
  · intro p q s x
    simpa using wick_repeat skew diag (p.map c) (q.map c) (s.map c ++ ys) (c x)

/-- A cluster in a kernel with an internal and a residual part factors
through finitely many basis wedges. Each spectator list may be chosen
after the coefficients have been fixed. -/
theorem wick_factor (k : α → α → R) (skew : ∀ x y, l y x = -l x y)
    (diag : ∀ x, l x x = 0) (c : Mode r → α) (xs : List α)
    (rows : ∀ x ∈ xs, ∃ (s : Finset ℕ) (q : ℕ → R) (g : ℕ → Mode r),
      ∀ y, l x y = ∑ i ∈ s, q i * l (c (g i)) y) :
    ∃ v : Wedge r →₀ R, ∀ ys : List α, (∀ x y, y ∈ ys → k x y = 0) →
      wick (fun x y => k x y + l x y) (xs ++ ys) =
        ∑ z ∈ v.support, v z * wick l (z.val.map c ++ ys) := by
  classical
  let W (u : Wedge r) (ys : List α) := wick l (u.val.map c ++ ys)
  let M := (Finsupp.linearCombination R W).range
  have residual (s : List α) (hs : s ⊆ xs) (p : List (Mode r)) :
      (fun ys => wick l (p.map c ++ s ++ ys)) ∈ M := by
    induction s generalizing p with
    | nil =>
      obtain ⟨v, _, hv⟩ := normalize R p
      refine ⟨v, funext fun ys => ?_⟩
      simpa [W, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply]
        using (hv _ (alternates_map skew diag c ys)).symm
    | cons x s ih =>
      obtain ⟨t, q, g, he⟩ := rows x (hs (by simp))
      have hs' : s ⊆ xs := fun y hy => hs (by simp [hy])
      have hv := M.sum_mem (fun i (_ : i ∈ t) => M.smul_mem (q i) (ih hs' (p ++ [g i])))
      convert hv using 1
      funext ys
      simpa [Finset.sum_apply] using wick_linear skew he (p.map c) (s ++ ys)
  obtain ⟨v, hv⟩ := partial_mem M k (fun ys s => wick l (s ++ ys)) xs
    (fun s hs => residual s hs.subset [])
  refine ⟨v, fun ys h => ?_⟩
  rw [wick_add_append k l xs ys h]
  simpa [W, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply] using
    (congrFun hv ys).symm

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

section
/-!
# Changing generators in a wedge

The expansion in the ordered basis is independent of all spectator
insertions. It preserves length and respects additive energy bounds.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere

variable {R α β : Type*} [CommRing R] {r : ℕ} {k : α → α → R}

theorem wick_alternates (skew : ∀ x y, k y x = -k x y) (diag : ∀ x, k x x = 0)
    (label : Mode r → α) (a b : List α) :
    Alternates (fun xs => wick k (a ++ xs.map label ++ b)) := by
  constructor
  · intro p x y s
    simpa using wick_swap skew (a ++ p.map label) (s.map label ++ b) (label y) (label x)
  · intro p q s x
    simpa using wick_repeat skew diag (a ++ p.map label) (q.map label) (s.map label ++ b) (label x)

theorem substitute_modes (skew : ∀ x y, k y x = -k x y) (diag : ∀ x, k x x = 0)
    (source : β → α) (target : Mode r → α) (bound : β → ℕ)
    (rows : ∀ x, ∃ (s : Finset ℕ) (q : ℕ → R) (g : ℕ → Mode r),
      (∀ i ∈ s, 2 * (g i).2 + 1 ≤ bound x) ∧
      ∀ y, k (source x) y = ∑ i ∈ s, q i * k (target (g i)) y)
    (xs : List β) (p : List (Mode r)) :
    ∃ v : Wedge r →₀ R,
      (∀ y ∈ v.support, energy y.val ≤ energy p + (xs.map bound).sum ∧
        y.val.length = p.length + xs.length) ∧
      ∀ a b : List α, wick k (a ++ p.map target ++ xs.map source ++ b) =
        Finsupp.linearCombination R (fun y : Wedge r => wick k (a ++ y.val.map target ++ b)) v := by
  classical
  induction xs generalizing p with
  | nil =>
    obtain ⟨v, hv, he⟩ := normalize R p
    refine ⟨v, ?_, fun a b => ?_⟩
    · intro y hy
      have h := (hv y hy).symm
      exact ⟨(h.map (fun i => 2 * i.2 + 1)).sum_eq.le, h.length_eq⟩
    · simpa using he _ (wick_alternates skew diag target a b)
  | cons x xs ih =>
    obtain ⟨s, q, g, hb, hrow⟩ := rows x
    choose v hv he using fun i => ih (p ++ [g i])
    refine ⟨∑ i ∈ s, q i • v i, ?_, ?_⟩
    · intro y hy
      rw [Finsupp.mem_support_iff, Finsupp.finsetSum_apply] at hy
      obtain ⟨i, hi, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
      have hiy : y ∈ (v i).support := by
        rw [Finsupp.mem_support_iff]
        intro hy'
        simp [hy'] at hy
      obtain ⟨h₁, h₂⟩ := hv i y hiy
      have := hb i hi
      simp only [energy, List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, List.length_append, List.length_cons, List.length_nil] at h₁ h₂ ⊢
      omega
    · intro a b
      have hl := wick_linear skew hrow (a ++ p.map target) (xs.map source ++ b)
      simp only [map_sum, map_smul, smul_eq_mul, ← he]
      simpa using hl

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

/-! # Preparing a coefficient tensor at one auxiliary site -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor

variable {F A : Type} [Field F] [Fintype A] [DecidableEq A] [Nonempty A]

private theorem place_single (U : Tensor F A) (s : A ⊕ Unit) :
    place (fun _ => s) U ≤ 1 := by
  obtain ⟨n, hn⟩ := exists_bound U
  have bound := place_mono (fun _ : A => s) (hn.trans (natCast_le (Nat.le_succ n)))
  have hs : Finset.univ.image (fun _ : A => s) = {s, s} := by
    ext t
    simp [eq_comm]
  rw [← shared_all F (n + 1), place_shared, hs, ← wire, wire_self F s (Nat.succ_pos n)] at bound
  exact bound

variable {g : Tensor F (A ⊕ Unit) →+* ℝ}

theorem preparation (hg : Monotone g) (U : Raw F A) :
    Real.log (g (pad Unit (ofRaw U))) ≤
      ∑ i, dist g (.inl i) (.inr ()) * Real.log (Fintype.card (U.leg i)) := by
  by_cases h : ofRaw U = 0
  · rw [h, (padding Unit).zero, map_zero, Real.log_zero]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (dist_nonneg g hg _ _) (by positivity)
  let p : A → A ⊕ Unit := fun _ => .inr ()
  have h0 := hg (place_single (ofRaw U) (.inr ()))
  have hcost : Real.log (g (place p (ofRaw U))) ≤ 0 :=
    Real.log_nonpos (price_place_pos g hg p h).le (by simpa using h0)
  have hs := (abs_sub_le_iff.mp (price_transport g hg U h Sum.inl p)).1
  rw [place_inl] at hs
  exact (le_sub_iff_add_le.mpr (add_le_of_nonpos_right hcost)).trans hs

/-- Sending all legs of a common binary label costs at least one bit. -/
theorem preparation_lower (hg : Monotone g) {f : Tensor F A →+* ℝ}
    (he : ∀ T, g (pad Unit T) = f T) :
    1 ≤ ∑ i, dist g (.inl i) (.inr ()) := by
  have h := preparation hg (Raw.diag F A (Fin 2))
  rw [he, diag_fin, map_natCast] at h
  change Real.log (2 : ℕ) ≤ ∑ i, dist g (.inl i) (.inr ()) * Real.log (Fintype.card (Fin 2)) at h
  rw [Fintype.card_fin, ← Finset.sum_mul] at h
  exact (le_mul_iff_one_le_left (Real.log_pos (by norm_num))).mp h

end OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
end
