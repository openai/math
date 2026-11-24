import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The two energy cutoffs in the shifted crossing

Appendix B of *VP and VNP differ over every field* extracts `[z^(-s-1) w^s]`
from a product of two normally ordered fermionic fields times `(z-w)^L`.
On the exterior basis of occupation states in the first `N` modes, the two orders
of the product give different finite matrix factorizations over the integers.
All energy variables are doubled to keep track of the half-integral mode energies.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Crossing

open scoped BigOperators

variable {N : ℕ}

/-- An exterior basis state specified by the occupied modes among the first `N` modes. -/
abbrev Occupation (N : ℕ) := Finset (Fin N)

/-- Twice the energy of an occupation state, obtained by summing `2 * r + 1` over its occupied
modes. -/
def doubledEnergy (input : Occupation N) : ℤ := ∑ r ∈ input, (2 * (r.val : ℤ) + 1)

/-- One creation or annihilation term in a divided derivative of a fermionic field on the first
`N` modes. -/
structure FieldTerm (N : ℕ) where
  /-- The mode whose occupation is changed by this field term. -/
  mode : Fin N
  /-- Selects creation when true and annihilation when false. -/
  create : Bool
  /-- The order of the divided derivative applied to this field term. -/
  derivative : ℕ

namespace FieldTerm

/-- Laurent exponent after the divided derivative. -/
def exponent (f : FieldTerm N) : ℤ :=
  (if f.create then (f.mode.val : ℤ) else -f.mode.val - 1) - f.derivative

/-- The doubled source weight `2 * derivative + 1` contributed by this field term. -/
def weight (f : FieldTerm N) : ℤ := 2 * (f.derivative : ℤ) + 1

/-- The integer coefficient of the divided derivative on the chosen mode, including the sign
from differentiating an annihilation term. -/
def derivativeCoefficient (f : FieldTerm N) : ℤ :=
  if f.create then f.mode.val.choose f.derivative else
    (-1) ^ f.derivative * ((f.mode.val + f.derivative).choose f.derivative : ℤ)

/-- The signed exterior creation or deletion, with the divided derivative coefficient. -/
def matrix (f : FieldTerm N) : Matrix (Occupation N) (Occupation N) ℤ := fun out input =>
  let scalar := f.derivativeCoefficient *
    (-1 : ℤ)^((input.filter (· < f.mode)).card)
  if f.create then
    if f.mode ∉ input ∧ out = insert f.mode input then scalar else 0
  else
    if f.mode ∈ input ∧ out = input.erase f.mode then scalar else 0

end FieldTerm

private def Shifted (A : Matrix (Occupation N) (Occupation N) ℤ) (t : ℤ) : Prop :=
  ∀ out input, A out input ≠ 0 → doubledEnergy out = doubledEnergy input + t

private theorem shifted_term (f : FieldTerm N) : Shifted f.matrix (2*f.exponent+f.weight) := by
  intro out input hn
  cases hc : f.create with
  | false =>
    have h : f.mode ∈ input ∧ out = input.erase f.mode := by
      by_contra h
      exact hn (by simp [FieldTerm.matrix, hc, h])
    obtain ⟨hm, rfl⟩ := h
    have he := Finset.sum_erase_add input (fun r : Fin N => 2 * (r.val : ℤ) + 1) hm
    simp [doubledEnergy, FieldTerm.exponent, FieldTerm.weight, hc]
    omega
  | true =>
    have h : f.mode ∉ input ∧ out = insert f.mode input := by
      by_contra h
      exact hn (by simp [FieldTerm.matrix, hc, h])
    obtain ⟨hm, rfl⟩ := h
    simp [doubledEnergy, FieldTerm.exponent, FieldTerm.weight, hc, Finset.sum_insert hm]
    omega

private theorem shifted_mul {A B : Matrix (Occupation N) (Occupation N) ℤ} {r s : ℤ}
    (ha : Shifted A r) (hb : Shifted B s) : Shifted (A * B) (r+s) := by
  intro out input hn
  by_contra he
  apply hn
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hak : A out k = 0
  · simp [hak]
  by_cases hbk : B k input = 0
  · simp [hbk]
  exact False.elim <| he (by have := ha _ _ hak; have := hb _ _ hbk; omega)

private theorem shifted_word (l : List (FieldTerm N)) :
    Shifted (l.map FieldTerm.matrix).prod ((l.map (fun f => 2*f.exponent+f.weight)).sum) := by
  induction l with
  | nil =>
    intro out input hn
    by_cases h : out = input
    · simp [h]
    · exact False.elim (hn (by simp [h]))
  | cons f l ih => simpa using shifted_mul (shifted_term f) ih

/-- Move creations left and deletions right, preserving the order within each group. -/
def normalOrder (l : List (FieldTerm N)) : List (FieldTerm N) :=
  l.filter FieldTerm.create ++ l.filter (fun f => !f.create)

private theorem normalOrder_sum (l : List (FieldTerm N)) (a : FieldTerm N → ℤ) :
    ((normalOrder l).map a).sum = (l.map a).sum := by
  simp only [normalOrder, List.map_append, List.sum_append]
  induction l with
  | nil => simp
  | cons f l ih =>
    cases h : f.create <;> simp [h, add_assoc, add_left_comm, ih]

private theorem sum_delta (l : List (FieldTerm N)) :
    (l.map (fun f => 2*f.exponent+f.weight)).sum =
      2 * (l.map FieldTerm.exponent).sum + (l.map FieldTerm.weight).sum := by
  induction l with
  | nil => simp
  | cons f l ih => simp [ih]; omega

/-- The permutation and derivative weights affect the values of entries, while
every supported entry changes energy by the exponent plus the source weight. -/
theorem normal_word_homogeneous (l : List (FieldTerm N)) (scalar : ℤ)
    (out input : Occupation N)
    (hn : scalar * ((normalOrder l).map FieldTerm.matrix).prod out input ≠ 0) :
    doubledEnergy out = doubledEnergy input +
      2 * (l.map FieldTerm.exponent).sum + (l.map FieldTerm.weight).sum := by
  have hm : ((normalOrder l).map FieldTerm.matrix).prod out input ≠ 0 := by
    intro hz
    simp [hz] at hn
  have hs := shifted_word (normalOrder l) out input hm
  rw [normalOrder_sum, sum_delta] at hs
  omega

/-- A coefficient of a sum of normally ordered words with the same source
weight is homogeneous on the exterior basis. -/
theorem normal_coefficient_homogeneous {A : Type*} [Fintype A]
    (words : A → List (FieldTerm N)) (scalar : A → ℤ) (b h : ℤ)
    (hw : ∀ k, ((words k).map FieldTerm.weight).sum = h)
    (out input : Occupation N)
    (hn : (∑ k : A, if ((words k).map FieldTerm.exponent).sum = b then
      scalar k * ((normalOrder (words k)).map FieldTerm.matrix).prod out input else 0) ≠ 0) :
    doubledEnergy out = doubledEnergy input + 2*b + h := by
  by_contra he
  apply hn
  apply Finset.sum_eq_zero
  intro k _
  split
  next hb =>
    by_contra hk
    exact he (by simpa [hb, hw] using normal_word_homogeneous (words k) (scalar k) out input hk)
  next => rfl

/-- Exponent of the normal-ordering sign: each deletion crosses the creations to
its right. -/
def normalInversions : List (FieldTerm N) → ℕ
  | [] => 0
  | f :: l => (if f.create then 0 else (l.filter FieldTerm.create).length) + normalInversions l

private def fieldWord {m : ℕ} (D : Fin m → ℕ) (k : Fin m → Bool × Fin N) :
    List (FieldTerm N) :=
  List.ofFn fun a => ⟨(k a).2, (k a).1, D a⟩

/-- Coefficient of the normally ordered product of the divided derivatives of
orders `D 0, …, D (m-1)`, truncating the modes to `Fin N`. -/
def normalBlock {m : ℕ} (D : Fin m → ℕ) (b : ℤ) :
    Matrix (Occupation N) (Occupation N) ℤ := fun out input =>
  ∑ k : Fin m → Bool × Fin N, let l := fieldWord D k
    if (l.map FieldTerm.exponent).sum = b then
      (-1 : ℤ)^(normalInversions l) * ((normalOrder l).map FieldTerm.matrix).prod out input
    else 0

/-- The coefficient `[z^b] Y_D` changes doubled energy by precisely
`2b + ∑ᵢ(2Dᵢ+1)` whenever its matrix entry is nonzero. -/
theorem normalBlock_homogeneous {m : ℕ} (D : Fin m → ℕ) (b : ℤ)
    (out input : Occupation N) (hn : normalBlock D b out input ≠ 0) :
    doubledEnergy out = doubledEnergy input + 2*b + ∑ j, (2*(D j : ℤ)+1) := by
  apply normal_coefficient_homogeneous (fieldWord D) (fun k => (-1 : ℤ)^normalInversions (fieldWord D k))
    b (∑ j, (2*(D j : ℤ)+1)) _ out input hn
  intro k
  simp [fieldWord, List.map_ofFn, List.sum_ofFn, FieldTerm.weight, Function.comp_def]

variable {S I J : Type*} [Fintype S] (energy : S → ℤ)

/-- A coefficient of exponent `b` for a block of doubled energy `h` changes doubled
energy by `2*b+h`. -/
def ModeHomogeneous (h : ℤ) (Y : ℤ → Matrix S S ℤ) : Prop :=
  ∀ b out input, Y b out input ≠ 0 → energy out = energy input + 2 * b + h

/-- The states whose specified energy is at most `E`. -/
abbrev Cutoff (E : ℤ) := {p : S // energy p ≤ E}

/-- The coefficient of `z^(L-a) w^a` in `(z-w)^L`. -/
def multiplier (L a : ℕ) : ℤ := (-1) ^ a * L.choose a

/-- The power `-s - 1 - L + a` required from the first field after choosing `z^(L-a) * w^a` in
the multiplier. -/
def firstExponent (L : ℕ) (s : ℤ) (a : Fin (L+1)) : ℤ := -s - 1 - L + a.val

/-- The power `s - a` required from the second field after choosing the term of degree `a` in
`w` in the multiplier. -/
def secondExponent (s : ℤ) {L : ℕ} (a : Fin (L+1)) : ℤ := s - a.val

/-- Expanding the polynomial multiplier into individual signed binomial weights. -/
theorem multiplier_expansion (z w : ℤ) (L : ℕ) :
    (z - w)^L = ∑ a : Fin (L+1), multiplier L a.val * z^(L-a.val) * w^a.val := by
  rw [sub_eq_add_neg, add_comm, add_pow, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro a _
  simp only [multiplier, neg_eq_neg_one_mul w, mul_pow]
  ring

/-- Number of coordinates in either finite factorization. -/
theorem coordinateCount (L : ℕ) (B : ℤ) :
    Fintype.card (Fin (L+1) × Cutoff energy B) = (L+1) * Fintype.card (Cutoff energy B) := by
  simp

private theorem sum_restrict {B : ℤ} (f : S → ℤ)
    (hf : ∀ x, B < energy x → f x = 0) :
    ∑ x : S, f x = ∑ x : Cutoff energy B, f x.val := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter fun x : S => energy x ≤ B)
    (by simp) f]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x _ hx
  apply hf
  simpa using hx

/-- Two factorizations of the signed coefficient, with an integral factor on each side
of the two respective cuts. The finite coordinate types include the binomial index
and the intermediate occupation state. -/
def HasShiftedFactorizations (H E s : ℤ) (m L : ℕ)
    (X : I → ℤ → Matrix S S ℤ) (Y : J → ℤ → Matrix S S ℤ) : Prop :=
    ∃ (p : Fin (L+1) × Cutoff energy (E+H+2*s) → I → Cutoff energy E → ℤ)
      (q : Fin (L+1) × Cutoff energy (E+H+2*s) → J → Cutoff energy E → ℤ)
      (r : Fin (L+1) × Cutoff energy (E+H-2*s) → I → Cutoff energy E → ℤ)
      (t : Fin (L+1) × Cutoff energy (E+H-2*s) → J → Cutoff energy E → ℤ),
    ∀ (i : I) (j : J) (out input : Cutoff energy E),
      (∑ a : Fin (L+1), multiplier L a.val *
        ((X i (firstExponent L s a) * Y j (secondExponent s a)) out.val input.val -
          (-1 : ℤ)^(m*m) *
            (Y j (secondExponent s a) * X i (firstExponent L s a)) out.val input.val)) =
        (∑ v, p v i out * q v j input) + ∑ v, r v i input * t v j out

/-- For `[z^(-s-1) w^s]`, the first product has the intermediate bound
`E+H+2*s` in doubled energy, and the reversed product has `E+H-2*s`.
The two product-coordinate types display both exact integer factorizations. -/
theorem shiftedBlockFactorization (h h' H E s : ℤ) (m L : ℕ)
    (hL : 2 * (L : ℤ) = h + h' - 2) (hh : h ≤ H) (hh' : h' ≤ H)
    (X : I → ℤ → Matrix S S ℤ) (Y : J → ℤ → Matrix S S ℤ)
    (hX : ∀ i, ModeHomogeneous energy h (X i))
    (hY : ∀ j, ModeHomogeneous energy h' (Y j)) :
    HasShiftedFactorizations energy H E s m L X Y := by
  classical
  refine ⟨fun v i out => multiplier L v.1.val * X i (firstExponent L s v.1) out.val v.2.val,
    fun v j input => Y j (secondExponent s v.1) v.2.val input.val,
    fun v i input => -(multiplier L v.1.val * (-1 : ℤ)^(m*m)) *
      X i (firstExponent L s v.1) v.2.val input.val,
    fun v j out => Y j (secondExponent s v.1) out.val v.2.val, ?_⟩
  intro i j out input
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have hf {x : S} (hx : E+H+2*s < energy x) :
      Y j (secondExponent s a) x input.val = 0 := by
    by_contra hn
    have := hY j _ _ _ hn
    have := input.property
    simp only [secondExponent] at *
    omega
  have hr {x : S} (hx : E+H-2*s < energy x) :
      X i (firstExponent L s a) x input.val = 0 := by
    by_contra hn
    have := hX i _ _ _ hn
    have := input.property
    have := a.isLt
    simp only [firstExponent] at *
    omega
  rw [Matrix.mul_apply, Matrix.mul_apply, mul_sub,
    ← mul_assoc, Finset.mul_sum, Finset.mul_sum]
  rw [sum_restrict energy _ (fun x hx => by rw [hf hx]; ring),
    sum_restrict energy _ (fun x hx => by rw [hr hx]; ring),
    sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

/-- Apply the two distinct finite cut factorizations directly to the signed coefficient
of the concrete normally ordered field products. The two lists of derivative orders
have the same length and their doubled source energies are constant in this block. -/
theorem normalBlock_factorization (N m L : ℕ) (h h' H E s : ℤ)
    (D : I → Fin m → ℕ) (D' : J → Fin m → ℕ)
    (hD : ∀ i, (∑ a, (2*(D i a : ℤ)+1)) = h)
    (hD' : ∀ j, (∑ a, (2*(D' j a : ℤ)+1)) = h')
    (hL : 2 * (L : ℤ) = h + h' - 2) (hh : h ≤ H) (hh' : h' ≤ H) :
    HasShiftedFactorizations (doubledEnergy (N := N)) H E s m L
      (fun i => normalBlock (D i)) (fun j => normalBlock (D' j)) := by
  apply shiftedBlockFactorization _ h h' _ _ _ _ _ hL hh hh'
  · intro i b out input hn
    simpa only [hD i] using normalBlock_homogeneous (D i) b out input hn
  · intro j b out input hn
    simpa only [hD' j] using normalBlock_homogeneous (D' j) b out input hn

/-- Integer rank factorizations give the same bound after passage to any field. -/
theorem factorization_rank {R X Y K : Type*} [Field R] [Fintype K] [Fintype Y]
    (p : K → X → ℤ) (q : K → Y → ℤ) :
    Matrix.rank (fun (x : X) (y : Y) => (↑(∑ k : K, p k x * q k y) : R)) ≤
      Fintype.card K := by
  let A : Matrix X K R := fun x k => p k x
  let B : Matrix K Y R := fun k y => q k y
  have eqm : (fun (x : X) (y : Y) => (↑(∑ k : K, p k x * q k y) : R) : Matrix X Y R) =
      A * B := by
    ext x y
    change (↑(∑ k : K, p k x * q k y) : R) = ∑ k : K, A x k * B k y
    simp [A, B]
  rw [eqm]
  exact (Matrix.rank_mul_le_left A B).trans A.rank_le_card_width

end Crossing

end VPVNP
end Computability
end OAI
