import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.PolynomialTensor
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.PolynomialDegeneration
import Lean.Elab.Tactic.Omega

open OAI.LinearAlgebra.MatrixExponent.Integral

/-!
# The three-sector polynomial degeneration

These are the coefficient identities of Section 5.2.  The first input has
weight zero throughout the degeneration.  Only when identifying the individual
middle branch do we reverse its first index; its other two indices are swapped.
-/

noncomputable section

open OAI.MatrixMultiplication.Foundation

namespace OAI.LinearAlgebra.MatrixExponent.Integral.Upper

/-- The second input length in the tripling construction. -/
def triplingWidth (a h : ℕ) : ℕ := 3 * h + a - 1

/-- The middle interval of the second input has weight one. -/
def triplingYWeight (a h y : ℕ) : ℤ :=
  if h ≤ y ∧ y < 2 * h + a - 1 then 1 else 0

/-- The middle output-dual interval has weight minus one. -/
def triplingZWeight (a h z : ℕ) : ℤ :=
  if h + a - 1 ≤ z ∧ z < 2 * h + a - 1 then -1 else 0

/-- The three matched pairs of intervals, expressed with exclusive upper bounds. -/
def triplingMatched (a h y z : ℕ) : Prop :=
  (y < h ∧ z < h + a - 1) ∨
  (h ≤ y ∧ y < 2 * h + a - 1 ∧ h + a - 1 ≤ z ∧ z < 2 * h + a - 1) ∨
  (2 * h + a - 1 ≤ y ∧ 2 * h + a - 1 ≤ z)

instance triplingMatched_decidable (a h y z : ℕ) : Decidable (triplingMatched a h y z) := by
  unfold triplingMatched
  infer_instance

theorem tripling_support_left {a h x y z : ℕ}
    (ha : 1 ≤ a) (hx : x < a) (hy : y < h) (hs : x + y = z) :
    z < h + a - 1 := by omega

theorem tripling_support_right {a h x y z : ℕ}
    (hy : 2 * h + a - 1 ≤ y) (hs : x + y = z) :
    2 * h + a - 1 ≤ z := by omega

/-- A supported middle output can only come from the middle second input. -/
theorem tripling_support_middle {a h x y z : ℕ}
    (ha : 1 ≤ a) (hx : x < a) (hs : x + y = z)
    (hz : h + a - 1 ≤ z ∧ z < 2 * h + a - 1) :
    h ≤ y ∧ y < 2 * h + a - 1 := by omega

/-- No nonzero convolution coefficient has a negative total weight. -/
theorem tripling_weight_nonneg {a h x y z : ℕ}
    (ha : 1 ≤ a) (hx : x < a) (hs : x + y = z) :
    0 ≤ triplingYWeight a h y + triplingZWeight a h z := by
  unfold triplingYWeight triplingZWeight
  split_ifs <;> omega

/-- Precisely the three matched sectors survive in weight zero. -/
theorem tripling_weight_zero_iff {a h x y z : ℕ}
    (ha : 1 ≤ a) (hx : x < a) (hs : x + y = z) :
    triplingYWeight a h y + triplingZWeight a h z = 0 ↔
      triplingMatched a h y z := by
  unfold triplingYWeight triplingZWeight triplingMatched
  split_ifs <;> omega

/-- Every term that disappears has weight exactly one, and goes from the
middle second-input sector to one of the two outer output sectors. -/
theorem tripling_weight_one_iff {a h x y z : ℕ}
    (ha : 1 ≤ a) (_hx : x < a) (_hs : x + y = z) :
    triplingYWeight a h y + triplingZWeight a h z = 1 ↔
      h ≤ y ∧ y < 2 * h + a - 1 ∧
        (z < h + a - 1 ∨ 2 * h + a - 1 ≤ z) := by
  unfold triplingYWeight triplingZWeight
  split_ifs <;> omega

/-- The simultaneous weight-zero tensor, with one unchanged shared first leg. -/
def triplingGraded (a h : ℕ) :
    Tensor O (Fin a) (Fin (triplingWidth a h)) (Fin (a + triplingWidth a h - 1)) :=
  weightedLimit (polynomialTensor a (triplingWidth a h)) (fun _ => 0)
    (fun y => triplingYWeight a h y.val) (fun z => triplingZWeight a h z.val)

theorem triplingGraded_of_weights (a h : ℕ)
    (x : Fin a) (y : Fin (triplingWidth a h))
    (z : Fin (a + triplingWidth a h - 1))
    (hw : triplingYWeight a h y.val + triplingZWeight a h z.val = 0) :
    triplingGraded a h x y z = polynomialTensor a (triplingWidth a h) x y z := by
  simp [triplingGraded, weightedLimit, hw]

/-- The full coefficient formula includes all vanishing cross-sector terms. -/
theorem triplingGraded_coefficient (a h : ℕ) (ha : 1 ≤ a)
    (x : Fin a) (y : Fin (triplingWidth a h))
    (z : Fin (a + triplingWidth a h - 1)) :
    triplingGraded a h x y z =
      if x.val + y.val = z.val ∧ triplingMatched a h y.val z.val then 1 else 0 := by
  classical
  by_cases hs : x.val + y.val = z.val
  · have hw := tripling_weight_zero_iff (h := h) ha x.isLt hs
    simp [triplingGraded, weightedLimit, polynomialTensor, hs, hw]
  · simp [triplingGraded, weightedLimit, polynomialTensor, hs]

/-- Translate a coordinate into the left second-input sector. -/
def triplingLeftY (a h : ℕ) (ha : 1 ≤ a) (j : Fin h) : Fin (triplingWidth a h) :=
  ⟨j.val, by have hj := j.isLt; dsimp [triplingWidth]; omega⟩

/-- Translate a coordinate into the left output sector. -/
def triplingLeftZ (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (k : Fin (a + h - 1)) : Fin (a + triplingWidth a h - 1) :=
  ⟨k.val, by have hk := k.isLt; dsimp [triplingWidth]; omega⟩

/-- Translate a coordinate into the middle second-input sector. -/
def triplingMiddleY (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (k : Fin (a + h - 1)) : Fin (triplingWidth a h) :=
  ⟨h + k.val, by have hk := k.isLt; dsimp [triplingWidth]; omega⟩

/-- Translate a coordinate into the middle output sector. -/
def triplingMiddleZ (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (j : Fin h) : Fin (a + triplingWidth a h - 1) :=
  ⟨h + a - 1 + j.val, by have hj := j.isLt; dsimp [triplingWidth]; omega⟩

/-- Translate a coordinate into the right second-input sector. -/
def triplingRightY (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (j : Fin h) : Fin (triplingWidth a h) :=
  ⟨2 * h + a - 1 + j.val, by have hj := j.isLt; dsimp [triplingWidth]; omega⟩

/-- Translate a coordinate into the right output sector. -/
def triplingRightZ (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (k : Fin (a + h - 1)) : Fin (a + triplingWidth a h - 1) :=
  ⟨2 * h + a - 1 + k.val, by have hk := k.isLt; dsimp [triplingWidth]; omega⟩

/-- Reversal used only in the middle branch identification. -/
def triplingReverse {a : ℕ} (u : Fin a) : Fin a :=
  ⟨a - 1 - u.val, by have hu := u.isLt; omega⟩

theorem triplingReverse_involutive {a : ℕ} (u : Fin a) :
    triplingReverse (triplingReverse u) = u := by
  apply Fin.ext
  have hu := u.isLt
  dsimp [triplingReverse]
  omega

theorem tripling_left_weights (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (j : Fin h) (k : Fin (a + h - 1)) :
    triplingYWeight a h (triplingLeftY a h ha j).val +
      triplingZWeight a h (triplingLeftZ a h ha hh k).val = 0 := by
  have hj := j.isLt
  have hk := k.isLt
  dsimp [triplingYWeight, triplingZWeight, triplingLeftY, triplingLeftZ]
  split_ifs <;> omega

theorem tripling_middle_weights (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (k : Fin (a + h - 1)) (j : Fin h) :
    triplingYWeight a h (triplingMiddleY a h ha hh k).val +
      triplingZWeight a h (triplingMiddleZ a h ha hh j).val = 0 := by
  have hj := j.isLt
  have hk := k.isLt
  dsimp [triplingYWeight, triplingZWeight, triplingMiddleY, triplingMiddleZ]
  split_ifs <;> omega

theorem tripling_right_weights (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (j : Fin h) (k : Fin (a + h - 1)) :
    triplingYWeight a h (triplingRightY a h ha hh j).val +
      triplingZWeight a h (triplingRightZ a h ha hh k).val = 0 := by
  dsimp [triplingYWeight, triplingZWeight, triplingRightY, triplingRightZ]
  split_ifs <;> omega

/-- The left branch is exactly polynomial multiplication of lengths `a,h`. -/
theorem tripling_left_coefficient (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (x : Fin a) (j : Fin h) (k : Fin (a + h - 1)) :
    triplingGraded a h x (triplingLeftY a h ha j) (triplingLeftZ a h ha hh k) =
      polynomialTensor a h x j k := by
  rw [triplingGraded_of_weights a h x _ _ (tripling_left_weights a h ha hh j k)]
  rfl

/-- The right branch is the same tensor after translations on the last two legs. -/
theorem tripling_right_coefficient (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (x : Fin a) (j : Fin h) (k : Fin (a + h - 1)) :
    triplingGraded a h x (triplingRightY a h ha hh j) (triplingRightZ a h ha hh k) =
      polynomialTensor a h x j k := by
  rw [triplingGraded_of_weights a h x _ _ (tripling_right_weights a h ha hh j k)]
  have hs : x.val + (2 * h + a - 1 + j.val) = 2 * h + a - 1 + k.val ↔
      x.val + j.val = k.val := by omega
  simp only [polynomialTensor, triplingRightY, triplingRightZ, hs]

/-- In the middle branch the second and third tensor legs are exchanged, and
the first basis is reversed.  This identity does not reverse the first basis
of either outer branch or of the whole simultaneous degeneration. -/
theorem tripling_middle_coefficient (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (u : Fin a) (k : Fin (a + h - 1)) (j : Fin h) :
    triplingGraded a h (triplingReverse u)
      (triplingMiddleY a h ha hh k) (triplingMiddleZ a h ha hh j) =
      polynomialTensor a h u j k := by
  rw [triplingGraded_of_weights a h (triplingReverse u) _ _
    (tripling_middle_weights a h ha hh k j)]
  have hu := u.isLt
  have hs : a - 1 - u.val + (h + k.val) = h + a - 1 + j.val ↔
      u.val + j.val = k.val := by omega
  simp only [polynomialTensor, triplingReverse, triplingMiddleY, triplingMiddleZ, hs]

/-- The three second-input images are pairwise disjoint. -/
theorem tripling_second_sectors_disjoint (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (j₁ j₂ : Fin h) (k : Fin (a + h - 1)) :
    triplingLeftY a h ha j₁ ≠ triplingMiddleY a h ha hh k ∧
    triplingMiddleY a h ha hh k ≠ triplingRightY a h ha hh j₂ ∧
    triplingLeftY a h ha j₁ ≠ triplingRightY a h ha hh j₂ := by
  have hj₁ := j₁.isLt
  have hk := k.isLt
  constructor
  · intro he
    have hv := congrArg Fin.val he
    dsimp [triplingLeftY, triplingMiddleY] at hv
    omega
  constructor
  · intro he
    have hv := congrArg Fin.val he
    dsimp [triplingMiddleY, triplingRightY] at hv
    omega
  · intro he
    have hv := congrArg Fin.val he
    dsimp [triplingLeftY, triplingRightY] at hv
    omega

/-- The three output images are pairwise disjoint as well. -/
theorem tripling_output_sectors_disjoint (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (k₁ k₂ : Fin (a + h - 1)) (j : Fin h) :
    triplingLeftZ a h ha hh k₁ ≠ triplingMiddleZ a h ha hh j ∧
    triplingMiddleZ a h ha hh j ≠ triplingRightZ a h ha hh k₂ ∧
    triplingLeftZ a h ha hh k₁ ≠ triplingRightZ a h ha hh k₂ := by
  have hk₁ := k₁.isLt
  have hj := j.isLt
  constructor
  · intro he
    have hv := congrArg Fin.val he
    dsimp [triplingLeftZ, triplingMiddleZ] at hv
    omega
  constructor
  · intro he
    have hv := congrArg Fin.val he
    dsimp [triplingMiddleZ, triplingRightZ] at hv
    omega
  · intro he
    have hv := congrArg Fin.val he
    dsimp [triplingLeftZ, triplingRightZ] at hv
    omega

/-- The three complete second-input sectors, before forgetting their labels. -/
abbrev TriplingY (a h : ℕ) := Fin h ⊕ (Fin (a + h - 1) ⊕ Fin h)

/-- The corresponding complete output sectors. -/
abbrev TriplingZ (a h : ℕ) := Fin (a + h - 1) ⊕ (Fin h ⊕ Fin (a + h - 1))

def triplingYMap (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    TriplingY a h → Fin (triplingWidth a h)
  | .inl j => triplingLeftY a h ha j
  | .inr (.inl k) => triplingMiddleY a h ha hh k
  | .inr (.inr j) => triplingRightY a h ha hh j

def triplingZMap (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    TriplingZ a h → Fin (a + triplingWidth a h - 1)
  | .inl k => triplingLeftZ a h ha hh k
  | .inr (.inl j) => triplingMiddleZ a h ha hh j
  | .inr (.inr k) => triplingRightZ a h ha hh k

theorem triplingYMap_injective (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    Function.Injective (triplingYMap a h ha hh) := by
  intro u v he
  rcases u with j | (k | j) <;> rcases v with j' | (k' | j')
  all_goals
    have hv := congrArg Fin.val he
    simp only [triplingYMap, triplingLeftY, triplingMiddleY, triplingRightY] at hv
    first
    | (exfalso; omega)
    | (simp only [Sum.inl.injEq, Sum.inr.injEq]; apply Fin.ext; omega)

theorem triplingZMap_injective (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    Function.Injective (triplingZMap a h ha hh) := by
  intro u v he
  rcases u with k | (j | k) <;> rcases v with k' | (j' | k')
  all_goals
    have hv := congrArg Fin.val he
    simp only [triplingZMap, triplingLeftZ, triplingMiddleZ, triplingRightZ] at hv
    first
    | (exfalso; omega)
    | (simp only [Sum.inl.injEq, Sum.inr.injEq]; apply Fin.ext; omega)

/-- All second-input coordinates occur in exactly one sector. -/
theorem triplingYMap_surjective (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    Function.Surjective (triplingYMap a h ha hh) := by
  intro y
  have hy := y.isLt
  dsimp [triplingWidth] at hy
  by_cases hl : y.val < h
  · refine ⟨.inl ⟨y.val, hl⟩, ?_⟩
    apply Fin.ext
    rfl
  · by_cases hm : y.val < 2 * h + a - 1
    · refine ⟨.inr (.inl ⟨y.val - h, by omega⟩), ?_⟩
      apply Fin.ext
      dsimp [triplingYMap, triplingMiddleY]
      omega
    · refine ⟨.inr (.inr ⟨y.val - (2 * h + a - 1), by omega⟩), ?_⟩
      apply Fin.ext
      dsimp [triplingYMap, triplingRightY]
      omega

/-- All output coordinates occur in exactly one corresponding sector. -/
theorem triplingZMap_surjective (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    Function.Surjective (triplingZMap a h ha hh) := by
  intro z
  have hz := z.isLt
  dsimp [triplingWidth] at hz
  by_cases hl : z.val < h + a - 1
  · refine ⟨.inl ⟨z.val, by omega⟩, ?_⟩
    apply Fin.ext
    rfl
  · by_cases hm : z.val < 2 * h + a - 1
    · refine ⟨.inr (.inl ⟨z.val - (h + a - 1), by omega⟩), ?_⟩
      apply Fin.ext
      dsimp [triplingZMap, triplingMiddleZ]
      omega
    · refine ⟨.inr (.inr ⟨z.val - (2 * h + a - 1), by omega⟩), ?_⟩
      apply Fin.ext
      dsimp [triplingZMap, triplingRightZ]
      omega

/-- A single simultaneous second-input basis equivalence. -/
def triplingYEquiv (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    TriplingY a h ≃ Fin (triplingWidth a h) :=
  Equiv.ofBijective (triplingYMap a h ha hh)
    ⟨triplingYMap_injective a h ha hh, triplingYMap_surjective a h ha hh⟩

/-- A single simultaneous output basis equivalence. -/
def triplingZEquiv (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    TriplingZ a h ≃ Fin (a + triplingWidth a h - 1) :=
  Equiv.ofBijective (triplingZMap a h ha hh)
    ⟨triplingZMap_injective a h ha hh, triplingZMap_surjective a h ha hh⟩

/-- The actual common-first-input assembly.  Its middle summand, in the same
first-input coordinates as the outer summands, has reversed first coefficients.
Every cross-sector coefficient is zero. -/
def triplingSectorTensor (a h : ℕ) : Tensor O (Fin a) (TriplingY a h) (TriplingZ a h)
  | x, .inl j, .inl k => polynomialTensor a h x j k
  | x, .inr (.inl k), .inr (.inl j) => polynomialTensor a h (triplingReverse x) j k
  | x, .inr (.inr j), .inr (.inr k) => polynomialTensor a h x j k
  | _, _, _ => 0

/-- Reindexing the last two legs by their single complete sector equivalences
gives the full assembled tensor.  The first input is literally unchanged. -/
theorem triplingGraded_sector_assembly (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) :
    (fun x y z => triplingGraded a h x
      (triplingYEquiv a h ha hh y) (triplingZEquiv a h ha hh z)) =
        triplingSectorTensor a h := by
  funext x y z
  change triplingGraded a h x (triplingYMap a h ha hh y)
    (triplingZMap a h ha hh z) = triplingSectorTensor a h x y z
  rcases y with j | (k | j) <;> rcases z with k' | (j' | k')
  · exact tripling_left_coefficient a h ha hh x j k'
  · rw [triplingGraded_coefficient a h ha]
    have hj := j.isLt
    have hx := x.isLt
    have hn : ¬(x.val + (triplingYMap a h ha hh (.inl j)).val =
        (triplingZMap a h ha hh (.inr (.inl j'))).val ∧
      triplingMatched a h (triplingYMap a h ha hh (.inl j)).val
        (triplingZMap a h ha hh (.inr (.inl j'))).val) := by
      dsimp [triplingMatched, triplingYMap, triplingZMap, triplingLeftY,
        triplingMiddleZ]
      omega
    simp only [hn, ite_false, triplingSectorTensor]
  · rw [triplingGraded_coefficient a h ha]
    have hj := j.isLt
    have hx := x.isLt
    have hn : ¬(x.val + (triplingYMap a h ha hh (.inl j)).val =
        (triplingZMap a h ha hh (.inr (.inr k'))).val ∧
      triplingMatched a h (triplingYMap a h ha hh (.inl j)).val
        (triplingZMap a h ha hh (.inr (.inr k'))).val) := by
      dsimp [triplingMatched, triplingYMap, triplingZMap, triplingLeftY,
        triplingRightZ]
      omega
    simp only [hn, ite_false, triplingSectorTensor]
  · rw [triplingGraded_coefficient a h ha]
    have hk := k.isLt
    have hk' := k'.isLt
    have hn : ¬(x.val + (triplingYMap a h ha hh (.inr (.inl k))).val =
        (triplingZMap a h ha hh (.inl k')).val ∧
      triplingMatched a h (triplingYMap a h ha hh (.inr (.inl k))).val
        (triplingZMap a h ha hh (.inl k')).val) := by
      dsimp [triplingMatched, triplingYMap, triplingZMap, triplingMiddleY,
        triplingLeftZ]
      omega
    simp only [hn, ite_false, triplingSectorTensor]
  · simpa only [triplingReverse_involutive, triplingYMap, triplingZMap,
      triplingSectorTensor] using
      tripling_middle_coefficient a h ha hh (triplingReverse x) k j'
  · rw [triplingGraded_coefficient a h ha]
    have hk := k.isLt
    have hn : ¬(x.val + (triplingYMap a h ha hh (.inr (.inl k))).val =
        (triplingZMap a h ha hh (.inr (.inr k'))).val ∧
      triplingMatched a h (triplingYMap a h ha hh (.inr (.inl k))).val
        (triplingZMap a h ha hh (.inr (.inr k'))).val) := by
      dsimp [triplingMatched, triplingYMap, triplingZMap, triplingMiddleY,
        triplingRightZ]
      omega
    simp only [hn, ite_false, triplingSectorTensor]
  · rw [triplingGraded_coefficient a h ha]
    have hk' := k'.isLt
    have hn : ¬(x.val + (triplingYMap a h ha hh (.inr (.inr j))).val =
        (triplingZMap a h ha hh (.inl k')).val ∧
      triplingMatched a h (triplingYMap a h ha hh (.inr (.inr j))).val
        (triplingZMap a h ha hh (.inl k')).val) := by
      dsimp [triplingMatched, triplingYMap, triplingZMap, triplingRightY,
        triplingLeftZ]
      omega
    simp only [hn, ite_false, triplingSectorTensor]
  · rw [triplingGraded_coefficient a h ha]
    have hj' := j'.isLt
    have hn : ¬(x.val + (triplingYMap a h ha hh (.inr (.inr j))).val =
        (triplingZMap a h ha hh (.inr (.inl j'))).val ∧
      triplingMatched a h (triplingYMap a h ha hh (.inr (.inr j))).val
        (triplingZMap a h ha hh (.inr (.inl j'))).val) := by
      dsimp [triplingMatched, triplingYMap, triplingZMap, triplingRightY,
        triplingMiddleZ]
      omega
    simp only [hn, ite_false, triplingSectorTensor]
  · exact tripling_right_coefficient a h ha hh x j k'

end OAI.LinearAlgebra.MatrixExponent.Integral.Upper
