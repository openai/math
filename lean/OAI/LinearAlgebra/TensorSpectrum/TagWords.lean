import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity

/-!
# Exact finite word fibers for the tag inequality

Length-`N` words over `s` letters are grouped by their occurrence counts.
The ambient count-vector space has exactly `(N + 1)^s` elements. Finite
distributivity gives the total weight, so one fiber has at least the average
weight. There are no tensor, asymptotic, or factorial assumptions here.
-/

noncomputable section

open scoped BigOperators

namespace OAI.LinearAlgebra.TensorSpectrum.TagWords

abbrev Word (s N : ℕ) := Fin N → Fin s

abbrev CountVector (s N : ℕ) := Fin s → Fin (N + 1)

/-- Number of positions occupied by the specified letter. -/
def occurrences {s N : ℕ} (w : Word s N) (i : Fin s) : ℕ :=
  (Finset.univ.filter (fun j => w j = i)).card

theorem occurrences_le {s N : ℕ} (w : Word s N) (i : Fin s) :
    occurrences w i ≤ N := by
  simpa [occurrences] using
    (Finset.card_le_card (Finset.filter_subset (fun j => w j = i) Finset.univ))

/-- Every occurrence count lies between zero and the word length. -/
def countVector {s N : ℕ} (w : Word s N) : CountVector s N :=
  fun i => ⟨occurrences w i, Nat.lt_succ_of_le (occurrences_le w i)⟩

@[simp] theorem countVector_val {s N : ℕ} (w : Word s N) (i : Fin s) :
    (countVector w i).val = occurrences w i := rfl

@[simp] theorem card_countVector (s N : ℕ) :
    Fintype.card (CountVector s N) = (N + 1) ^ s := by
  simp [CountVector]

theorem sum_occurrences {s N : ℕ} (w : Word s N) :
    ∑ i, occurrences w i = N := by
  simpa [occurrences] using
    (Finset.sum_fiberwise' Finset.univ w (fun _ : Fin s => (1 : ℕ)))

/-- The finite set of words having exactly this count vector. -/
def fiber {s N : ℕ} (c : CountVector s N) : Finset (Word s N) :=
  Finset.univ.filter (fun w => countVector w = c)

@[simp] theorem mem_fiber {s N : ℕ} (w : Word s N) (c : CountVector s N) :
    w ∈ fiber c ↔ countVector w = c := by
  simp [fiber]

theorem disjoint_fiber {s N : ℕ} {c d : CountVector s N} (h : c ≠ d) :
    Disjoint (fiber c) (fiber d) := by
  apply Finset.disjoint_left.mpr
  intro w hc hd
  exact h (((mem_fiber w c).mp hc).symm.trans ((mem_fiber w d).mp hd))

section Weights

variable {R : Type*} [CommMonoid R] {s N : ℕ}

def wordWeight (a : Fin s → R) (w : Word s N) : R :=
  ∏ j, a (w j)

def countWeight (a : Fin s → R) (c : CountVector s N) : R :=
  ∏ i, a i ^ (c i).val

/-- Grouping positions by their letters identifies the common weight of a
count fiber. This is an exact finite product identity. -/
theorem wordWeight_eq_countWeight (a : Fin s → R) (w : Word s N) :
    wordWeight a w = countWeight a (countVector w) := by
  classical
  simpa [wordWeight, countWeight, countVector, occurrences] using
    (Finset.prod_fiberwise' Finset.univ w a).symm

theorem wordWeight_eq_of_mem_fiber (a : Fin s → R)
    {c : CountVector s N} {w : Word s N} (hw : w ∈ fiber c) :
    wordWeight a w = countWeight a c := by
  rw [wordWeight_eq_countWeight, (mem_fiber w c).mp hw]

end Weights

section Mass

variable {R : Type*} [CommSemiring R] {s N : ℕ}

/-- Fiber mass is its actual cardinality times its common word weight. -/
def fiberMass (a : Fin s → R) (c : CountVector s N) : R :=
  (fiber c).card * countWeight a c

theorem sum_fiber_wordWeight (a : Fin s → R) (c : CountVector s N) :
    ∑ w ∈ fiber c, wordWeight a w = fiberMass a c := by
  calc
    ∑ w ∈ fiber c, wordWeight a w = ∑ _w ∈ fiber c, countWeight a c := by
      apply Finset.sum_congr rfl
      intro w hw
      exact wordWeight_eq_of_mem_fiber a hw
    _ = fiberMass a c := by simp [fiberMass]

/-- Finite distributivity over all length-`N` words. -/
theorem sum_wordWeight (a : Fin s → R) :
    ∑ w : Word s N, wordWeight a w = (∑ i, a i) ^ N := by
  exact (Fintype.sum_pow a N).symm

/-- The fibers partition all words, including empty fibers without changing
the total mass. -/
theorem sum_fiberMass (a : Fin s → R) :
    ∑ c : CountVector s N, fiberMass a c = (∑ i, a i) ^ N := by
  calc
    ∑ c : CountVector s N, fiberMass a c =
        ∑ c : CountVector s N, ∑ w ∈ fiber c, wordWeight a w := by
      apply Finset.sum_congr rfl
      intro c hc
      exact (sum_fiber_wordWeight a c).symm
    _ = ∑ w : Word s N, wordWeight a w := by
      exact Finset.sum_fiberwise Finset.univ countVector (wordWeight a)
    _ = (∑ i, a i) ^ N := sum_wordWeight a

end Mass

/-- Exact polynomial-overhead bound, before any limit is taken. -/
theorem exists_fiberMass_ge_average {s N : ℕ} (a : Fin s → ℝ) :
    ∃ c : CountVector s N,
      (∑ i, a i) ^ N / ((N : ℝ) + 1) ^ s ≤ fiberMass a c := by
  classical
  have hd : ((N : ℝ) + 1) ^ s ≠ 0 := by positivity
  have hsum :
      (∑ _c : CountVector s N, (∑ i, a i) ^ N / ((N : ℝ) + 1) ^ s) =
        (∑ i, a i) ^ N := by
    simp only [Finset.sum_const, Finset.card_univ, card_countVector, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    exact mul_div_cancel₀ _ hd
  obtain ⟨c, hc, hbound⟩ := Finset.exists_le_of_sum_le
    (s := Finset.univ) Finset.univ_nonempty
    (f := fun _c : CountVector s N => (∑ i, a i) ^ N / ((N : ℝ) + 1) ^ s)
    (g := fiberMass a) (by rw [hsum, sum_fiberMass])
  exact ⟨c, hbound⟩

/-- A positive total gives a genuinely nonempty selected word fiber. -/
theorem exists_nonempty_fiberMass_ge_average {s N : ℕ} (a : Fin s → ℝ)
    (ha : 0 < ∑ i, a i) :
    ∃ c : CountVector s N, (fiber c).Nonempty ∧
      (∑ i, a i) ^ N / ((N : ℝ) + 1) ^ s ≤ fiberMass a c := by
  obtain ⟨c, hc⟩ := exists_fiberMass_ge_average (N := N) a
  have hmass : 0 < fiberMass a c :=
    lt_of_lt_of_le (div_pos (pow_pos ha N) (by positivity)) hc
  have hcard : (fiber c).card ≠ 0 := by
    intro hzero
    simp [fiberMass, hzero] at hmass
  exact ⟨c, Finset.card_pos.mp (Nat.pos_of_ne_zero hcard), hc⟩

end OAI.LinearAlgebra.TensorSpectrum.TagWords
