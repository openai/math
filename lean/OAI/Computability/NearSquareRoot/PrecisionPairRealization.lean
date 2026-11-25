import OAI.Computability.NearSquareRoot.PrecisionPairTables
import OAI.Computability.IntegerMultiplication.Brief.Blot

/-! # Polynomial-tape implementation of the rational local phase tables

P192's binary integer programs evaluate rational expressions while retaining
a positive denominator. The scaled square root adds a binary integer division
and one call to the P192 integer square root before the final rescaling.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhaseTable

open IntegerMultiplication IntegerMultiplication.Brief IntegerMultiplication.Strip
  IntegerMultiplication.Staff IntegerMultiplication.Carry

variable {J : Type} {r : Regime J}

/-- A rational function represented by P192's polynomial tape setup language. -/
abbrev RatRealized (r : Regime J) (q : J → ℚ) : Prop := Blot r (fun j ↦ (q j : ℝ))

/-- Two separately encoded rational components. -/
abbrev PairRealized (r : Regime J) (q : J → ℚ × ℚ) : Prop :=
  RatRealized r (fun j ↦ (q j).1) ∧ RatRealized r (fun j ↦ (q j).2)

namespace RatRealized

variable {x y : J → ℚ}

theorem natConst (n : ℕ) : RatRealized r (fun _ ↦ n) := by
  simpa only [RatRealized, Rat.cast_natCast] using Blot.natural (Figure.natural (r := r) n)

theorem add (h : RatRealized r x) (k : RatRealized r y) :
    RatRealized r (fun j ↦ x j + y j) := by
  simpa only [RatRealized, Rat.cast_add] using h.adding k

theorem subtr (h : RatRealized r x) (k : RatRealized r y) :
    RatRealized r (fun j ↦ x j - y j) := by
  simpa only [RatRealized, Rat.cast_sub] using h.sub k

theorem neg (h : RatRealized r x) : RatRealized r (fun j ↦ -x j) := by
  simpa only [RatRealized, Rat.cast_neg] using h.minus

theorem mul (h : RatRealized r x) (k : RatRealized r y) :
    RatRealized r (fun j ↦ x j * y j) := by
  simpa only [RatRealized, Rat.cast_mul] using h.times k

theorem positiveDiv (h : RatRealized r x) (k : RatRealized r y) (hy : ∀ j, 0 < y j) :
    RatRealized r (fun j ↦ x j / y j) := by
  simpa only [RatRealized, Rat.cast_div] using h.ratio k (fun j ↦ by exact_mod_cast hy j)

/-- Return zero at a zero denominator; all nonzero denominators are positive. -/
theorem nonnegDiv (h : RatRealized r x) (k : RatRealized r y) (hy : ∀ j, 0 ≤ y j) :
    RatRealized r (fun j ↦ x j / y j) := by
  classical
  have zero : RatRealized r (fun _ ↦ 0) := natConst 0
  have one : RatRealized r (fun _ ↦ 1) := natConst 1
  have test : Classified r (fun j ↦ (0 : ℝ) < (y j : ℝ)) := by
    simpa only [Rat.cast_zero] using zero.compared k
  have guarded := k.choice one test
  have num := h.choice zero test
  have pos j : 0 < (if (0 : ℝ) < (y j : ℝ) then (y j : ℝ) else ((1 : ℚ) : ℝ)) := by
    split <;> first | assumption | norm_num
  have result := num.ratio guarded pos
  have eqn (j : J) :
      (if (0 : ℝ) < (y j : ℝ) then (x j : ℝ) else ((0:ℚ):ℝ)) /
      (if (0 : ℝ) < (y j : ℝ) then (y j : ℝ) else ((1:ℚ):ℝ)) = ((x j / y j : ℚ) : ℝ) := by
    by_cases hpos : (0 : ℝ) < (y j : ℝ)
    · simp [hpos]
    · have hz : (y j : ℝ) = 0 := le_antisymm (le_of_not_gt hpos) (by exact_mod_cast hy j)
      simp [hz]
  simpa only [eqn] using result

theorem powTwo (p : J → ℕ) (hp : Realizes r p) : RatRealized r (fun j ↦ 2 ^ p j) := by
  simpa only [RatRealized, Rat.cast_pow, Rat.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat] using
    Blot.natural ((Figure.natural (r := r) 2).repeated hp)

theorem floor (h : RatRealized r x) : Figure r (fun j ↦ ⌊x j⌋₊) := by
  obtain ⟨a,b,ha,hb,_,he⟩ := h
  dsimp only at he
  have eqn (j : J) : ⌊x j⌋₊ = (a j).toNat / b j := by
    calc
      ⌊x j⌋₊ = ⌊(x j : ℝ)⌋₊ := by rw [← Int.floor_toNat, ← Int.floor_toNat, Rat.floor_cast]
      _ = ⌊(a j : ℝ)⌋₊ / b j := by rw [he, Nat.floor_div_natCast]
      _ = _ := by rw [← Int.floor_toNat, Int.floor_intCast]
  simp_rw [eqn]
  exact ha.toNat.quotients hb

theorem squareRoot {p : J → ℕ} (hp : Realizes r p) (h : RatRealized r x) :
    RatRealized r (fun j ↦ sqrtRat (p j) (x j)) := by
  have s := powTwo p hp
  have scaled : RatRealized r (fun j ↦ x j * (2 ^ p j) ^ 2) := by
    simpa only [pow_two] using mul h (mul s s)
  have root := (floor scaled).rooted
  have frac : RatRealized r (fun j ↦ (Nat.sqrt ⌊x j * (2 ^ p j) ^ 2⌋₊ : ℚ)) := by
    simpa only [RatRealized, Rat.cast_natCast] using Blot.natural root
  exact positiveDiv frac s (fun _ ↦ by positivity)

end RatRealized

private theorem normSqRealized {q : J → ℚ × ℚ} (hq : PairRealized r q) :
    RatRealized r (fun j ↦ normSqRat (q j)) := by
  simpa only [normSqRat, pow_two] using RatRealized.add
    (RatRealized.mul hq.1 hq.1) (RatRealized.mul hq.2 hq.2)

private theorem unitPhaseRealized {p : J → ℕ} (hp : Realizes r p) {q : J → ℚ × ℚ}
    (hq : PairRealized r q) : PairRealized r (fun j ↦ unitPhase (p j) (q j)) := by
  have hm : RatRealized r (fun j ↦ modulus (p j) (q j)) :=
    RatRealized.squareRoot hp (normSqRealized hq)
  have nonneg j : 0 ≤ modulus (p j) (q j) := by unfold modulus sqrtRat; positivity
  exact ⟨RatRealized.nonnegDiv hq.1 hm nonneg, RatRealized.nonnegDiv hq.2 hm nonneg⟩

private theorem rotatedPairRealized {p : J → ℕ} (hp : Realizes r p) {q : J → ℚ × ℚ}
    (hq : PairRealized r q) :
    PairRealized r (fun j ↦ rotatedA (p j) (q j)) ∧
    PairRealized r (fun j ↦ rotatedB (p j) (q j)) := by
  have two : RatRealized r (fun _ ↦ 2) := RatRealized.natConst 2
  have h : RatRealized r (fun j ↦ walshRat (p j)) :=
    RatRealized.positiveDiv (RatRealized.squareRoot hp two) two (by norm_num)
  have t : RatRealized r (fun j ↦ dilationTailRat (p j) (q j)) :=
    RatRealized.squareRoot hp (RatRealized.subtr (RatRealized.natConst 1) (normSqRealized hq))
  exact ⟨⟨RatRealized.mul h (RatRealized.add hq.1 t), RatRealized.mul h hq.2⟩,
    ⟨RatRealized.mul h (RatRealized.subtr t hq.1), RatRealized.mul h hq.2⟩⟩

private theorem tableRealized {p : J → ℕ} (hp : Realizes r p) {a b : J → ℚ × ℚ}
    (ha : PairRealized r a) (hb : PairRealized r b) (i : Fin 6) :
    PairRealized r (fun j ↦ rationalTable (p j) (a j) (b j) i) := by
  have hu := unitPhaseRealized hp ha
  have hv := unitPhaseRealized hp hb
  have hr : RatRealized r (fun j ↦ modulus (p j) (a j)) :=
    RatRealized.squareRoot hp (normSqRealized ha)
  have hs : RatRealized r (fun j ↦ modulus (p j) (b j)) :=
    RatRealized.squareRoot hp (normSqRealized hb)
  fin_cases i
  · exact hu
  · exact ⟨hv.2, hv.1⟩
  · exact ⟨hr, hs⟩
  · exact ⟨hr, RatRealized.neg hs⟩
  · exact ⟨RatRealized.natConst 1, RatRealized.natConst 0⟩
  · exact ⟨RatRealized.subtr (RatRealized.mul hu.1 hv.2) (RatRealized.mul hu.2 hv.1),
      RatRealized.neg (RatRealized.add (RatRealized.mul hu.1 hv.1) (RatRealized.mul hu.2 hv.2))⟩

/-- Every computed table entry is realized by a fixed polynomial P192 program
on the original input, including integer square root, all divisions, products
and signed components. This assertion also covers a zero computed modulus. -/
theorem chirpPairTable_realizable (bits : J → ℕ) (p : Realizes r bits) (q : J → ℚ × ℚ)
    (hq : PairRealized r q) (i : Fin 6) :
    PairRealized r (fun j ↦ chirpPairTable (bits j) (q j) i) := by
  have hp : Realizes r (fun j ↦ bits j + 10) := p.plus (.fix 10)
  obtain ⟨ha,hb⟩ := rotatedPairRealized hp hq
  exact tableRealized hp ha hb i

end PhaseTable

end NearSquareRoot
end Computability
end OAI
