import OAI.Optimization.LinearProgramming.Contract.AppAnalysis
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-! ## Decoding the finite oracle's dyadic response words -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Contraction

open OracleSpec Contract

/-- Read a self-delimiting little-endian natural and return the unused suffix. -/
def readMagnitude : Word → Option (ℕ × Word)
  | false :: tail => some (0, tail)
  | true :: bit :: more => do
    let (n, tail) ← readMagnitude more
    return (Nat.bit bit n, tail)
  | _ => none

private theorem readMagnitude_frame (bits tail : Word) :
    readMagnitude (frame bits ++ tail) = some (bits.foldr Nat.bit 0, tail) := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    change (do
      let (n, t) ← readMagnitude (frame bs ++ tail)
      pure (Nat.bit b n, t)) = some (Nat.bit b (bs.foldr Nat.bit 0), tail)
    rw [ih]
    rfl

private theorem bits_value (n : ℕ) : n.bits.foldr Nat.bit 0 = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n h ih => rw [Nat.bits_append_bit n b h, List.foldr_cons, ih]

theorem readMagnitude_encodeNat (n : ℕ) (tail : Word) :
    readMagnitude (encodeNat n ++ tail) = some (n, tail) := by
  simpa [encodeNat, bits_value] using readMagnitude_frame n.bits tail

/-- Read the sign bit followed by a framed magnitude. -/
def readSigned : Word → Option (ℤ × Word)
  | [] => none
  | negative :: rest => do
    let (n, tail) ← readMagnitude rest
    return (if negative then -(n : ℤ) else (n : ℤ), tail)

private def signedWord (z : ℤ) : Word := decide (z < 0) :: encodeNat z.natAbs

theorem readSigned_word (z : ℤ) (tail : Word) :
    readSigned ((decide (z < 0) :: encodeNat z.natAbs) ++ tail) = some (z, tail) := by
  by_cases h : z < 0
  · simp [readSigned, h, readMagnitude_encodeNat, Int.ofNat_natAbs_of_nonpos h.le]
  · simp [readSigned, h, readMagnitude_encodeNat, Int.natAbs_of_nonneg (le_of_not_gt h)]

/-- Read the requested coordinate from the beginning of the reply, skipping complete earlier
coordinates. Every branch on a malformed prefix terminates. -/
def readSignedAt : ℕ → Word → Option ℤ
  | 0, w => (readSigned w).map Prod.fst
  | i+1, w => do
    let (_, rest) ← readSigned w
    readSignedAt i rest

private theorem readSignedAt_list (xs : List ℤ) (i : ℕ) (h : i < xs.length) (tail : Word) :
    readSignedAt i (xs.flatMap signedWord ++ tail) = some xs[i] := by
  induction xs generalizing i with
  | nil => simp at h
  | cons z zs ih =>
    simp only [List.flatMap_cons, List.append_assoc]
    have hr : readSigned (signedWord z ++ (List.flatMap signedWord zs ++ tail)) =
        some (z, List.flatMap signedWord zs ++ tail) := readSigned_word z _
    cases i with
    | zero => rw [readSignedAt, hr]; rfl
    | succ i =>
      have hi : i < zs.length := by simpa using h
      rw [readSignedAt, hr]
      exact ih i hi

theorem readSignedAt_bitApproximation {n : ℕ} (z : Fin n → ℤ) (i : Fin n) :
    readSignedAt i.val (bitApproximation z) = some (z i) := by
  change readSignedAt i.val ((List.ofFn z).flatMap signedWord) = _
  have hi : i.val < (List.ofFn z).length := by simp
  have h := readSignedAt_list (List.ofFn z) i.val hi []
  rw [List.append_nil] at h
  exact h.trans (congrArg some (List.getElem_ofFn (f := z) hi))

/-- Interpret a signed integer at the requested precision. Malformed messages default to zero;
the legal-reply theorem depends only on the exact protocol's canonical words. -/
def decodeDyadic (precision i : ℕ) (answer : Word) : ℚ :=
  (((readSignedAt i answer).getD 0 : ℤ) : ℚ) * (1/2 : ℚ)^precision

theorem decodeDyadic_bitApproximation {n : ℕ} (z : Fin n → ℤ) (precision : ℕ) (i : Fin n) :
    decodeDyadic precision i.val (bitApproximation z) = (z i : ℚ) * (1/2 : ℚ)^precision := by
  simp [decodeDyadic, readSignedAt_bitApproximation]

/-- The signed integers in any admissible oracle response have absolute value at most `2ᵇ+1`.
This includes responses just outside the unit cube, as allowed by the oracle contract. -/
theorem closeDyadicEvaluation_magnitude {n : ℕ} {F : Contract.Cube n → Contract.Cube n}
    {q : Contract.Evaluation n} {z : Fin n → ℤ} (hz : closeDyadicEvaluation F q z) (i : Fin n) :
    (z i).natAbs ≤ 2^q.precision + 1 := by
  let P : ℝ := 2^q.precision
  have hP : 0 < P := by dsimp [P]; positivity
  have h := hz i
  change |(z i : ℝ) * ((2:ℝ)⁻¹ ^ q.precision) - (F (realPoint q.point) i : ℝ)| ≤
    (2:ℝ)⁻¹ ^ q.precision at h
  have hinv : (2:ℝ)⁻¹ ^ q.precision = 1/P := by simp [P, one_div]
  rw [hinv, mul_one_div] at h
  obtain ⟨hl, hu⟩ := abs_le.mp h
  have hu' : (z i : ℝ)/P ≤ 1 + 1/P := by linarith [(F (realPoint q.point) i).property.2]
  have hl' : -(1/P) ≤ (z i : ℝ)/P := by linarith [(F (realPoint q.point) i).property.1]
  have hzu : (z i : ℝ) ≤ P+1 := by
    have := (div_le_iff₀ hP).mp hu'
    field_simp [ne_of_gt hP] at this
    linarith
  have hzl : -(1:ℝ) ≤ z i := by
    have := (le_div_iff₀ hP).mp hl'
    field_simp [ne_of_gt hP] at this
    linarith
  have habs : |(z i : ℝ)| ≤ (2:ℝ)^q.precision + 1 :=
    abs_le.mpr ⟨by change -(P+1) ≤ _; linarith, hzu⟩
  rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
  exact_mod_cast habs

private theorem frame_length (xs : Word) : (frame xs).length = 2*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    change (frame xs).length + 1 + 1 = 2*(xs.length+1) + 1
    omega

theorem encodeNat_length (n : ℕ) : (encodeNat n).length = 2*n.size+1 := by
  simp [encodeNat, frame_length, Nat.size_eq_bits_len]

private theorem signedVector_length_le {n : ℕ} (z : Fin n → ℤ) (b : ℕ)
    (hz : ∀ i, (z i).natAbs ≤ 2^b+1) : (bitApproximation z).length ≤ n * (2*b + 6) := by
  have hword (i : Fin n) : (signedWord (z i)).length ≤ 2*b+6 := by
    have hpos : 0 < (2:ℕ)^b := by positivity
    have hmag := hz i
    have hsize : (z i).natAbs.size ≤ b+2 := Nat.size_le.mpr (by rw [pow_add]; norm_num; omega)
    simp only [signedWord, List.length_cons, encodeNat_length]
    omega
  change ((List.ofFn z).flatMap signedWord).length ≤ n * (2*b+6)
  have hlist (xs : List ℤ) (hb : ∀ u ∈ xs, (signedWord u).length ≤ 2*b+6) :
      (xs.flatMap signedWord).length ≤ xs.length*(2*b+6) := by
    induction xs with
    | nil => simp
    | cons u xs ih =>
      have hu := hb u (by simp)
      have hs := ih (fun v hv => hb v (by simp [hv]))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [Nat.succ_mul xs.length (2*b+6)]
      omega
  simpa using hlist (List.ofFn z) (fun u hu => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
    exact hword i)

theorem closeDyadicEvaluation_word_length {n : ℕ} {F : Contract.Cube n → Contract.Cube n}
    {q : Contract.Evaluation n} {z : Fin n → ℤ} (hz : closeDyadicEvaluation F q z) :
    (bitApproximation z).length ≤ n * (2*q.precision+6) :=
  signedVector_length_le z q.precision (closeDyadicEvaluation_magnitude hz)

/-- The signed-rational wire representation has one sign bit, two delimiters and two bits
per numerator/denominator digit, in the same normalization used by the RAM. -/
theorem encodeRat_length_le_ratBits (x : ℚ) : (encodeRat x).length ≤ 2*RAM.ratBits x + 1 := by
  have hsize (n : ℕ) : n.size ≤ n.log2+1 := Nat.size_le.mpr Nat.lt_log2_self
  simp only [encodeRat, List.length_cons, List.length_append, encodeNat_length, RAM.ratBits]
  have hn := hsize x.num.natAbs
  have hd := hsize x.den
  omega

/-- Encoding an entire rational vector incurs only linear overhead. -/
theorem vectorBits_length_le_ratBits {n : ℕ} (x : Fin n → ℚ) :
    (vectorBits x).length ≤ 2 * (∑ i, RAM.ratBits (x i)) + n := by
  induction n with
  | zero => simp [vectorBits]
  | succ n ih =>
    let xs : Fin n → ℚ := fun i => x i.succ
    have h := ih xs
    have h0 := encodeRat_length_le_ratBits (x 0)
    rw [Fin.sum_univ_succ]
    change ((List.ofFn x).flatMap encodeRat).length ≤ _
    rw [List.ofFn_succ, List.flatMap_cons, List.length_append]
    change (encodeRat (x 0)).length + (vectorBits xs).length ≤ 2*(RAM.ratBits (x 0) + ∑ i, RAM.ratBits (xs i)) + (n+1)
    omega

/-- This is the size of the complete outgoing packet charged by `BitProgram.tick`. -/
theorem bitQuestion_length_le {n : ℕ} (q : Contract.Evaluation n) :
    (bitQuestion q).length ≤ 2*q.precision.size + 1 + 2*(∑ i, RAM.ratBits (q.point i).1) + n := by
  rw [bitQuestion, List.length_append, encodeNat_length]
  have h := vectorBits_length_le_ratBits (fun i => (q.point i).1)
  omega

/-- Decode one actual response, including its dependence on the history of earlier oracle
exchanges. The accuracy and transfer-size guarantees refer to the same returned word. -/
theorem respects_decodeDyadic {n : ℕ} {F : Contract.Cube n → Contract.Cube n} {o : WordOracle}
    (ho : Respects bitQuestion bitApproximation (closeDyadicEvaluation F) o)
    (past : Transcript) (q : Contract.Evaluation n) :
    let answer := o past (bitQuestion q)
    (∀ i : Fin n, |(decodeDyadic q.precision i.val answer : ℝ) - (F (realPoint q.point) i : ℝ)| ≤
      (1/2 : ℝ)^q.precision) ∧ answer.length ≤ n * (2*q.precision + 6) := by
  obtain ⟨z, heq, hz⟩ := ho past q
  dsimp only
  rw [heq]
  refine ⟨?_, closeDyadicEvaluation_word_length hz⟩
  intro i
  rw [decodeDyadic_bitApproximation]
  push_cast
  simpa only [one_div] using hz i

end Contraction
end LinearProgramming
end Optimization
end OAI
