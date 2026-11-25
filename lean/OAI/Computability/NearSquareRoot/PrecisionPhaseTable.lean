import OAI.Computability.IntegerMultiplication.Winds
import OAI.Computability.NearSquareRoot.PhaseProgramRelease

/-!
# Fixed-program generation of rational-angle phases

A query contains the requested fractional precision in unary, a signed binary
numerator, and a positive binary denominator. P192's polynomial setup language
computes the reduced residue, approximates the rational angle by its Taylor
program, and writes two rounded binary components. The time bound below is in
the encoded query length, uniformly in all three inputs.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhaseTable
open IntegerMultiplication Code Bits Grid Strip Staff Carry Dusk Brief Star

structure Query where
  bits : ℕ
  numerator : Grid.S
  denominator : Word
  positive : 0 < value denominator

def Query.payload (q : Query) : Tally × Grid.S × Word :=
  (tally q.bits, q.numerator, q.denominator)

def Query.inputSize (q : Query) := q.bits + q.numerator.2.length + q.denominator.length

private def regime : Regime Query where
  scale := Query.inputSize
  header := fun q => send q.payload
  gauge := by
    refine ⟨1, 8, fun q => ?_⟩
    change size q.payload ≤ 8 * (q.inputSize + 1) ^ 1
    simp only [Query.payload, Query.inputSize, size_prod, size_tally, tally_length,
      show size q.numerator.1 = 1 from rfl, size_word, pow_one]
    omega

/-- An arbitrary signed numerator and positive denominator available on the
setup stacks can be used without any bound on their ratio. -/
theorem computeAngleAt {I : Type} {r : Regime I} (frac width : I → ℕ)
    (hf : Realizes r frac) (hw : Realizes r width)
    (guard : ∀ i, 2 * (2 : ℝ) ^ frac i + 2 < 2 ^ width i)
    (z : I → ℤ) (hz : Signed r z) (m : I → ℕ) (hm : Figure r m) (pos : ∀ i, 0 < m i) :
    ∃ B : (i : I) → Grain (width i), Satisfactory width r B ∧
      ∀ i, ‖meaning (frac i) (width i) (B i) - Fourier.phase (m i) (z i)‖ ≤
        3 * (1 / 2 : ℝ) ^ frac i := by
  let a (i : I) := (z i % (m i : ℤ)).toNat
  have ha : Figure r a := hz.modulo hm pos
  have hrem (i : I) : 0 ≤ z i % (m i : ℤ) :=
    Int.emod_nonneg _ (by exact_mod_cast Nat.ne_of_gt (pos i))
  have ha_le (i : I) : a i ≤ m i := by
    have := Int.emod_lt_of_pos (z i) (by exact_mod_cast pos i : 0 < (m i : ℤ))
    dsimp [a]
    omega
  obtain ⟨B, run, hB⟩ := Star.direction frac width hf hw guard ha hm pos ha_le
  refine ⟨B, run, fun i => ?_⟩
  have : NeZero (m i) := ⟨Nat.ne_of_gt (pos i)⟩
  have heq : Fourier.phase (m i) (a i : ℕ) = Fourier.phase (m i) (z i) := by
    apply (Fourier.phase_inj ..).2
    dsimp [a]
    rw [Int.toNat_of_nonneg (hrem i)]
    exact Int.dvd_emod_sub_self
  rw [← heq]
  exact hB i

/-- Two fractional guard bits suffice for any requested precision. -/
theorem computeAngle {I : Type} {r : Regime I} (bits : I → ℕ) (hp : Realizes r bits)
    (z : I → ℤ) (hz : Signed r z) (m : I → ℕ) (hm : Figure r m) (pos : ∀ i, 0 < m i) :
    ∃ B : (i : I) → Grain (bits i + 4), Satisfactory (fun i => bits i + 4) r B ∧
      ∀ i, ‖meaning (bits i + 2) (bits i + 4) (B i) - Fourier.phase (m i) (z i)‖ ≤
        (1 / 2 : ℝ) ^ bits i := by
  have guard (i : I) : 2 * (2 : ℝ) ^ (bits i + 2) + 2 < 2 ^ (bits i + 4) := by
    have : 1 ≤ (2 : ℝ) ^ bits i := one_le_pow₀ (by norm_num)
    rw [pow_add, pow_add]
    norm_num
    linarith
  obtain ⟨B, run, hB⟩ := computeAngleAt (fun i => bits i + 2) (fun i => bits i + 4)
    (hp.plus (.fix 2)) (hp.plus (.fix 4)) guard z hz m hm pos
  refine ⟨B, run, fun i => (hB i).trans ?_⟩
  rw [pow_add]
  have hp0 : 0 ≤ (1 / 2 : ℝ) ^ bits i := by positivity
  nlinarith

/-- Enumerating a polynomial-length table of generated signed rational angles
produces the encoded dyadics in index order under the same setup budget. -/
theorem computeAngleTable {I : Type} {r : Regime I} (n : I → ℕ) (hn : Realizes r n)
    (bits : Across n → ℕ) (hp : Realizes (Staff.signal n hn) bits)
    (z : Across n → ℤ) (hz : Signed (Staff.signal n hn) z)
    (m : Across n → ℕ) (hm : Figure (Staff.signal n hn) m) (pos : ∀ q, 0 < m q) :
    ∃ B : (q : Across n) → Grain (bits q + 4),
      r.Has (fun i => List.ofFn (fun j : Fin (n i) => mark (B ⟨i, j⟩))) ∧
        ∀ q, ‖meaning (bits q + 2) (bits q + 4) (B q) - Fourier.phase (m q) (z q)‖ ≤
          (1 / 2 : ℝ) ^ bits q := by
  obtain ⟨B, run, accuracy⟩ := computeAngle bits hp z hz m hm pos
  exact ⟨B, harvest n hn (fun i j => mark (B ⟨i, j⟩)) run, accuracy⟩

/-- One program works on every header. Its result has two `bits + 5`-bit words
in P192's signed dyadic encoding, with Euclidean error at most `2^(-bits)`. -/
theorem computeRoot :
    ∃ output : (q : Query) → Grain (q.bits + 4),
      Task.BT Query.inputSize (fun q => send q.payload) (fun q => send (mark (output q))) ∧
        ∀ q : Query, ‖meaning (q.bits + 2) (q.bits + 4) (output q) -
          Fourier.phase (value q.denominator) (whole q.numerator)‖ ≤ (1 / 2 : ℝ) ^ q.bits := by
  have hpayload : regime.Has Query.payload := regime.self
  have hp : Realizes regime Query.bits := hpayload.ez Easy.fst
  have hs : Signed regime (fun q => whole q.numerator) :=
    ⟨Query.numerator, (hpayload.ez Easy.snd).ez Easy.fst, fun _ => rfl⟩
  have hd : Figure regime (fun q => value q.denominator) :=
    ⟨Query.denominator, (hpayload.ez Easy.snd).ez Easy.snd, fun _ => rfl⟩
  exact computeAngle _ hp _ hs _ hd Query.positive

/-- The same generator compiled to a finite-alphabet multitape machine. The
polynomial bound covers head moves and the transfer to a separate output tape. -/
theorem computeRootOnTapes :
    ∃ output : (q : Query) → Grain (q.bits + 4),
      PolyTreeMachine Query.inputSize (fun q => send q.payload) (fun q => send (mark (output q))) ∧
        ∀ q : Query, ‖meaning (q.bits + 2) (q.bits + 4) (output q) -
          Fourier.phase (value q.denominator) (whole q.numerator)‖ ≤ (1 / 2 : ℝ) ^ q.bits := by
  obtain ⟨output, program, accuracy⟩ := computeRoot
  exact ⟨output, polyTreeMachine_of_BT program regime.gauge, accuracy⟩

end PhaseTable

end NearSquareRoot
end Computability
end OAI
