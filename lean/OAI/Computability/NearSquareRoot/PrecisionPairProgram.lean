import OAI.Computability.NearSquareRoot.PrecisionPairRealization
import OAI.Computability.NearSquareRoot.PhaseProgramRelease
import OAI.Computability.NearSquareRoot.SynchronizedDilationPairs
import OAI.Computability.IntegerMultiplication.Star.Stroke

/-! # Finite-tape setup for all six phases of a dilation pair

A query gives both signed components of a dyadic approximation to the scaled
chirp multiplier. Polynomial setup produces the six coefficients in order,
each in the same finite record format as the main arithmetic passes.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhaseTable

open IntegerMultiplication Code Bits Grid Strip Staff Carry Dusk Brief Star

private theorem collectFixed {J X : Type} [Codec X] {r : Regime J} {n : ℕ}
    {f : Fin n → J → X} (hf : ∀ i, r.Has (f i)) :
    r.Has (fun j => List.ofFn (fun i => f i j)) := by
  induction n with
  | zero => simpa using (Regime.fixed (r := r) ([] : List X))
  | succ n ih =>
    have tail := ih (f := fun i => f i.succ) (fun i => hf i.succ)
    have both := ((hf 0).pair tail).ez Easy.cons
    simpa only [List.ofFn_succ] using both

/-- Generate all six records in one polynomial stack task. The precision of
each stored complex coefficient is two fractional guard bits beyond the
requested output accuracy. The ideal multiplier is used only for the proof. -/
theorem computePairTableAt {J : Type} {r : Regime J} (bits : J → ℕ) (hp : Realizes r bits)
    (q : J → ℚ × ℚ) (hq : PairRealized r q)
    (valid : ∀ j, ∃ z : ℂ, ‖z‖ ≤ 1 / 2 ∧
      ‖toComplex (q j) - z‖ ≤ 1 / (2 : ℝ) ^ (bits j + 11)) :
    ∃ output : (j : J) → Fin 6 → Grain (bits j + 5),
      r.Has (fun j => List.ofFn (fun i => mark (output j i))) ∧
      ∀ (j : J) (z : ℂ), ‖z‖ ≤ 1 / 2 →
        ‖toComplex (q j) - z‖ ≤ 1 / (2 : ℝ) ^ (bits j + 11) →
        ∀ i, ‖meaning (bits j + 2) (bits j + 5) (output j i) -
          ShortFourier.dilationTable z i‖ ≤ 1 / (2 : ℝ) ^ bits j := by
  let c (j : J) (i : Fin 6) := toComplex (chirpPairTable (bits j + 1) (q j) i)
  have approx (j : J) (z : ℂ) (hz : ‖z‖ ≤ 1 / 2)
      (h : ‖toComplex (q j) - z‖ ≤ 1 / (2 : ℝ) ^ (bits j + 11)) :=
    chirpPairTable_error (bits j + 1) (q j) z hz h
  have bounded (j : J) (i : Fin 6) : ‖c j i‖ ≤ 2 := by
    obtain ⟨z, hz, hqz⟩ := valid j
    obtain ⟨e, unit, err, _⟩ := approx j z hz hqz
    have add := norm_add_le (c j i - e i) (e i)
    rw [sub_add_cancel, unit] at add
    have small : 1 / (2 : ℝ) ^ (bits j + 1) ≤ 1 :=
      (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
    exact add.trans (by linarith [show ‖c j i - e i‖ ≤ _ from err i])
  have make (i : Fin 6) :
      ∃ b : (j : J) → Grain (bits j + 5), Satisfactory (fun j => bits j + 5) r b ∧
        ∀ j, ‖meaning (bits j + 2) (bits j + 5) (b j) - c j i‖ ≤
          2 * Star.drop_ (bits j + 2) := by
    have hc : Curve r (fun j => c j i) :=
      chirpPairTable_realizable (fun j => bits j + 1) (hp.plus (.fix 1)) q hq i
    apply Star.stroke _ _ _ (hp.plus (.fix 2)) (hp.plus (.fix 5)) hc
    intro j
    have h := mul_le_mul_of_nonneg_right (bounded j i)
      (show 0 ≤ (2 : ℝ)^(bits j + 2) by positivity)
    change ‖c j i‖ * _ + 2 < _
    rw [pow_add, pow_add]
    rw [pow_add] at h
    norm_num only [Nat.reducePow, OfNat.ofNat, Nat.cast_ofNat] at h ⊢
    linarith [show 1 ≤ (2 : ℝ) ^ bits j from one_le_pow₀ (by norm_num)]
  choose out ready err using make
  refine ⟨fun j i => out i j, collectFixed ready, ?_⟩
  intro j z hz hqz i
  have he : ‖c j i - ShortFourier.dilationTable z i‖ ≤ 1 / (2 : ℝ) ^ (bits j + 1) :=
    chirpPairTable_approximates (bits j + 1) (q j) z hz hqz i
  have hh := (norm_sub_le_norm_sub_add_norm_sub _ (c j i) _).trans
    (add_le_add (err i j) he)
  refine hh.trans ?_
  simp only [Star.drop_, one_div, inv_pow, pow_add]
  ring_nf
  norm_num

/-- Dyadic input with its fractional precision supplied in unary. -/
structure PairPayload where
  bits : ℕ
  frac : ℕ
  x : Grid.S
  y : Grid.S

def PairPayload.approximation (q : PairPayload) : ℚ × ℚ :=
  dyadicPair q.frac (whole q.x) (whole q.y)

/-- A valid header promises a sufficiently accurate approximation to a
multiplier of norm at most one half. Only the payload is loaded on the tape. -/
def PairQuery := {q : PairPayload // ∃ z : ℂ, ‖z‖ ≤ 1 / 2 ∧
  ‖toComplex q.approximation - z‖ ≤ 1 / (2 : ℝ) ^ (q.bits + 11)}

def PairQuery.words (q : PairQuery) : Tally × Tally × Grid.S × Grid.S :=
  (tally q.val.bits, tally q.val.frac, q.val.x, q.val.y)

def PairQuery.inputSize (q : PairQuery) : ℕ :=
  q.val.bits + q.val.frac + q.val.x.2.length + q.val.y.2.length

private def pairRegime : Regime PairQuery where
  scale := PairQuery.inputSize
  header := fun q => send q.words
  gauge := by
    refine ⟨1, 12, fun q => ?_⟩
    change size q.words ≤ 12 * (q.inputSize + 1) ^ 1
    simp only [PairQuery.words, PairQuery.inputSize, size_prod, size_tally, tally_length,
      show size q.val.x.1 = 1 from rfl, show size q.val.y.1 = 1 from rfl, size_word, pow_one]
    omega

/-- One fixed multitape machine, with both physical steps and distinct cells
polynomial in the encoded header length, emits all the phases jointly.
The factorization consists of normalized Walsh transforms and ideal unit
phases; every emitted record approximates its corresponding phase. -/
theorem computePairTableOnTapes :
    ∃ out : (q : PairQuery) → Fin 6 → Grain (q.val.bits + 5),
      PolyTreeMachine PairQuery.inputSize (fun q => send q.words)
        (fun q => send (List.ofFn (fun i => mark (out q i)))) ∧
      ∀ (q : PairQuery) (z : ℂ), ‖z‖ ≤ 1 / 2 →
        ‖toComplex q.val.approximation - z‖ ≤ 1 / (2 : ℝ) ^ (q.val.bits + 11) →
        ∀ i, ‖meaning (q.val.bits + 2) (q.val.bits + 5) (out q i) -
          ShortFourier.dilationTable z i‖ ≤ 1 / (2 : ℝ) ^ q.val.bits := by
  have headers : pairRegime.Has PairQuery.words := pairRegime.self
  have hp : Realizes pairRegime (fun q => q.val.bits) := headers.ez Easy.fst
  have hf : Realizes pairRegime (fun q => q.val.frac) := (headers.ez Easy.snd).ez Easy.fst
  have pair := ((headers.ez Easy.snd).ez Easy.snd)
  have hx : Signed pairRegime (fun q => whole q.val.x) :=
    ⟨fun q => q.val.x, pair.ez Easy.fst, fun _ => rfl⟩
  have hy : Signed pairRegime (fun q => whole q.val.y) :=
    ⟨fun q => q.val.y, pair.ez Easy.snd, fun _ => rfl⟩
  have word {w : PairQuery → Grid.S} (hw : Signed pairRegime (fun q => whole (w q))) :
      RatRealized pairRegime (fun q => ((whole (w q) : ℤ) : ℚ) / 2 ^ q.val.frac) := by
    have den := RatRealized.powTwo (fun q : PairQuery => q.val.frac) hf
    have num : RatRealized pairRegime (fun q => (whole (w q) : ℚ)) := by
      simpa only [RatRealized, Rat.cast_intCast] using Blot.integer hw
    exact RatRealized.positiveDiv num den (fun _ => by positivity)
  have shape : PairRealized pairRegime (fun q : PairQuery => q.val.approximation) :=
    ⟨word hx, word hy⟩
  obtain ⟨out, physical, accuracy⟩ := computePairTableAt _ hp _ shape (fun q => q.property)
  exact ⟨out, polyTreeMachine_of_BT physical pairRegime.gauge, accuracy⟩

end PhaseTable

end NearSquareRoot
end Computability
end OAI
