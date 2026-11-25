import OAI.Computability.NearSquareRoot.PrecisionChirpSetup
import OAI.Computability.NearSquareRoot.PrecisionPreparedPhase
import OAI.Computability.NearSquareRoot.PrecisionOuterChirp
import OAI.Computability.NearSquareRoot.SynchronizedIdleWalsh

/-! # Prepared coefficients for the restored short Fourier transform -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhaseTable

open IntegerMultiplication Code Strip Staff Carry Dusk Grid ShortFourier ChirpTable

attribute [local irreducible] Nat.clog

variable {J : Type} {s : Regime J} {a r bits : J → ℕ}

/-- The original header supplies the axis, frequency, and output precision.
The one polynomial-time program computes all six finite phase records, including
the normalized Bluestein sum and the fixed amplitude calibration factor. -/
theorem prepareDilation (A : Realizes s a) (P : Realizes s bits) (R : Figure s r)
    (ξ : (j : J) → Fin (r j)) (F : Figure s (fun j ↦ (ξ j).val)) (ha : ∀ j, 0 < a j) :
    ∃ v : (j : J) → Fin 6 → Grain (bits j + 5),
      s.Has (fun j ↦ List.ofFn fun i ↦ mark (v j i)) ∧
      ∀ j i, ‖meaning (bits j + 2) (bits j + 5) (v j i) -
        dilationTable (calibratedMultiplier (a j) (r j) (ξ j)) i‖ ≤ 1 / (2 : ℝ) ^ bits j := by
  let b j := bits j + 17
  have B : Realizes s b := P.plus (.fix 17)
  have W : Realizes s (fun j ↦ sumPrecision (a j) (b j)) :=
    (B.plus (Figure.of_spoken A).short_log).plus (.fix 5)
  have hr j : 0 < r j := Nat.zero_lt_of_lt (ξ j).isLt
  obtain ⟨val,built,err⟩ := prepareBluestein A B R F ha hr
  exact prepareDilationFromMultiplier ξ ha W P val built err

/-- One of the six pair-table entries selected by its actual gate/address
index. Both the query and all table generation run in the same regime. -/
theorem Prepared.dilation (A : Realizes s a) (P : Realizes s bits) (R : Figure s r)
    (ξ : (j : J) → Fin (r j)) (F : Figure s (fun j ↦ (ξ j).val)) (ha : ∀ j, 0 < a j)
    (e : J → Fin 6) (E : Figure s (fun j ↦ (e j).val)) :
    Prepared s bits (fun j ↦ dilationTable (calibratedMultiplier (a j) (r j) (ξ j)) (e j)) := by
  obtain ⟨v, h, err⟩ := prepareDilation A P R ξ F ha
  exact ⟨fun j ↦ v j (e j), selectSix (fun j i ↦ mark (v j i)) h e E, fun j ↦ err j (e j)⟩

/-- Generate the diagonal of the restored chirp convolution and convert the
summation record to the same format used by the dilation and twiddle tables. -/
theorem Prepared.spectrum [∀ j, NeZero (a j)] (A : Realizes s a) (P : Realizes s bits)
    (ξ : (j : J) → Fin (a j)) (F : Figure s (fun j ↦ (ξ j).val)) :
    Prepared s bits (fun j ↦ chirpSpectrum (a j) (ξ j)) := by
  let b j := bits j + 1
  have B : Realizes s b := P.plus (.fix 1)
  have W : Realizes s (fun j ↦ sumPrecision (a j) (b j)) :=
    (B.plus (Figure.of_spoken A).short_log).plus (.fix 5)
  obtain ⟨v, h, err⟩ := prepareSpectrum A B ξ F
  exact Prepared.ofGrain W P v h (fun j ↦ chirpSpectrum_norm (ξ j)) err

/-- A row of coefficients is emitted in increasing address order. The header
must enumerate the row length in unary, as for every short table. -/
theorem Prepared.row {n : J → ℕ} (N : Realizes s n) (z : (j : J) → Fin (n j) → ℂ)
    (h : Prepared (signal n N) (fun j : Across n ↦ bits j.1) (fun j ↦ z j.1 j.2)) :
    ∃ v : (j : J) → Fin (n j) → Grain (bits j + 5),
      s.Has (fun j ↦ List.ofFn fun i ↦ mark (v j i)) ∧
      ∀ j i, ‖meaning (bits j + 2) (bits j + 5) (v j i) - z j i‖ ≤ 1 / (2 : ℝ) ^ bits j := by
  obtain ⟨v, h, err⟩ := h
  exact ⟨fun j i ↦ v ⟨j,i⟩, harvest n N (fun j i ↦ mark (v ⟨j,i⟩)) h,
    fun j i ↦ err ⟨j,i⟩⟩

/-- Prepare any of the three quadratic chirp diagonals, in either orientation.
The requested coordinate is selected on the setup stacks. -/
theorem Prepared.outer (kind : OuterChirp) (A : Realizes s a) (P : Realizes s bits)
    {adj : J → Bool} (Adj : s.Has adj) (index : (j : J) → Fin (a j))
    (I : Figure s (fun j ↦ (index j).val)) :
    Prepared s bits (fun j ↦ kind.oriented (adj j) (index j)) := by
  have B : Realizes s (fun j ↦ bits j + 1) := P.plus (.fix 1)
  obtain ⟨out, ready, err⟩ := outerChirpRow kind A B Adj
  have got := selectTable (fun j i ↦ mark (out j i)) ready index I (diameter a A)
  have hentry (j : J) : ‖kind.entry (index j)‖ = 1 := by
    cases kind <;> simp [OuterChirp.entry, bluesteinDiagonal, chirp, short_phase_cis]
  apply Prepared.ofGrain (B.plus (.fix 2)) P (fun j ↦ out j (index j)) got
  · intro j
    cases h : adj j <;> simpa [OuterChirp.oriented, h] using hentry j
  · intro j
    simpa only [one_div, inv_pow] using err j (index j)

/-- Polynomial setup for the idle half of a controlled Walsh butterfly uses
a fixed lookup of signed eighth-root exponents. -/
theorem Prepared.idleWalsh (P : Realizes s bits)
    (slot : J → Fin 6) (Slot : Figure s (fun j ↦ (slot j).val)) :
    Prepared s bits (fun j ↦ identityTable (slot j)) := by
  simp_rw [identityTable_phase]
  exact Prepared.root P (signedLookup identityExponent slot Slot) (.natural 8) (fun _ ↦ by decide)

end PhaseTable

end NearSquareRoot
end Computability
end OAI
