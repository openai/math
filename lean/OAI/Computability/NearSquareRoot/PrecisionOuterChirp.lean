import OAI.Computability.NearSquareRoot.PrecisionChirpRoots
import OAI.Computability.NearSquareRoot.PrecisionPhaseTable
import OAI.Computability.NearSquareRoot.SynchronizedPaddedChirp

/-! # Polynomial-time setup for the three outer chirp diagonals

A short Fourier axis uses a positive quadratic phase at both ends of its
padded convolution. Restoring the borrowed coordinates uses the two
parity-corrected phases. Each entire row is generated in coordinate order,
including signed angle reduction and fixed-point rounding.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ChirpTable

open IntegerMultiplication Code Strip Staff Carry Brief Dusk Grid

inductive OuterChirp where
  | bluestein
  | periodic
  | reflected

/-- The exact diagonal entry consumed by the corresponding local circuit. -/
noncomputable def OuterChirp.entry (kind : OuterChirp) {a : ℕ} (j : Fin a) : ℂ :=
  match kind with
  | .bluestein => ShortFourier.bluesteinDiagonal a j j
  | .periodic => ShortFourier.chirp a (j.val : ℤ)
  | .reflected => ShortFourier.chirp a (-(j.val : ℤ))

/-- Taking the adjoint of a diagonal conjugates each coefficient. -/
noncomputable def OuterChirp.oriented (kind : OuterChirp) (adjoint : Bool) {a : ℕ} (j : Fin a) :
    ℂ := if adjoint then (starRingEnd ℂ) (kind.entry j) else kind.entry j

private def OuterChirp.numerator (kind : OuterChirp) (a j : ℕ) : ℤ :=
  match kind with
  | .bluestein => (j : ℤ)^2
  | .periodic => (j : ℤ)^2 + (a % 2 : ℕ) * (j : ℤ)
  | .reflected => (j : ℤ)^2 - (a % 2 : ℕ) * (j : ℤ)

private theorem outer_angle (kind : OuterChirp) {a : ℕ} (j : Fin a) :
    Fourier.phase (2*a) (kind.numerator a j.val) = kind.entry j := by
  have hm : (((a : ℤ) % 2 : ℤ) : ℝ) = ((a % 2 : ℕ) : ℝ) := Int.cast_natCast _
  cases kind <;>
    simp only [OuterChirp.numerator, OuterChirp.entry, ShortFourier.bluesteinDiagonal,
      Matrix.diagonal_apply_eq, ShortFourier.chirp, ShortFourier.chirpAngle,
      short_phase_cis, Fourier.phase] <;>
    congr 1 <;> push_cast [-Int.natCast_mod] <;> (try rw [hm]) <;> ring

private theorem signed_angle (kind : OuterChirp) (adjoint : Bool) {a : ℕ} (j : Fin a) :
    Fourier.phase (2*a) (if adjoint then -kind.numerator a j.val else kind.numerator a j.val) =
      kind.oriented adjoint j := by
  cases adjoint with
  | false => exact outer_angle kind j
  | true =>
    simp only [OuterChirp.oriented, ite_true, Fourier.phase_neg]
    rw [← outer_angle kind j, Fourier.phase, ← short_phase_cis, ShortFourier.phase_conj]

/-- On a setup stack with unary axis length and precision, one fixed program
generates the entire row for the requested diagonal. Its numerical error is
uniform over the row. -/
theorem outerChirpRow {J : Type} {s : Regime J} (kind : OuterChirp)
    {a bits : J → ℕ} (A : Realizes s a) (P : Realizes s bits)
    {adjoint : J → Bool} (D : s.Has adjoint) :
    ∃ B : (i : J) → Fin (a i) → Grain (bits i + 4),
      s.Has (fun i => List.ofFn (fun j => mark (B i j))) ∧
      ∀ i j, ‖meaning (bits i + 2) (bits i + 4) (B i j) - kind.oriented (adjoint i) j‖ ≤
        (1 / 2 : ℝ) ^ bits i := by
  let E := signal a A
  let H := Figure.of_spoken (floor_ a A)
  let L := Figure.of_spoken (landing a A a A)
  have t := Signed.up H
  have sq := t.multiplying t
  have lin := (Signed.up (L.modded (Figure.natural 2))).multiplying t
  have hnum : Signed E (fun x : Across a => kind.numerator (a x.1) x.2.val) := by
    cases kind <;> simp only [OuterChirp.numerator, pow_two]
    · exact sq
    · exact sq.adding lin
    · exact sq.subtraction lin
  have hflag : E.Has (adjoint ∘ at_ a) := sendRoof a A (send ∘ adjoint) D
  have signedNum := hnum.negative.choose hnum (Classified.learn _ hflag)
  have hden : Figure E (fun x : Across a => 2*a x.1) :=
    (Figure.natural 2).multiplied L
  obtain ⟨B, built, error⟩ := PhaseTable.computeAngleTable a A (bits ∘ at_ a)
    (landing a A bits P) _ signedNum _ hden (fun x => by have := x.2.isLt; omega)
  exact ⟨fun i j => B ⟨i,j⟩, built, fun i j => (signed_angle kind (adjoint i) j) ▸ error ⟨i,j⟩⟩

/-- Header parameters for the local outer diagonals. -/
structure OuterChirpQuery where
  adjoint : Bool
  length : ℕ
  bits : ℕ

def OuterChirpQuery.payload (q : OuterChirpQuery) := (q.adjoint, tally q.length, tally q.bits)

private def rowRegime : Regime OuterChirpQuery where
  header q := send q.payload
  scale q := q.length + q.bits
  gauge := by
    refine ⟨1, 8, fun q => ?_⟩
    change size q.payload ≤ 8 * (q.length + q.bits + 1)^1
    simp only [OuterChirpQuery.payload, size_prod, size_tally, tally_length, pow_one,
      show size q.adjoint = 1 from rfl]
    omega

/-- One finite-tape machine writes the three complete rows for either direction.
Its input encodes the direction bit, unary axis size and unary precision. The
time and distinct visited cells are polynomial in `length + bits`, uniformly
in all three inputs. The rows are in coordinate order in both directions. -/
theorem outerChirpRowsOnTapes :
    ∃ B : OuterChirp → (q : OuterChirpQuery) → Fin q.length → Grain (q.bits + 4),
      PolyTreeMachine (fun q : OuterChirpQuery => q.length + q.bits) (fun q => send q.payload)
        (fun q => send (List.ofFn (fun j => mark (B .bluestein q j)),
          List.ofFn (fun j => mark (B .periodic q j)),
          List.ofFn (fun j => mark (B .reflected q j)))) ∧
      ∀ (kind : OuterChirp) (q : OuterChirpQuery) (j : Fin q.length),
        ‖meaning (q.bits + 2) (q.bits + 4) (B kind q j) - kind.oriented q.adjoint j‖ ≤
          (1 / 2 : ℝ) ^ q.bits := by
  have h : rowRegime.Has OuterChirpQuery.payload := rowRegime.self
  have A : Realizes rowRegime OuterChirpQuery.length := (h.ez Easy.snd).ez Easy.fst
  have P : Realizes rowRegime OuterChirpQuery.bits := (h.ez Easy.snd).ez Easy.snd
  have D : rowRegime.Has OuterChirpQuery.adjoint := h.ez Easy.fst
  obtain ⟨b, hb, eb⟩ := outerChirpRow .bluestein A P D
  obtain ⟨f, hf, ef⟩ := outerChirpRow .periodic A P D
  obtain ⟨g, hg, eg⟩ := outerChirpRow .reflected A P D
  let B : OuterChirp → (q : OuterChirpQuery) → Fin q.length → Grain (q.bits + 4)
    | .bluestein => b
    | .periodic => f
    | .reflected => g
  exact ⟨B, polyTreeMachine_of_BT (hb.pair (hf.pair hg)) rowRegime.gauge,
    fun kind => by cases kind <;> assumption⟩

end ChirpTable

end NearSquareRoot
end Computability
end OAI
