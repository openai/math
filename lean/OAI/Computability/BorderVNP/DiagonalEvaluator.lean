import OAI.Computability.BorderVNP.DiagonalEntry
import OAI.Computability.BorderVNP.DiagonalTallies
import OAI.Computability.BorderVNP.DiagonalPins

/-!
# The evaluator with independent substituted and live indices

Section 11 first guesses the substituted index and one assigned network term.
Only after aggregating the team's gadget and parameter counts does it read
one Fourier matrix entry. This module computes the integer path sum of these
choices and proves its reduction is the corresponding column of the matrix.
Unassigned binary index codes contribute zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open ResiduePins ResidueFourier Module
open scoped BigOperators Classical

variable {σ β ι Team Gadget E K : Type*} [Fintype σ] [Fintype β] [Fintype ι]
    [Fintype Team] [Fintype Gadget] [Field E] [Field K] [Fintype K]
    {p H q b pinBits : ℕ} [Fact p.Prime] [Algebra (ZMod p) E] [Algebra (ZMod p) K]

/-- A fully assigned term supplies each individual unary use bit and each
team's count of every fixed gadget position. -/
structure Tally (Team Param Gadget : Type*) (b : ℕ) where
  /-- Selected parameter powers, separated by substituted batch. -/
  powers : Team → Param → Fin b → Bool
  /-- Occurrence counts for gadget entries, including zero-valued entries. -/
  counts : Team → Gadget → ℕ

/-- Sum the parameter exponents across the teams exactly once. -/
noncomputable def Tally.exponents (t : Tally Team σ Gadget b) : σ →₀ ℕ :=
  ∑ team, batchExponent (t.powers team)

/-- Reconstruct the coefficient of a fully assigned term from the scalar subtotals. -/
noncomputable def Tally.coefficient (values : Gadget → E) (t : Tally Team σ Gadget b) : E :=
  ∏ g, values g ^ (∑ team, t.counts team g)

/-- The finite integer evaluation mode for a supplied live pin. Its physical
branches choose the row, assigned term, interpolation grid, and threshold. -/
noncomputable def evaluationMode (B : Basis β (ZMod p) E) (φ : E →ₐ[ZMod p] K)
    (enc : K ≃ Fin (Fintype.card K)) (projection : β → K →ₗ[ZMod p] ZMod p)
    (g : ι → MvPolynomial (Option σ) E) (values : Gadget → E)
    {Path : Index β σ H → Type*} [∀ i, Fintype (Path i)]
    (assigned : ∀ i, Path i → Tally Team σ Gadget b) (q : ℕ)
    (codec : PinCodec (Index β σ H) pinBits) (h : Index β σ H) : ℤ :=
  ∑ bin, (codec.decode bin).elim 0 (fun i => ∑ path, ∑ guess : EntryChoices σ K p,
    let t := assigned i path
    entryBranch B φ enc projection q g (t.coefficient values) t.exponents i h guess)

/-- For every live pin, reduction of the full evaluation mode is the sum
of the selected entries of the actual substituted row polynomials. The
coordinate advice is independent of all expansion and pin guesses. -/
theorem evaluationMode_reduction (B : Basis β (ZMod p) E) (φ : E →ₐ[ZMod p] K)
    (enc : K ≃ Fin (Fintype.card K)) (g : ι → MvPolynomial (Option σ) E)
    (hq : 0 < q) (hwidth : (q - 1) * ∑ t, (g t).totalDegree < Fintype.card Kˣ)
    (values : Gadget → E) {Path : Index β σ H → Type*} [∀ i, Fintype (Path i)]
    (assigned : ∀ i, Path i → Tally Team σ Gadget b) (codec : PinCodec (Index β σ H) pinBits) :
    ∃ projection : β → K →ₗ[ZMod p] ZMod p, ∀ h,
      (evaluationMode B φ enc projection g values assigned q codec h : ZMod p) =
        ∑ i, pinEntry (entryWeight p B H q hq g) i h
          (∑ path, MvPolynomial.monomial (assigned i path).exponents
            ((assigned i path).coefficient values)) := by
  obtain ⟨projection, _, correct⟩ := exists_entry_reader (σ := σ) (ι := ι) B φ enc
  refine ⟨projection, fun h => ?_⟩
  rw [evaluationMode, codec.sum_decode]
  simp only [map_sum, pinEntry_monomial, Int.cast_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun path _ => ?_
  simpa only [Int.cast_sum] using
    (correct H q hq g hwidth ((assigned i path).coefficient values)
      (assigned i path).exponents i h).symm

end Diagonal

end BorderVNP
end Computability
end OAI
