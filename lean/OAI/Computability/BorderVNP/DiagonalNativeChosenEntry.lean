import OAI.Computability.BorderVNP.DiagonalNativeExpansionValue
import OAI.Computability.BorderVNP.TransmissionChosenPacket

/-! # The actual checked tally continuation gives the chosen Fourier matrix entry

The selected reader, the literal board program, the two independent pin arrays and
the serialized exponent arrays all refer to one concrete machine state. Invalid
binary pin encodings give zero under the same physical reader.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing MvPolynomial ResidueBox ResiduePins ResidueEntryInput ResidueIndex ResidueFourier
open DiagonalResidueRAM ResidueRates VPVNP VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator
open scoped Classical BigOperators

variable {K : Type*} [Field K] {D m : ℕ} {ι : Type} [Fintype ι] {G : PaidIdentity K D m}
variable {aux : ι → K} {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
variable {R : CommonField G aux q k s ord} {chart : AdvisedBranch R}
variable [Fact R.p.Prime] [Algebra (ZMod R.p) chart.E] {teams r multBits tally W pin : ℕ}

local notation "h" => pairedTableParameters (k+1) s
local notation "query" => Board.Physical h pin tally (G.Entry ⊕ ι)
local notation "guess" reader => Guess (Fin h) (ChosenReader.gridRank reader) (Nat.clog 2 R.p+1) (Nat.clog 2 R.p)

/-- On the lead team, a genuine completed occurrence and tally run contributes the
entry of the chosen reader at its substituted row, original live column and exact
parameter and gadget exponents. The board program is the one in the native literal. -/
theorem ChosenReader.tallyValue_entry (reader : ChosenReader chart teams r multBits tally W pin)
    (pub : Arg → Word W) (mac : TeamOpcode.Macros W 8) (bank : Bank W) (mem : Memory W)
    (occurrences : Code) (det : occurrences.deterministic = true) (unsgn : occurrences.unsigned = true)
    {es post out} (run : Runs pub mac (finishExpansion occurrences) bank mem es post out)
    (lead : out (pub 0).val = 0) (base entry dense row col totals : ℕ) (extension : Fin 81 → Word W)
    (layout : DiagonalResidueRAM.Layout base entry dense
      (sourceAddress row col totals ∘ (Fintype.equivFin query).symm) (Fintype.card (guess reader)) reader.gates W)
    (room : (pub 0).val+30 < 2^W)
    (control : packFrame pub out dense entry (6+3*reader.gates+Fintype.card query))
    (literal : DiagonalTallyBits.WordsAt out dense
      ((reader.nativePacket base entry row col totals extension).entry.map wordBits))
    (rowBits colBits : Fin ((h+2)*pin) → Bool) (μ : Fin h →₀ ℕ) (δ : G.Entry ⊕ ι → ℕ)
    (rowImage : ∀ j, out (row+j.val) = wordBit W (rowBits j)) (colImage : ∀ j, out (col+j.val) = wordBit W (colBits j))
    (powers : ∀ (i : Fin h) (j : Fin tally), out (totals+i.val*tally+j.val) = wordBit W ((μ i).testBit j.val))
    (gadgets : ∀ (i : G.Entry ⊕ ι) (j : Fin tally), out (totals+(h+(Fintype.equivFin (G.Entry ⊕ ι) i).val)*tally+j.val) =
      wordBit W ((δ i).testBit j.val))
    (range : ResidueIndex.Fits (chart.pinRadius teams r) (parameterShift μ))
    (widthP : ∀ i, μ i < 2^tally) (multiplicity : ∀ i, δ i < 2^multBits) (widthG : ∀ i, δ i < 2^tally) :
    let codec := boxPinCodec h reader.rankFits reader.boxFits
    (tallyValue pub mac bank mem occurrences det : ZMod R.p) =
      (codec.decode rowBits).elim 0 fun i => (codec.decode colBits).elim 0 fun j =>
        entryWeight R.p (Module.finBasis (ZMod R.p) chart.E) (chart.pinRadius teams r) (R.p^reader.power)
          (pow_pos R.prime.pos reader.power) (signedEquations chart.E k s ord chart.advice) μ i j
          (∏ l, chart.gadgets l ^ δ l) := by
  intro codec
  rw [tallyValue_of_return pub mac bank mem occurrences det unsgn run,leadMultiplicity,ite_eq_left lead]
  push_cast
  exact reader.counts W pub mac (leadBank pub post out) out base entry dense row col totals layout room control
    literal rowBits colBits μ δ rowImage colImage powers gadgets range widthP multiplicity widthG

/-- The same completed tally on every other team supplies the Boolean unit factor. -/
theorem tallyValue_otherTeam {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (bank : Bank w) (mem : Memory w)
    (occurrences : Code) (det : occurrences.deterministic = true) (unsgn : occurrences.unsigned = true)
    {es post out} (run : Runs pub mac (finishExpansion occurrences) bank mem es post out) (other : out (pub 0).val ≠ 0) :
    tallyValue pub mac bank mem occurrences det = 1 := by
  rw [tallyValue_of_return pub mac bank mem occurrences det unsgn run,leadMultiplicity,ite_eq_right other]

end Diagonal

end BorderVNP
end Computability
end OAI
