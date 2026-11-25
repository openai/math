import OAI.Computability.BorderVNP.DiagonalRealizedColumn

/-! # Concrete input to the live program at a boundary point

The public program receives a distinguished index and the staged Boolean
circuit for a matrix entry. The residue eigenvector is used in the proof and
occupies no part of the processor input.
-/

namespace OAI
namespace Computability
namespace BorderVNP

set_option maxHeartbeats 2000000
set_option maxRecDepth 6000

namespace Diagonal

open Branch Crossing MvPolynomial ResidueBox ResiduePins ResidueEntryInput
open DiagonalResidueRAM ResidueRates VPVNP
open scoped Classical BigOperators

variable {K : Type*} [Field K] {D m : ℕ} {ι : Type} [Fintype ι] {G : PaidIdentity K D m}
variable {aux : ι → K} {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
variable {R : CommonField G aux q k s ord}

/-- The box radius used simultaneously for the live and substituted pin. -/
noncomputable abbrev AdvisedBranch.pinRadius (chart : AdvisedBranch R) (teams r : ℕ) : ℕ :=
  radius (batchDegree teams (pairedTableParameters (k+1) s) r k) chart.degreeSum

/-- A field and pin reader, with all its concrete counting and memory resources.
The basis is shared with the matrix action. The pin only names the distinguished
coordinate, and the finite verifier accepts the matrix-entry witnesses. -/
structure ChosenReader (chart : AdvisedBranch R) [Fact R.p.Prime] [Algebra (ZMod R.p) chart.E]
    (teams r multBits tally word pin : ℕ) where
  /-- Exponent in the extraction power of the prime characteristic. -/
  power : ℕ
  positive : 0 < power
  fixes : ∀ a : chart.E, a^(R.p^power) = a
  /-- The one index that the unit branch is programmed to recognize. -/
  star : Index (Fin (Module.finrank (ZMod R.p) chart.E)) (Fin (pairedTableParameters (k+1) s))
    (chart.pinRadius teams r)
  rankFits : Module.finrank (ZMod R.p) chart.E ≤ 2^pin
  boxFits : 2*(chart.pinRadius teams r) < 2^pin
  /-- Cardinality of the finite interpolation field. -/
  gridCard : ℕ
  /-- Number of prime-field limbs in an interpolation-grid element. -/
  gridRank : ℕ
  /-- Length of the actual gate program supplied in the literals. -/
  gates : ℕ
  /-- Shared Boolean program reading the two pins, subtotals and finite-field guesses. -/
  circuit : BooleanTranscript.Circuit (Fin (Fintype.card
    (Board.Physical (pairedTableParameters (k+1) s) pin tally (G.Entry ⊕ ι) ⊕
      Guess (Fin (pairedTableParameters (k+1) s)) gridRank (Nat.clog 2 R.p+1) (Nat.clog 2 R.p)))) gates
  counts : StagedEntries
    (Guess (Fin (pairedTableParameters (k+1) s)) gridRank (Nat.clog 2 R.p+1) (Nat.clog 2 R.p))
    (Module.finBasis (ZMod R.p) chart.E) (R.p^power) (chart.pinRadius teams r)
    (pow_pos R.prime.pos power) rankFits boxFits
    (signedEquations chart.E k s ord chart.advice) chart.gadgets multBits tally circuit

variable {chart : AdvisedBranch R} [Fact R.p.Prime] [Algebra (ZMod R.p) chart.E]
variable {teams r multBits tally word pin : ℕ}

/-- The bit, register and execution cost of the actual selected reader. -/
noncomputable def ChosenReader.charge (reader : ChosenReader chart teams r multBits tally word pin) : ℕ :=
  let Q := R.p^reader.power
  let sizes : ReaderSizes :=
    ⟨pairedTableParameters (k+1) s, adviceGateBudget (2*(k+1)) k s, Fintype.card (G.Entry ⊕ ι),
      multBits, pin, tally, Module.finrank (ZMod R.p) chart.E, reader.gridRank, word, R.p, Q,
      chart.pinRadius teams r,(Q-1)*chart.degreeSum,reader.gridCard⟩
  sizes.stagedCharge reader.gates

/-- The exact typed certificate that the native packing and evaluation program
must supply on the chosen chart and reader. -/
abbrev ChosenReader.Realization {teamsPred : ℕ}
    (reader : ChosenReader chart (teamsPred+1) r multBits tally word pin)
    (t link inner : ℕ) (Edge : Type) [Fintype Edge] :=
  RealizedBranchColumn (Module.finBasis (ZMod R.p) chart.E) (pow_pos R.prime.pos reader.power)
    ord (signedEquations chart.E k s ord chart.advice) chart.gadgets reader.rankFits reader.boxFits
    reader.star teamsPred r t link inner Edge

/-- The chart construction chooses a charged reader such that a correct realization
on a specified physical wire system would give the diagonal contradiction. -/
theorem exists_chosen_reader (G : PaidIdentity K D m) (aux : ι → K) :
    ∃ A C : ℕ, ∀ {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
      {R : CommonField G aux q k s ord} (chart : AdvisedBranch R)
      (teamsPred r multBits tally word T link : ℕ) (Edge : Type) [Fintype Edge],
      ReaderInputs chart (teamsPred+1) r multBits T → tally ≤ T → word ≤ T →
      letI : Fact R.p.Prime := ⟨R.prime⟩
      letI : Algebra (ZMod R.p) chart.E := ZMod.algebra _ _
      ∃ reader : ChosenReader chart (teamsPred+1) r multBits tally word (T+6),
        reader.charge ≤ A*(T+1)^C ∧ ∀ t inner, IsEmpty (reader.Realization t link inner Edge) := by
  obtain ⟨A,C,stage⟩ := staged_chart_data G aux
  refine ⟨A,C,?_⟩
  intro q k s ord R chart pred r mb tally word T link Edge _ inputs ht hw
  let : Fact R.p.Prime := ⟨R.prime⟩
  let : Algebra (ZMod R.p) chart.E := ZMod.algebra _ _
  let h := pairedTableParameters (k+1) s
  obtain ⟨e,he,fixes,_,star,_,fail,hd,hH,N,d',gates,cost,circuit,counts⟩ :=
    stage (Fin ((h+2)*(T+6))) (Layout.Wire pred r link Edge) chart (pred+1) r mb tally word T inputs ht hw
  let reader : ChosenReader chart (pred+1) r mb tally word (T+6) :=
    ⟨e,he,fixes,star,hd,hH,N,d',gates,circuit,counts⟩
  exact ⟨reader,cost,fun _ _ => ⟨fun col => col.contradiction fail⟩⟩

end Diagonal

end BorderVNP
end Computability
end OAI
