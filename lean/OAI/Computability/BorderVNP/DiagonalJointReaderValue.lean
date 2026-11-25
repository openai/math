import OAI.Computability.BorderVNP.DiagonalJointAcceptedTerms
import OAI.Computability.BorderVNP.DiagonalPositiveFiber

/-! # The actual matrix entry left on a globally accepted physical assignment -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PositiveTeam

open VPVNP.BurstRAM TeamContraction CompactMachine CellMacro.Generator BorderVNP.Cube
open scoped Classical

variable {dim box lanes selectors symbols w n : ℕ} {id : TableEntry dim box lanes selectors symbols → ℕ}
    {gen : Fragment IO} (S : PositiveTeam id gen n w)

/-- The unique returning deterministic subtotal computation on a passing
prepared assignment. Its output memory contains the serialized totals. -/
noncomputable def finish (p : S.Prefix) (ok : S.tallyReturns p) :
    Returns (finishExpansion signedOccurrences) S.pub (install gen n S.routines)
      (cellBank S.pub (install gen n S.routines) p.2.val.2.1 p.2.val.2.2) p.2.val.2.2 :=
  ok.some

/-- A returning nonlead tally has exactly the unit continuation weight. -/
theorem other_reader_one (p : S.Prefix) (ok : S.tallyReturns p)
    (other : (S.finish p ok).val.2.2 (S.pub 0).val ≠ 0) : S.readerWeight p = 1 :=
  Diagonal.tallyValue_otherTeam _ _ _ _ signedOccurrences signedOccurrences_deterministic (by decide)
    (S.finish p ok).property other

end RoutingISA.Evaluator.PositiveTeam

namespace Diagonal

open Branch Crossing MvPolynomial ResidueBox ResiduePins ResidueEntryInput ResidueIndex ResidueFourier
open DiagonalResidueRAM ResidueRates VPVNP VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator CellMacro.Generator
open BorderVNP.Cube
open scoped Classical BigOperators

variable {K : Type} [Field K] {D m : ℕ} {ι : Type} [Fintype ι] {G : PaidIdentity K D m}
    {aux : ι → K} {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
    {R : CommonField G aux q k s ord} {chart : AdvisedBranch R}
    [Fact R.p.Prime] [Algebra (ZMod R.p) chart.E]
    {teamPred r multBits tally w pin exp : ℕ} (reader : ChosenReader chart (teamPred+1) r multBits tally w pin)

local notation "h" => pairedTableParameters (k+1) s
local notation "query" => Board.Physical h pin tally (G.Entry ⊕ ι)
local notation "guess" reader => Guess (Fin h) (ChosenReader.gridRank reader) (Nat.clog 2 R.p+1) (Nat.clog 2 R.p)

/-- Physical lead-team receipt on the native memory produced by its genuine
finished subtotal stage. Its fields name actual locations and bytes, not
an assertion that a contraction or a matrix has the desired value. -/
structure ReaderImage (pub : Arg → Word w) (out : Memory w)
    (rowBits colBits : Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool)
    (μ : Fin (pairedTableParameters (k+1) s) →₀ ℕ) (δ : G.Entry ⊕ ι → ℕ) where
  /-- Packed reader's public work registers and source addresses. -/
  base : ℕ
  /-- Start of the native residue entry's working region. -/
  entry : ℕ
  /-- Packed literal containing its actual gate program. -/
  dense : ℕ
  /-- Substituted binary index. -/
  row : ℕ
  /-- Live binary index. -/
  col : ℕ
  /-- Binary subtotal word array. -/
  totals : ℕ
  /-- The same extended directory stored in the native packet. -/
  extension : Fin 81 → Word w
  /-- Physical output of the finite-field staged reader is allocated in this word range. -/
  layout : DiagonalResidueRAM.Layout base entry dense
    (sourceAddress row col totals ∘ (Fintype.equivFin query).symm) (Fintype.card (guess reader)) reader.gates w
  /-- The startup frame fits the public address space. -/
  frame : (pub 0).val+30 < 2^w
  /-- Native read of the finite circuit header. -/
  control : packFrame pub out dense entry (6+3*reader.gates+Fintype.card query)
  /-- The bytes of the actual advised circuit remain at the addressed memory range. -/
  literal : DiagonalTallyBits.WordsAt out dense ((reader.nativePacket base entry row col totals extension).entry.map wordBits)
  /-- Every named original bit of the substituted row is present. -/
  rowImage : ∀ j, out (row+j.val) = wordBit w (rowBits j)
  /-- Every original bit of the independent live column is present. -/
  colImage : ∀ j, out (col+j.val) = wordBit w (colBits j)
  /-- The accumulated parameter exponents occupy their numbered coordinates. -/
  powers : ∀ (i : Fin h) (j : Fin tally), out (totals+i.val*tally+j.val) = wordBit w ((μ i).testBit j.val)
  /-- Every gadget coordinate is the true sum of its occurrence multiplicities. -/
  gadgets : ∀ (i : G.Entry ⊕ ι) (j : Fin tally), out (totals+(h+(Fintype.equivFin (G.Entry ⊕ ι) i).val)*tally+j.val) =
    wordBit w ((δ i).testBit j.val)

variable {dim box lanes selectors symbols n : ℕ} {id : TableEntry dim box lanes selectors symbols → ℕ}
    {gen : Fragment IO} (S : Fin (teamPred+1) → PositiveTeam id gen n w)
    (joint : ∀ a : (u : Fin (teamPred+1)) → (S u).Prefix,
      JoinedCells (fun u => (S u).pub) (fun u => (S u).postMemory) (fun u => (S u).generated) a)
    (a : PositiveAssignment S joint) (ok : positivePass S joint a)

/-- Reduction of this actual accepted joint term. All nonlead subtotal
continuations return one. The lead team's genuine circuit handles the
independently guessed raw pin, including out-of-range codes. -/
theorem joint_entry (rowBits : Fin ((h+2)*pin) → Bool) (j : Index (Fin (Module.finrank (ZMod R.p) chart.E))
    (Fin h) (chart.pinRadius (teamPred+1) r)) (t : Tally (Fin (teamPred+1)) (Fin h) (G.Entry ⊕ ι) exp)
    (sign : (joint a.1).privateWeight a.2 = 1)
    (team : ∀ u, ((S u).finish (a.1 u) (ok.2 u)).val.2.2 ((S u).pub 0).val = u.val)
    (I : ReaderImage reader (S 0).pub ((S 0).finish (a.1 0) (ok.2 0)).val.2.2 rowBits
      ((boxPinCodec h reader.rankFits reader.boxFits).encode j) t.exponents (fun l => ∑ u, t.counts u l))
    (range : ResidueIndex.Fits (chart.pinRadius (teamPred+1) r) (parameterShift t.exponents))
    (widthP : ∀ i, t.exponents i < 2^tally)
    (multiplicity : ∀ l, ∑ u, t.counts u l < 2^multBits)
    (widthG : ∀ l, ∑ u, t.counts u l < 2^tally) :
    let codec := boxPinCodec h reader.rankFits reader.boxFits
    (positiveWeight S joint a : ZMod R.p) = (codec.decode rowBits).elim 0 fun i =>
      entryWeight R.p (Module.finBasis (ZMod R.p) chart.E) (chart.pinRadius (teamPred+1) r) (R.p^reader.power)
        (pow_pos R.prime.pos reader.power) (signedEquations chart.E k s ord chart.advice) t.exponents i j
        (t.coefficient chart.gadgets) := by
  intro codec
  unfold positiveWeight
  rw [sign,one_mul,Finset.prod_eq_single (0 : Fin (teamPred+1))]
  · have read := reader.tallyValue_entry (S 0).pub _ _ _ signedOccurrences signedOccurrences_deterministic (by decide)
      ((S 0).finish (a.1 0) (ok.2 0)).property (Fin.ext (team 0)) I.base I.entry I.dense I.row I.col I.totals I.extension
      I.layout I.frame I.control I.literal rowBits (codec.encode j) t.exponents (fun l => ∑ u, t.counts u l)
      I.rowImage I.colImage I.powers I.gadgets range widthP multiplicity widthG
    have back : (boxPinCodec h reader.rankFits reader.boxFits).decode (codec.encode j) = some j :=
      (codec.decode_eq_some (codec.encode j) j).mpr rfl
    change _ = (codec.decode rowBits).elim 0 _ at read
    simp only [back,Option.elim_some] at read
    refine read.trans ?_
    unfold Tally.coefficient
    congr 1
  · intro u _ other
    exact (S u).other_reader_one (a.1 u) (ok.2 u) (fun eq => other (Fin.ext ((team u).symm.trans (congrArg Fin.val eq))))
  · simp

end Diagonal

end BorderVNP
end Computability
end OAI
