import OAI.Computability.BorderVNP.DiagonalJointReaderValue
import OAI.Computability.BorderVNP.DiagonalJointExterior

/-! # The accepted native path fiber and its signed prime-field column -/

namespace OAI
namespace Computability
namespace BorderVNP

set_option maxHeartbeats 1200000

namespace Diagonal

open Branch Crossing MvPolynomial ResidueBox ResiduePins ResidueIndex TeamContraction ProcessorSlots
open RoutingISA RoutingISA.Evaluator CellMacro.Generator BorderVNP.Cube
open scoped Classical BigOperators

variable {K : Type} [Field K] {D m : ℕ} {ι : Type} [Fintype ι] {G : PaidIdentity K D m}
    {aux : ι → K} {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
    {R : CommonField G aux q k s ord} {chart : AdvisedBranch R}
    [Fact R.p.Prime] [Algebra (ZMod R.p) chart.E]
    {teamPred r multBits tally w pin exp : ℕ} (reader : ChosenReader chart (teamPred+1) r multBits tally w pin)

local notation "h" => pairedTableParameters (k+1) s
local notation "Raw" => (Fin ((h+2)*pin) → Bool)
local notation "Idx" => Index (Fin (Module.finrank (ZMod R.p) chart.E)) (Fin h) (chart.pinRadius (teamPred+1) r)
local notation "Counts" => Tally (Fin (teamPred+1)) (Fin h) (G.Entry ⊕ ι) exp

variable {dim box lanes selectors symbols n : ℕ} {id : TableEntry dim box lanes selectors symbols → ℕ}
    {gen : Fragment IO} {X : Type} [Fintype X] (S : X → Fin (teamPred+1) → PositiveTeam id gen n w)
    (joint : ∀ x (a : (u : Fin (teamPred+1)) → (S x u).Prefix), JoinedCells (fun u => (S x u).pub)
      (fun u => (S x u).postMemory) (fun u => (S x u).generated) a)
    (Path : (Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool) → Type) [∀ b, Fintype (Path b)]
    (assigned : ∀ b, Path b → Tally (Fin (teamPred+1)) (Fin (pairedTableParameters (k+1) s)) (G.Entry ⊕ ι) exp)

/-- Path-level data for a live native column. The bijection accounts for the
entire exterior, all private pin guesses, public profiles, cube selectors,
shared and local bits, owned cell witnesses and subtotal checks. The memory
image refers to the actual output of the unique finishing run on that path. -/
structure NativeColumnFiber (j : Idx) where
  /-- Decode every accepted complete native assignment, with its inverse. -/
  path : AcceptedExterior S joint ≃ (Σ b : Raw, Path b)
  /-- Passing Boolean private validators contribute unit sign on these cells. -/
  cellSign : ∀ a : AcceptedExterior S joint, (joint a.1 a.2.val.1).privateWeight a.2.val.2 = 1
  /-- The finish stage retained each processor's literal team number. -/
  team : ∀ (a : AcceptedExterior S joint) u, ((S a.1 u).finish (a.2.val.1 u) (a.2.property.2 u)).val.2.2
    ((S a.1 u).pub 0).val = u.val
  /-- Physical lead input to the installed finite-field reader. -/
  image : ∀ a : AcceptedExterior S joint, let p := path a
    let t := assigned p.1 p.2
    ReaderImage reader (S a.1 0).pub ((S a.1 0).finish (a.2.val.1 0) (a.2.property.2 0)).val.2.2 p.1
      ((boxPinCodec h reader.rankFits reader.boxFits).encode j) t.exponents (fun l => ∑ u, t.counts u l)

/-- Sum the values of the complete physical preparations using their decoded
rows and genuine reader-memory images. An invalid substituted raw code is
handled by the reader's real zero contribution. -/
theorem NativeColumnFiber.sum {j : Idx} (F : NativeColumnFiber reader S joint Path assigned j)
    (bounds : ∀ b a, let t := assigned b a
      ResidueIndex.Fits (chart.pinRadius (teamPred+1) r) (parameterShift t.exponents) ∧
      (∀ i, t.exponents i < 2^tally) ∧ (∀ l, ∑ u, t.counts u l < 2^multBits) ∧
      (∀ l, ∑ u, t.counts u l < 2^tally)) :
    let codec := boxPinCodec h reader.rankFits reader.boxFits
    ((∑ a : AcceptedExterior S joint, positiveWeight (S a.1) (joint a.1) a.2.val : ℤ) : ZMod R.p) =
      ∑ i : Idx, ∑ a : Path (codec.encode i), entryWeight R.p (Module.finBasis (ZMod R.p) chart.E)
        (chart.pinRadius (teamPred+1) r) (R.p^reader.power) (pow_pos R.prime.pos reader.power)
        (signedEquations chart.E k s ord chart.advice) (assigned (codec.encode i) a).exponents i j
        ((assigned (codec.encode i) a).coefficient chart.gadgets) := by
  intro codec
  let amount := fun (b : Raw) (a : Path b) (i : Idx) => entryWeight R.p (Module.finBasis (ZMod R.p) chart.E)
    (chart.pinRadius (teamPred+1) r) (R.p^reader.power) (pow_pos R.prime.pos reader.power)
    (signedEquations chart.E k s ord chart.advice) (assigned b a).exponents i j ((assigned b a).coefficient chart.gadgets)
  rw [Int.cast_sum]
  refine (Fintype.sum_equiv F.path _ (fun p => (codec.decode p.1).elim 0 (amount p.1 p.2)) ?_).trans ?_
  · intro a
    let p := F.path a
    obtain ⟨range,powers,mult,gadgets⟩ := bounds p.1 p.2
    exact joint_entry reader (S a.1) (joint a.1) a.2.val a.2.property p.1 j (assigned p.1 p.2)
      (F.cellSign a) (F.team a) (F.image a) range powers mult gadgets
  · rw [Fintype.sum_sigma]
    exact codec.sum_decode_paths Path amount

end Diagonal

end BorderVNP
end Computability
end OAI
