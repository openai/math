import OAI.Computability.VPVNP.RankCoordinatePlannedReads
import OAI.Computability.VPVNP.RankCoordinateSelectedPrepare
import OAI.Computability.VPVNP.RankQueryPrepareResources

/-! # A fixed coordinate callback for both operations of the evaluator

Starting from the raw indexed relation-entry reader, the installed program
performs pivot selection, computes the live target row, executes the two
determinants, divides their outputs and reclaims its workspace. Both operation
tables use the same advice and the same uniform clock and storage bound.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace RankQuery.Stack.Coordinate.CanonicalReader

open RAMTape BurstRAM UniversalCountStack SliceArithmetic
open Cursor
open RadicalCertificate.MonomialIndex RadicalCertificate.MonomialIndex.QueryData
open Evaluator Evaluator.MatrixCallbacks ConcreteResources SliceMinors NativeReader

variable {K F : Type} [DecidableEq K] [Fintype K]

/-- Decide equality of prefix-scan ports using the Gram engine's scan-port representation. -/
local instance : DecidableEq (PrefixPort K) := inferInstanceAs (DecidableEq (ScanPort (GramEngine.Aux K)))
/-- Decide equality of auxiliary ports used while computing the rank of a prefix. -/
local instance : DecidableEq (PrefixWorkspace.Aux (PrefixPort K)) := fun a b => PrefixWorkspace.instDecidableEqAux a b
/-- Compare addresses on one side of the selected-minor advice using their prefix-register
representation. -/
local instance : DecidableEq (SelectedAdvice.Side K) := inferInstanceAs (DecidableEq (PrefixWords.Port (PrefixWorkspace.Aux (PrefixPort K))))
/-- Compare selected-minor ports by distinguishing the row bank, column bank, and scalar
reader. -/
local instance {J : Type} [DecidableEq J] : DecidableEq (SelectedMinor.Host K J) :=
  inferInstanceAs (DecidableEq (SelectedAdvice.Side K ⊕ (SelectedAdvice.Side K ⊕ J)))
/-- Compare working ports of the selected-minor reader using the underlying submatrix
workspace. -/
local instance {J : Type} [DecidableEq J] : DecidableEq (SelectedMinor.Work K J) := fun a b => Submatrix.instDecidableEqWork a b
/-- Decide equality across the disjoint banks used to prepare a selected Cramer query. -/
local instance : DecidableEq (SelectedAdvice.Parts K) := Prepare.partsDecidable

variable [Fintype (SelectedAdvice.Parts K)]

/-- Install the coordinate callback that prepares the two selected minors and divides their top
Schur coefficients. The common determinant sign cancels, yielding the matrix entry with the
next basis index as row and the current one as column. -/
def program (read : FiniteRoutine (MacaulayRead.Port K)) (mode : Bool) :=
  Reader.install (pairCore Prepare.root Prepare.scratch (SelectedAdvice.machine read mode)
    (SelectedMinor.restrictEntry read read) (SelectedMinor.numerator read (ordinary read) powered))

variable [Field F] [DecidableEq F] {p e t eqs d w v B A S : ℕ} [Fact p.Prime] [NeZero e]
    [Algebra (ZMod p) F] {c : Vector p e} [Fact (Irreducible (modulus c))]
    [DecidableEq (AdjoinRoot (modulus c))]

set_option maxHeartbeats 1500000 in
theorem readsEntryWithin (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] F) (Q : QueryData t eqs F)
    (dim : BurstRAM.Word w) (hdim : dim.val = Q.dimension) (op : Operation t)
    (read : FiniteRoutine (MacaulayRead.Port K)) {ready : Stacks K → Prop}
    (hc : MacaulayRead.CorrectSpace read (baseMatrix φ Q) w v B S ready)
    (ha : ∀ a, ready a → ∀ k, (a k).length ≤ A) (base : Stacks K) (hr : ready base)
    (hv : SliceArithmetic.Word.workingWidth p ≤ v) (fit : CanonicalFits Q d w v e A S B) :
    let cost := preparedBudget (SelectedAdvice.Parts K) (SelectedAdvice.Work K) K
      (height Q) (width Q) (order Q) d w v e B A S B t
    ReadsEntryWithin φ dim (SelectedAdvice.selectedExtra c Q w v base) (program read (SelectedAdvice.mode op))
      v (SelectedAdvice.label op) cost.time cost.space (fun i j => Q.matrixEntry op (Fin.cast hdim j) (Fin.cast hdim i)) := by
  let minor := minorBudget K (height Q) (width Q) d w v e B A S B
  let prep := prepareBudget (SelectedAdvice.Parts K) K (height Q) d w v e B A S t
  let V := SelectedMinor.space K d w v e A S
  let peak := pairPeak (order Q) w v e V minor.space prep.space
  obtain ⟨hp,hq,hd⟩ := pairPeak_covers (order Q) w v e V minor.space prep.space
  apply NativeReader.entry_reader (B := minor.time) (S := minor.space) (V := V) (prep := prep.time)
    (peak := peak) Q φ dim hdim op (SelectedAdvice.label op) Prepare.root Prepare.scratch (fun _ => Sum.inl_ne_inr)
    (SelectedAdvice.selectedAdvice c Q w v base) (SelectedAdvice.machine read (SelectedAdvice.mode op))
    (SelectedMinor.restrictEntry read read) (SelectedMinor.numerator read (ordinary read) powered)
    hv fit.widthThree fit.descriptorFit fit.depthFit fit.orderShape fit.orderBound fit.rootFit fit.childFit hq hd
  intro i j
  let cur := Fin.cast hdim i
  let next := Fin.cast hdim j
  let replace := combinedOrdinal Q.equations Q.monomials next
  obtain ⟨dn,nu⟩ := native_reads_of_plan φ Q fit op cur next read hc ha base hr hv
  obtain ⟨dc,nc⟩ := planned_ready_bounds (c := c) Q fit op cur ha base hr replace
  obtain ⟨rd,rn⟩ := SelectedAdvice.prepared_root_ready c Q base hr fit.rowFit op cur next
  have labelBound : SelectedAdvice.label op ≤ t := by cases op with | label i => exact i.isLt.le | frobenius => exact Nat.zero_le _
  have labelFit : SelectedAdvice.label op+1 < 2^w := (Nat.add_le_add_right labelBound 1).trans_lt fit.labelFit
  obtain ⟨u,hu,out,empty,roots,run⟩ := SelectedAdvice.prepare_bounded φ Q op cur next read hc ha base hr fit.rowShape fit.gramFit
    hv fit.wordLive fit.arityLive fit.scalarLive labelFit
  have cover := prepare_mode_covers (SelectedAdvice.Parts K) (SelectedAdvice.mode op) (SelectedAdvice.portBound K d w v e A S)
    (max (SelectedAdvice.portBound K d w v e A S) t) (Select.scanTime K (height Q) d w v e B A S+OrdinalABI.overhead w)
    (SelectedAdvice.selectorCap K d w v e A S) w labelBound
  have input (j : Fin dim.val) : Reader.ordinal dim j = digits w (Fin.cast hdim j).val := by
    unfold Reader.ordinal digits
    apply congrArg wordBits
    exact Fin.ext (Nat.mod_eq_of_lt (j.isLt.trans dim.isLt)).symm
  rw [← input i,← input j] at run
  exact ⟨{
    denominator := denominator φ Q
    numerator := numerator φ Q op cur next
    denMatrix := denominator_map φ Q
    numMatrix := numerator_map φ Q op cur next
    denReady := _
    numReady := _
    denReads := dn
    numReads := nu
    denBound := dc
    numBound := nc
    work := out
    scratchEmpty := empty
    denAux := _
    numAux := _
    denInput := rd
    numInput := rn
    hostInput := roots
    ticks := u
    clock := hu.trans cover.1
    run := run.enlarge (cover.2.trans hp)
  }⟩

end RankQuery.Stack.Coordinate.CanonicalReader

end

end VPVNP
end Computability
end OAI
