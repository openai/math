import OAI.Hierarchy.DescentAtomSchedule
import OAI.Hierarchy.DescentStagePairCensus

namespace OAI
/-! # The grouped physical stage contributes at most one scheduled batch of atoms -/

namespace Hierarchy.DescentSixParty.GroupStage
open DescentCompiler
open scoped Classical BigOperators
noncomputable section

variable {F P : Type} [Field F] {d k : ℕ} {bits : P→ℕ}
variable {W : MarkedWorld F d P bits} {G : PoweredGadget F} {J V : Type}
    [Fintype J] [Fintype V] [DecidableEq J] [DecidableEq V] {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (S : AtomSchedule)

local notation "oldCount" => (∑u,List.length (A.records u))
local notation "pairBound" => (W.liveWidth/(2*(A.z*G.b)))

/-- Applies the physical block-capacity census before any coloring or matching is selected. -/
theorem scanned_births {i : ℕ} (age : i≤S.length) (positions : Fintype.card V≤S.hostSize i)
    (groups : Fintype.card J≤S.groupCount i) (blockSize : 2^k≤S.radix)
    (capacity : A.cap≤2^(8+S.capGain*i)) : 6*pairBound≤S.batch := by
  apply S.ordinary_reserve age positions (Nat.mul_le_mul groups blockSize) capacity
  simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using A.live_pairs_le_capacity

/-- Discharge the exact pessimistic atom invoice of the deterministic physical transition,
and carry the realized (possibly smaller) birth count to its actual successor. -/
theorem scanned_atom_ledger {i : ℕ} (positive : 0<S.height) (historyCost : 0<A.hist)
    (age : i<S.length) (positions : Fintype.card V≤S.hostSize i)
    (groups : Fintype.card J≤S.groupCount i) (blockSize : 2^k≤S.radix)
    (capacity : A.cap≤2^(8+S.capGain*i)) (past : S.Within i oldCount)
    (priceEq : price=1/((A.hist:ℝ)*(S.epochPower:ℝ)^S.priceExponent))
    (epsEq : ε=((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower) :
    price*A.hist*((oldCount+6*pairBound:ℕ):ℝ)≤ε ∧
      ∀ pairs : ℕ,2*pairs*(A.z*G.b)≤W.liveWidth→S.Within (i+1) (oldCount+6*pairs) := by
  have allot := A.scanned_births S age.le positions groups blockSize capacity
  constructor
  · have charge := congrArg (fun rate : ℝ => rate * A.hist * ((oldCount + 6 * pairBound : ℕ) : ℝ)) priceEq
    exact charge.le.trans ((S.paid positive historyCost age (S.advance past allot)).trans_eq epsEq.symm)
  · intro pairs fits
    have hbase : 0<G.b := by have := G.paid;omega
    have hw : 0<2*(A.z*G.b) := Nat.mul_pos (by decide) (Nat.mul_pos A.unitPos hbase)
    have counted : pairs*(2*(A.z*G.b))≤W.liveWidth := by
      simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using fits
    have keep : pairs≤pairBound := (Nat.le_div_iff_mul_le hw).mpr counted
    exact S.advance past ((Nat.mul_le_mul_left _ keep).trans allot)

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
