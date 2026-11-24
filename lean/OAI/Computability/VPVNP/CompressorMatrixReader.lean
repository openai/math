import OAI.Computability.VPVNP.MacaulayOrdinary
import OAI.Computability.VPVNP.MacaulayFieldReadback
import OAI.Computability.VPVNP.MacaulaySignedRow
import OAI.Computability.VPVNP.MacaulayPinRow
import OAI.Computability.VPVNP.MacaulayAppendedPower
import OAI.Computability.VPVNP.CompressorReaderBudgets

/-! # The augmented matrix reader for the compressor's actual finite model

The entry routine is a single finite bit-stack program. On every queried row
and column, including all original grammar and fixed compressor equations,
it returns the encoded scalar in the determinant algorithm's matrix. Its
reusable advice and workspace have a separate stack-height bound, independent
of the exponentially longer clock.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.BlockSchedule.Templates

open LabelEvaluator JointLabelSystem MvPolynomial RadicalCertificate.MonomialIndex
open RankQuery.Stack RankQuery.Stack.MacaulayRead RankQuery.Stack.Coordinate.SliceMinors
open RAMTape SliceArithmetic
open scoped Classical

local instance nativeEntryPrime (p : Nat.Primes) : Fact p.val.Prime := ⟨p.prop⟩

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 6000 in
set_option synthInstance.maxSize 3000 in
/-- All coefficients of the actual encoded augmented Macaulay matrix are
computed on the physical scalar-entry ABI required by the rank engine. -/
theorem compressorMatrixReader (q c : ℕ) {n w v e : ℕ} (hn : 2 ≤ n) {p : Nat.Primes} [NeZero e]
    {m : Vector p.val e} [Fact (Irreducible (modulus m))]
    (M : Model p (B.compressorDegree n) (B.compressorEquations hn c))
    (φ : AdjoinRoot (modulus m) ≃ₐ[ZMod p.val] Ground p (B.compressorLabelCount c n) (B.compressorDegree n))
    (hp : q ≠ 0 → p.val = q) (hz : q = 0 → p.val ≤ 2^B.compressorPrimeBits c n)
    (hw : (B.compressorReaderPlan q c n).wordWidth ≤ w)
    (he : e ≤ B.readerDegreeBudget q c n) (hv : v ≤ B.readerLimbBudget q c n)
    (working : SliceArithmetic.Word.workingWidth p.val ≤ v) (sp ex : ℕ)
    (hspace : SignedLeaf.callSpace B.Entry B.EquationIndex B.equation c hn w v m ≤ sp)
    (htime : SignedLeaf.callTime B.Entry B.EquationIndex B.equation c hn w v m ≤ 2^ex) :
    let Q := M.queryData (B.compressorCoeff hn c)
    let plan := B.compressorReaderPlan q c n
    let E := B.readerDegreeBudget q c n
    let V := B.readerLimbBudget q c n
    let L := JointScalar.Leaf.layout B.Entry B.EquationIndex B.equation c hn w p.val e v
    CorrectSpace ordinaryReader (baseMatrix φ Q) w v (plan.readTime E V w sp ex) (plan.armSpace E V w sp)
      (BaseAdvice.ready (2^n+Fintype.card B.EquationIndex) Q L m w v M.pins (AffinePin.Query.encode φ ∘ M.values)) := by
  intro Q plan E V L
  let vals := AffinePin.Query.encode φ ∘ M.values
  let aux := Arms.coefficientAdvice L w v M.pins vals
  let d := BaseAdvice.inputs Q
  let constants := BaseAdvice.scalars m v
  let bank := BaseAdvice.leaf Q L m w v M.pins vals
  let A := plan.live E V w sp
  have cov : plan.Covers Q := (B.compressorReaderCovers q c hn p M hp hz).1
  have hbank : JointScalar.Leaf.bankSize L w (plan.arity*w) ≤ sp :=
    (le_max_right ..).trans ((Nat.le_add_right ..).trans hspace)
  have pre : Arms.Preload (w := w) A d constants aux :=
    Arms.coefficientAdvice_preload (P := plan) rfl he hv hbank M.pins vals d (fun _ => rfl) constants
      (fun b => (Engine.scalar_length v (if b then (1 : Scalar m) else 0)).le)
  have rawCap z : (bank z).length ≤ A := by
    rcases z with ⟨side,x⟩ | x
    · cases x with
      | external f =>
        have hh := PairCall.values_le (d side) (fun _ => []) ([] : List Bool) [] pre.words (pre.arity side)
          (by simp) (by simp) (by simp) f
        cases f <;> first | exact hh | exact Nat.zero_le _
      | internal | scratch => exact Nat.zero_le _
    · cases x with
      | zeroScalar => exact pre.scalars false
      | oneScalar => exact pre.scalars true
      | temp => exact Nat.zero_le _
      | payload j => exact pre.payload j
  have room : max w A + MacaulayRowDispatch.ticks w ≤ plan.armSpace E V w sp := by
    rw [max_eq_right pre.words]
    have b := plan.leaf_bounds w sp ex he hv (d false) rfl
      (cov.degrees.2.1.trans (le_max_right ..)) cov.degrees.2.2
    exact b.2.1.2.2.1
  apply correctSpace_of_arms (M := baseMatrix φ Q) (A := A) (b := plan.addressBits)
    (arms := ordinaryArms) (bound := cov.dispatch) (hw := plan.dispatchWidth.1.trans hw)
    (hbw := plan.dispatchWidth.2.1.trans hw) (ht := plan.dispatchWidth.2.2.trans hw)
    (space := fun s hs z => (show s = bank from hs) ▸ rawCap z) (room := room)
  apply armCorrect_of_blocks
  · intro rs row o j hrow hsource hcol
    obtain ⟨ticks,ht,run⟩ := Arms.signed_row_plan B.Entry B.EquationIndex B.equation c hn φ
      Function.Embedding.inl working plan Q rfl (cov.degrees.2.1.trans (le_max_right ..)) cov.degrees.2.2
      he hv sp ex hspace htime hw rs aux pre (Arms.coefficientAdvice_loaded L w v M.pins vals).1 row o j hrow hsource hcol
    let a := enumeration plan.arity Q.multiplierDegree o
    let b := enumeration plan.arity Q.columnDegree j
    let poly := map (Int.castRingHom (Ground p plan.arity (B.compressorDegree n)))
      (B.compressorEquations hn c (FixedRows.rowIndex B.EquationIndex n row))
    have hcoef : Q.getCoeff (row.castAdd plan.pins) (fun i => b.val i-a.val i) = poly.coeff (b.val-a.val) := by
      let z : Fin plan.arity → ℕ := fun i => b.val i-a.val i
      have hx : exponentVector z = b.val-a.val := Finsupp.ext fun _ => rfl
      have read : Q.getCoeff (row.castAdd plan.pins) = (fun u => (B.compressorCoeff hn c row u : Ground p plan.arity (B.compressorDegree n))) :=
        Fin.addCases_left (motive := fun _ => (Fin plan.arity → ℕ) → Ground p plan.arity (B.compressorDegree n))
          (left := fun i u => (B.compressorCoeff hn c i u : Ground p plan.arity (B.compressorDegree n)))
          (right := fun i => (M.pinCut i).getCoeff) row
      let eq := B.compressorEquations hn c (FixedRows.rowIndex B.EquationIndex n row)
      let cast := Int.castRingHom (Ground p plan.arity (B.compressorDegree n))
      have hc : B.compressorCoeff hn c row z = eq.coeff (b.val-a.val) :=
        (B.compressorCoeff_eq hn c row z).trans (congrArg eq.coeff hx)
      exact (congrFun read z).trans ((congrArg cast hc).trans (coeff_map cast eq (b.val-a.val)).symm)
    have ident := shifted_matrix_entry φ Q (row.castAdd plan.pins) o j
    change _ = (if a.val ≤ b.val then AffinePin.Query.encode φ (Q.getCoeff _ (fun i => b.val i - a.val i)) else 0) at ident
    rw [hcoef] at ident
    refine ⟨ticks,ht,?_⟩
    exact ident.symm ▸ run
  · intro rs row o j hrow hsource hcol
    let sys (i) := map (Int.castRingHom (Ground p plan.arity (B.compressorDegree n))) (B.compressorEquations hn c i)
    obtain ⟨ticks,ht,run⟩ := Arms.pin_row_plan plan Q cov he hv sp ex hw working φ sys M.pins M.values row L hbank
      rs hrow o j hsource hcol
    let a := enumeration plan.arity Q.multiplierDegree o
    let b := enumeration plan.arity Q.columnDegree j
    have hcoef : Q.getCoeff (row.natAdd plan.equations) (fun i => b.val i-a.val i) =
        (SliceGeometry.pinnedEquations sys M.pins M.values (.inr row)).coeff (b.val-a.val) := by
      let z : Fin plan.arity → ℕ := fun i => b.val i-a.val i
      have hx : exponentVector z = b.val-a.val := Finsupp.ext fun _ => rfl
      have read : Q.getCoeff (row.natAdd plan.equations) = (M.pinCut row).getCoeff :=
        Fin.addCases_right (motive := fun _ => (Fin plan.arity → ℕ) → Ground p plan.arity (B.compressorDegree n))
          (left := fun i u => (B.compressorCoeff hn c i u : Ground p plan.arity (B.compressorDegree n)))
          (right := fun i => (M.pinCut i).getCoeff) row
      have polyEq : (M.pinCut row).polynomial = SliceGeometry.pinnedEquations sys M.pins M.values (.inr row) :=
        M.pinCut_polynomial row
      exact (congrFun read z).trans (((M.pinCut row).getCoeff_eq z).trans (congrArg₂ (fun (f : MvPolynomial (Fin plan.arity) (Ground p plan.arity (B.compressorDegree n))) u => f.coeff u) polyEq hx))
    have ident := shifted_matrix_entry φ Q (row.natAdd plan.equations) o j
    change _ = (if a.val ≤ b.val then AffinePin.Query.encode φ (Q.getCoeff _ (fun i => b.val i - a.val i)) else 0) at ident
    rw [hcoef] at ident
    refine ⟨ticks,ht,?_⟩
    exact ident.symm ▸ run
  · intro rs o j hs hj
    obtain ⟨ticks,ht,run⟩ := Arms.appended_power_plan plan Q cov he hv sp ex hw rs aux pre o j hs hj
    refine ⟨ticks,ht,?_⟩
    rw [show baseMatrix φ Q (appended o) j = _ from power_matrix_entry φ Q o j]
    exact run

end Compression.BlockSchedule.Templates

end VPVNP
end Computability
end OAI
