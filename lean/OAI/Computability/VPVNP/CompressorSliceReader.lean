import OAI.Computability.VPVNP.CompressorBaseAdvice
import OAI.Computability.VPVNP.CompressorCoordinateBudgets
import OAI.Computability.VPVNP.CompressorEvaluatorInput
import OAI.Computability.VPVNP.CompressorMatrixReader
import OAI.Computability.VPVNP.CompressorReaderTypes
import OAI.Computability.VPVNP.RankCoordinateCanonicalReader

/-! # The two advised physical readers for the actual compressor algebra

At every admissible prime and slice, the same two fixed programs return the
multiplication and Frobenius coordinates. All the initial field, coefficient,
rank and monomial advice is selected before the exponent widths and coordinate
ordinals. A single length-indexed budget bounds both programs.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorReader

open RankQuery.Stack RankQuery.Stack.Coordinate RAMTape Evaluator.MatrixCallbacks

/-- The bit selects the fixed Frobenius or label-multiplication control. The
program and its ports do not depend on the input length or the field. -/
def read (frobenius : Bool) : FiniteRoutine (ReadPort Ports) :=
  CanonicalReader.program MacaulayRead.ordinaryReader frobenius

end CompressorReader

namespace Compression.BlockSchedule.Templates

open LabelEvaluator SliceArithmetic RankQuery.Stack RankQuery.Stack.Coordinate
open ConcreteResources Evaluator.MatrixCallbacks RAMTape RadicalCertificate.MonomialIndex

local instance sliceReaderPrime (p : Nat.Primes) : Fact p.val.Prime := ⟨p.prop⟩
/-- Finite enumeration of the slice's ground field used in the coordinate reader construction. -/
noncomputable local instance sliceReaderFintype (p : Nat.Primes) (t d : ℕ) : Fintype (Ground p t d) := Fintype.ofFinite _
/-- Classical equality decision on ground-field elements used by the slice reader. -/
noncomputable local instance sliceReaderDecidable (p : Nat.Primes) (t d : ℕ) : DecidableEq (Ground p t d) := Classical.decEq _

variable {k : Type*} [Field k] {sched : BlockSchedule k} (B : sched.Templates)

set_option maxHeartbeats 1800000 in
set_option maxRecDepth 10000 in
set_option synthInstance.maxSize 12000 in
/-- The deterministic coordinate readers, their common advice and their
uniform bounds for one model. The field-coordinate map is the one used in
the terminal test of the nondeterministic evaluator. -/
theorem exists_sliceReaderAdvice (q c : ℕ) {sp ex : ℕ → ℕ} (signed : B.SignedCallFits q c (B.coordinateWidth q c) sp ex)
    (n : ℕ) (hn : 2 ≤ n) (p : Nat.Primes) (hp : q ≠ 0 → p.val = q) (hz : q = 0 → p.val ≤ 2^B.compressorPrimeBits c n)
    (M : Model p (B.compressorDegree n) (B.compressorEquations hn c)) :
    let w := B.coordinateWidth q c n
    let cost := B.coordinateBudget CompressorReader.Parts CompressorReader.Work CompressorReader.K q c n w (sp n) (ex n)
    ∃ H : B.SliceReaderAdvice M (CompressorReader.read true) (CompressorReader.read false),
      H.indexWidth = w ∧ H.degreePred+1 ≤ B.readerDegreeBudget q c n ∧ H.limbWidth ≤ B.readerLimbBudget q c n ∧
      H.extraSpace ≤ cost.space ∧ H.peak ≤ cost.space ∧ H.queryExponent ≤ Nat.clog 2 cost.time := by
  intro w cost
  let t := B.compressorLabelCount c n
  let e := SliceField.extensionDegree p.val (columnCountBound t (B.compressorDegree n))
  let v := B.readerLimbBudget q c n
  let plan := B.compressorReaderPlan q c n
  let data := M.queryData (B.compressorCoeff hn c)
  let d := planDepth plan
  let degree := B.readerDegreeBudget q c n
  let A := plan.live degree v w (sp n)
  let S := plan.armSpace degree v w (sp n)
  let T := plan.readTime degree v w (sp n) (ex n)
  have : NeZero e := ⟨Nat.succ_ne_zero _⟩
  obtain ⟨m, φ, _, irreducible, coord⟩ := exists_compatible_advice p.val (columnCountBound t (B.compressorDegree n))
  have : Fact (Irreducible (modulus m)) := ⟨irreducible⟩
  let : DecidableEq (AdjoinRoot (modulus m)) := Classical.decEq _
  obtain ⟨planFits, degreeFits, working⟩ := B.compressorReaderCovers q c hn p M hp hz
  have hdegree : e ≤ degree := degreeFits
  have hw : plan.wordWidth ≤ w := (planWidth_covers plan).2
  have fit : CanonicalFits data d w v e A S T := canonicalFits planFits le_rfl hdegree le_rfl (sp n) (ex n)
  obtain ⟨signedS, signedT⟩ := signed n hn p.val e v hdegree le_rfl
  have raw := B.compressorMatrixReader q c hn M φ hp hz hw hdegree le_rfl working (sp n) (ex n) signedS signedT
  let ready := B.compressorBaseReady hn M m φ w v
  let base := B.compressorBaseBank hn M m φ w v
  have isReady : ready base := B.compressorBaseBank_ready hn M m φ q w v hp hz hw
  let layout := JointScalar.Leaf.layout B.Entry B.EquationIndex B.equation c hn w p.val e v
  have signedBank : JointScalar.Leaf.bankSize layout w (t*w) ≤ sp n :=
    (le_max_right ..).trans ((Nat.le_add_right ..).trans signedS)
  have room (s : Stacks CompressorReader.K) (hs : ready s) (a : CompressorReader.K) : (s a).length ≤ A :=
    B.compressorBaseReady_length hn M m φ q w v (sp n) hdegree le_rfl signedBank s hs a
  let actual := preparedBudget CompressorReader.Parts CompressorReader.Work CompressorReader.K
    (SliceMinors.height data) (SliceMinors.width data) (NativeReader.order data) d w v e T A S T t
  have covered : actual.time ≤ cost.time ∧ actual.space ≤ cost.space :=
    B.coordinateBudget_covers CompressorReader.Parts CompressorReader.Work CompressorReader.K q c n w (sp n) (ex n)
      data planFits hdegree le_rfl
  let extra := SelectedAdvice.selectedExtra m data w v base
  have extras (a : CompressorReader.Ports) : (extra a).length ≤ cost.space := by
    have h := SelectedAdvice.extra_length (d := d) (S := S) m data base (room _ isReady) fit.rowFit fit.columnFit
      fit.wordLive fit.arityLive fit.scalarLive working a
    exact h.trans ((preparedBudget_advice CompressorReader.Parts CompressorReader.Work CompressorReader.K
      (SliceMinors.height data) (SliceMinors.width data) (NativeReader.order data) d w v e T A S T t).trans covered.2)
  let dim := M.dimensionWord fit.dimensionFit
  have run (op : QueryData.Operation t) :
      ReadsEntryWithin φ dim extra (CompressorReader.read (SelectedAdvice.mode op)) v (SelectedAdvice.label op)
        (2^(Nat.clog 2 cost.time)) cost.space (fun src dest ↦ data.matrixEntry op dest src) := by
    have h := CanonicalReader.readsEntryWithin φ data dim rfl op MacaulayRead.ordinaryReader raw room base isReady working fit
    exact ReadsEntryWithin.mono φ dim extra (covered.1.trans (Nat.le_pow_clog (by decide) _)) covered.2 h
  refine ⟨{
    degreePred := Nat.log p.val (2*columnCountBound t (B.compressorDegree n))
    coefficients := m
    fieldMap := φ
    primeCoordinate := coord
    indexWidth := w
    dimensionFits := fit.dimensionFit
    limbWidth := v
    widthFits := working
    extra := extra
    extraSpace := cost.space
    extraFits := extras
    peak := cost.space
    queryExponent := Nat.clog 2 cost.time
    frobeniusRead := run .frobenius
    labelRead := fun j ↦ run (.label j)
  }, rfl, hdegree, le_rfl, le_rfl, le_rfl, le_rfl⟩

end Compression.BlockSchedule.Templates

end

end VPVNP
end Computability
end OAI
