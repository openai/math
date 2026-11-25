import OAI.ThreeFlat.RAM.PhysicalExactRun
import OAI.Hierarchy.GridPinPublisherLayout
import OAI.Hierarchy.GridPinNativeScatter
import OAI.Hierarchy.GridPinNativePrefix
import OAI.Hierarchy.GridPinHeaderImage
import OAI.Hierarchy.GridPinPublishedBanks

namespace OAI
/-! # Native publication of the evaluator's literal and endpoint banks -/

namespace Hierarchy.GridPinPublisher
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open PhysicalProcedure FactorBucketRAM GridPinNativeLoops
open scoped Fin.CommRing
variable {w : ℕ}

variable (P : Plan)

/-- ABI of the two arrays supplied to the wired evaluator. -/
def Published {r k n q d : ℕ} (A : GridThrough.PinAssignment (Fin r) k n q d)
    (P : Plan) (out : Memory w) : Prop :=
  (∀ i<r*2,out (P.source.dest+i)=(GridOrderedPinOrigins.slot A i:Word w)) ∧
    ∀ ci : GridThrough.Cell k n×Fin (q*d),out (P.source.literal+(GridThrough.Ordered.dataCode ci).val)=
      ((A.literal ci).toNat:Word w)

def Outside (P : Plan) (rails a : ℕ) : Prop :=
  (a<P.source.rails ∨ P.source.rails+rails≤a) ∧
  (a<P.factor.ticks ∨ P.factor.ticks+P.ticks≤a) ∧
  (a<P.factor.bases ∨ P.factor.bases+P.factor.items≤a) ∧
  (a<P.bucket.blocks ∨ P.bucket.blocks+P.lanes≤a) ∧
  (a<P.source.literal ∨ P.source.literal+P.ticks*P.header.pins≤a) ∧
  (a<P.source.dest ∨ P.source.dest+P.endpoints≤a)

namespace Plan

def tickSeed (w : ℕ) := seedWords w P.ticks P.factor.ticks P.header.pins P.headerSize

def program (w : ℕ) : Procedure w :=
  (((((procedure seedOps (P.tickSeed w)).seq
    (procedure factorOps (factorWords w P.factors P.factor))).seq
    (procedure bucketOps (bucketWords w P.lanes P.bucket))).seq
    (GridPinHeaderNative.procedure w P.ticks P.header)).seq
    (procedure literalOps (literalWords w P.literals P.source))).seq
    (procedure endpointOps (endpointWords w P.endpoints P.source))

def seeded (m : Memory w) := iterRows seedStep (P.tickSeed w) m P.ticks
def factorized (m : Memory w) := iterRows factorStep (factorWords w P.factors P.factor) (P.seeded m) P.factors
def bucketed (m : Memory w) := iterRows bucketStep (bucketWords w P.lanes P.bucket) (P.factorized m) P.lanes
def initialized (m : Memory w) := fillSegment P.header.literalBase (P.ticks*P.header.pins)
    (fun a=>(GridPinHeaderNative.initialWord w P.header (fun j=>((P.bucketed m) j).val) a:Word w)) (P.bucketed m)
def scattered (m : Memory w) := iterRows literalStep (literalWords w P.literals P.source) (P.initialized m) P.literals
def output (m : Memory w) := iterRows endpointStep (endpointWords w P.endpoints P.source) (P.scattered m) P.endpoints

def budget (w : ℕ) :=
  (3+P.ticks*(1+seedOps.length)) + (3+P.factors*(1+factorOps.length)) +
  (3+P.lanes*(1+bucketOps.length)) +
  (4+(P.ticks*P.header.pins)*(2*(GridPinHeaderNative.headerExpr w P.header).work+4)) +
  (3+P.literals*(1+literalOps.length)) + (3+P.endpoints*(1+endpointOps.length))

/-- Each pass executes its real immutable word program, retaining the exact
intermediate memories for the port and source readback lemmas. -/
theorem execute (m : Memory w)
    (ticksFit : P.ticks<2^w) (factorsFit : P.factors<2^w) (lanesFit : P.lanes<2^w)
    (literalsFit : P.literals<2^w) (endsFit : P.endpoints<2^w) (pos : 0<w)
    (hp : 0<P.header.pins) (pf : P.header.pins<2^w)
    (outFit : P.header.literalBase+P.ticks*P.header.pins<2^w)
    (text : P.header.textBase+P.header.text<2^w)
    (ops : P.header.operandBase+P.header.operandBits<2^w)
    (sel : P.header.selectorBase+P.header.selector<2^w)
    (separate : ∀ z,GridPinHeaderNative.source P.header z → z<P.header.literalBase ∨
      P.header.literalBase+P.ticks*P.header.pins≤z) :
    (P.program w).Exec m (P.output m) (P.budget w) := by
  have S : (procedure seedOps (P.tickSeed w)).Exec (m) (P.seeded m) (3+P.ticks*(1+seedOps.length)) := Procedure.Spec.exec (loop_spec seedOps seedStep (fun _ _ _ _ _ _=> seed_trace ..)
    (P.tickSeed w) _ ticksFit rfl) m trivial
  have F : (procedure factorOps (factorWords w P.factors P.factor)).Exec (P.seeded m) (P.factorized m) (3+P.factors*(1+factorOps.length)) := Procedure.Spec.exec (loop_spec factorOps factorStep (fun _ _ _ _ _ _=>factor_trace ..)
    (factorWords w P.factors P.factor) _ factorsFit rfl) (P.seeded m) trivial
  have B : (procedure bucketOps (bucketWords w P.lanes P.bucket)).Exec (P.factorized m) (P.bucketed m) (3+P.lanes*(1+bucketOps.length)) := Procedure.Spec.exec (loop_spec bucketOps bucketStep (fun _ _ _ _ _ _=>bucket_trace ..)
    (bucketWords w P.lanes P.bucket) _ lanesFit rfl) (P.factorized m) trivial
  have H : (GridPinHeaderNative.procedure w P.ticks P.header).Exec (P.bucketed m) (P.initialized m)
      (4+(P.ticks*P.header.pins)*(2*(GridPinHeaderNative.headerExpr w P.header).work+4)) :=
    GridPinHeaderNative.procedure_spec w P.header P.ticks (P.bucketed m)
    outFit separate pos hp pf text ops sel
  have L : (procedure literalOps (literalWords w P.literals P.source)).Exec (P.initialized m) (P.scattered m) (3+P.literals*(1+literalOps.length)) := Procedure.Spec.exec (loop_spec literalOps literalStep (fun _ _ _ _ _ _=>literal_trace ..)
    (literalWords w P.literals P.source) _ literalsFit rfl) (P.initialized m) trivial
  have E : (procedure endpointOps (endpointWords w P.endpoints P.source)).Exec (P.scattered m) (P.output m) (3+P.endpoints*(1+endpointOps.length)) := Procedure.Spec.exec (loop_spec endpointOps endpointStep (fun _ _ _ _ _ _=>endpoint_trace ..)
    (endpointWords w P.endpoints P.source) _ endsFit rfl) (P.scattered m) trivial
  intro pcCount regCount pubCount machine pc reg pub exit installed data cfg mem first same
  exact Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then
    (Procedure.Exec.then S F) B) H) L) E machine pc reg pub exit installed data cfg mem first same

theorem budget_linear (P : Plan) (w : ℕ) :
    P.budget w ≤ (100+2*(GridPinHeaderNative.headerExpr w P.header).work)*
      (1+P.ticks+P.factors+P.lanes+P.ticks*P.header.pins+P.literals+P.endpoints) := by
  simp only [budget]
  have s : seedOps.length=9 := rfl
  have f : factorOps.length=34 := rfl
  have b : bucketOps.length=22 := rfl
  have l : literalOps.length=17 := rfl
  have e : endpointOps.length=20 := rfl
  rw [s,f,b,l,e]
  nlinarith only [Nat.zero_le (GridPinHeaderNative.headerExpr w P.header).work,
    Nat.zero_le ((GridPinHeaderNative.headerExpr w P.header).work * P.ticks),
    Nat.zero_le ((GridPinHeaderNative.headerExpr w P.header).work * P.factors),
    Nat.zero_le ((GridPinHeaderNative.headerExpr w P.header).work * P.lanes),
    Nat.zero_le ((GridPinHeaderNative.headerExpr w P.header).work * P.literals),
    Nat.zero_le ((GridPinHeaderNative.headerExpr w P.header).work * P.endpoints),
    Nat.zero_le P.ticks,Nat.zero_le P.factors,Nat.zero_le P.lanes,Nat.zero_le P.literals,
    Nat.zero_le P.endpoints,Nat.zero_le (P.ticks*P.header.pins)]

theorem budget_uniform (P : Plan) (w : ℕ) :
    P.budget w ≤ 852*(1+P.ticks+P.factors+P.lanes+P.ticks*P.header.pins+P.literals+P.endpoints) := by
  simpa only [GridPinHeaderNative.header_work] using budget_linear P w

/-- The ordinary exterior rail order is represented by a genuinely written
identity table. Relabelled callers may instead supply their original rank array. -/
def canonicalProgram (P : Plan) (w rails : ℕ) :=
  (procedure seedOps (seedWords w rails P.source.rails 1 0)).seq (P.program w)

/-- For fixed grid dimension, all class-major work is polynomial in the
word-age parameter times the number of genuine records and physical tape bits. -/
theorem canonical_cost (scale k n q pins nparams selector text compact rails bits
    items stages fullLanes span : ℕ) :
    let P:=canonical scale k n q pins nparams selector text compact rails bits items stages fullLanes span
    let K:=(20*(scale+1)+2)^(k+2)
    3+rails*(1+seedOps.length)+P.budget (64*scale) ≤
      900*K*(1+P.ticks+items+P.lanes+P.ticks*P.header.pins+P.literals+P.endpoints) := by
  intro P K
  have cost:=budget_uniform P (64*scale)
  let B:=1+P.ticks+P.lanes+P.ticks*P.header.pins+P.literals+P.endpoints
  have hp : 0<K := by dsimp [K];positivity
  have scaled : B≤K*B := Nat.le_mul_of_pos_left _ hp
  have factors : P.factors=K*items := rfl
  have ends : P.endpoints=rails*2 := rfl
  have work : seedOps.length=9 := rfl
  rw [work]
  rw [factors] at cost
  have small : rails≤B := by dsimp [B];rw [ends];omega
  have one : 1≤B := by dsimp [B];omega
  dsimp only [B] at scaled small one
  nlinarith only [scaled,small,one,cost,
    Nat.zero_le (K*items),Nat.zero_le P.ticks,Nat.zero_le P.lanes,
    Nat.zero_le (P.ticks*P.header.pins),Nat.zero_le P.literals,Nat.zero_le P.endpoints]

end Plan

export Plan (tickSeed program seeded factorized bucketed initialized scattered output budget execute budget_linear budget_uniform canonicalProgram canonical_cost)

end Hierarchy.GridPinPublisher

end OAI
