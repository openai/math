import OAI.Computability.BorderVNP.FiniteEvaluatorReportMatrices
import OAI.Computability.BorderVNP.FiniteEvaluatorSparseTaskReturns

/-! # The genuine report choices of the complete sparse preparation

The scalar-report producer is followed by the actual fragment writer, stable
bucket, typed table, supplemental splice and sparse exterior emitter. Every
fixed legal report matrix determines one full native return. Every native
return recovers its matrix and the final compressed memory of those stages.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.SparseTasks

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator DiagonalResidueRAM
open scoped Classical

variable {w : ℕ} {pub : Arg → Word w} {m : Memory w}
  {l : Reports.Layout} {rows : List Reports.Row}
  (start : Reports.Start pub m l rows) (mac : TeamOpcode.Macros w 8) (s : Bank w)
  (F : Type*) [Fintype F] (fields : l.scalars=Fintype.card F)

local notation "Values" => TaskReadback.Matrices F l.digits rows
local notation "first" => Reports.Start.matrixEquiv start mac s F fields
local notation "before" => SignedPrep.beforeTyped
local notation "join" => seqReturnEquiv prepareReports before pub mac s m

variable (X : ∀ c : TaskReadback.Matrices F l.digits rows,
  Inputs pub ((Reports.Start.matrixEquiv start mac s F fields) c).val.2.2)
  (ready : ∀ c, (X c).Ready)

include X ready in
/-- The actual unique five-stage suffix from the report producer's physical
bank and memory. -/
noncomputable def suffixReturn (c : Values) :
    Returns before pub mac ((first) c).val.2.1 ((first) c).val.2.2 :=
  (return_unique (X c) (ready c) mac ((first) c).val.2.1).exists.choose

include X ready in
/-- Genuine choice matrices are in bijection with all native histories of
the real six-stage field task preparation. -/
noncomputable def matrixReturns : Values ≃ Returns prepareSparseTasks pub mac s m := by
  let forward := fun c : Values => (join) ⟨(first) c,suffixReturn start mac s F fields X ready c⟩
  refine Equiv.ofBijective forward ⟨?_,?_⟩
  · intro c d same
    exact (first).injective (congrArg Sigma.fst ((join).injective same))
  · intro full
    obtain ⟨⟨head,tail⟩,back⟩ := (join).surjective full
    obtain ⟨c,rfl⟩ := (first).surjective head
    exact ⟨c,(congrArg (fun v => (join) ⟨(first) c,v⟩) (return_eq _ tail)).trans back⟩

/-- The entire chronology, exact compressed final image, real middle report
image, signed output, and native charge all belong to this same run. -/
theorem matrixReturns_spec (c : Values) :
    let out := matrixReturns start mac s F fields X ready c
    let head := (first) c
    let tail := suffixReturn start mac s F fields X ready c
    let bs := (TaskReadback.matrixEquiv F l.digits rows (start.bit_length F fields) c).val
    out.val.1=head.val.1++tail.val.1 ∧ out.val.2=tail.val.2 ∧
    TraceOK out.val.1 bs out.val.1.length ∧
    traceCost out.val.1 ≤ Reports.setup.slots+Reports.ticks rows+(X c).cost ∧
    readings head.val.2.2=Reports.image l (Reports.rebit rows bs) (readings m) ∧
    readings out.val.2.2=(X c).image := by
  let head := (first) c
  let tail := suffixReturn start mac s F fields X ready c
  obtain ⟨earlier,upper,report⟩ := start.matrixEquiv_spec mac s F fields c
  obtain ⟨suffix,lower,done⟩ := return_facts (X c) (ready c) tail
  refine ⟨rfl,rfl,?_,?_,report,done⟩
  · change TraceOK (head.val.1++tail.val.1) _ (head.val.1++tail.val.1).length
    simpa only [List.append_nil,List.length_append] using earlier.append suffix
  · change traceCost (head.val.1++tail.val.1) ≤ _
    rw [Transmission.cost_append]
    exact Nat.add_le_add upper lower

/-- At every actual six-stage endpoint the recovered matrix has exactly the
bit-major report written by the guesser at each real owned row. -/
theorem matrixReturns_bits (c : Values) (i : Fin rows.length) :
    let out := matrixReturns start mac s F fields X ready c
    ((Reports.rebit rows (out.val.1.flatMap TeamRAM.Event.choices))[i.val]'(by simp)).bits=FiniteScalarRounds.stream F (c i) := by
  intro out
  let get (bs : List Bool) := ((Reports.rebit rows bs)[i.val]'(by simp)).bits
  refine (congrArg get (matrixReturns_spec start mac s F fields X ready c).2.2.1.2.1).trans ?_
  exact TaskReadback.matrixEquiv_read F l.digits rows (start.bit_length F fields) c i

end FiniteEvaluator.SparseTasks

end BorderVNP
end Computability
end OAI
