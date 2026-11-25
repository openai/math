import OAI.Computability.BorderVNP.FiniteEvaluatorSparseTaskMatrices
import OAI.Computability.BorderVNP.FiniteEvaluatorPreparedTeam
import OAI.Computability.BorderVNP.FiniteEvaluatorMergedSparseScore

/-! # Physical operands after every real sparse field-report preparation

The genuine producer, bucket, patch and compression images determine a
word RAM at each field report. A proof on that computed image supplies
all rows and cube operands for the team, uniformly across returning paths.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.SparseTasks

open Crossing Packing FiniteDiagonal VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator DiagonalResidueRAM
open scoped BigOperators Classical

variable {w : ℕ} {pub : Arg → Word w} {m : Memory w}

/-- Word RAM of the computed five-stage result at the chosen report bits. -/
noncomputable def Inputs.imageMemory (a : Inputs pub m) : Memory w := fun i => word w (a.image i)

/-- Each actual final memory equals this word RAM at every address. -/
theorem Inputs.eq_imageMemory (a : Inputs pub m) (out : Memory w) (same : readings out=a.image) :
    out=a.imageMemory := by
  funext i
  apply Fin.ext
  change (out i).val=(word w (a.image i)).val
  have atI := congrFun same i
  change (out i).val=a.image i at atI
  rw [←atI,word_val _ _ (out i).isLt]

set_option synthInstance.maxSize 4096
set_option maxRecDepth 6000
set_option maxHeartbeats 1500000

variable {D n b h K t : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
  {F : Type*} [Field F] [Fintype F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
  (V : FieldRawLayout L S) (R : ℕ) (bank : Ports bits) (z : V.Public R) (u : Fin (R+1))
  {l : Reports.Layout} {rows : List Reports.Row} (order : Fin rows.length ≃ {c : L.Cell // V.cellOwner R z c=u})
  (start : Reports.Start pub m l rows) (mac : TeamOpcode.Macros w 8) (s : Bank w) (fields : l.scalars=Fintype.card F)
  (a : ∀ c : TaskReadback.Matrices F l.digits rows, Inputs pub ((Reports.Start.matrixEquiv start mac s F fields) c).val.2.2)
  (ready : ∀ c, (a c).Ready) (Y : CubePacket.Inputs n b h K t F)
  (length previous ticks : ℕ)

local notation "Values" => TaskReadback.Matrices F l.digits rows

include ready in
/-- Native reports and all physical private-call operands, from numerical
source conditions on the actual computed compression image. Each report can
have its own sparse description for the same physical driver. -/
theorem preparedReports
    (operands : ∀ c : Values, let final := (a c).imageMemory
      ∃ (X : Cells.Inputs F) (sparse : ℕ → SparseExterior.Field),
        Cells.Prepared X pub final length (.sparse sparse) ∧ CubePacket.Prepared Y pub final ∧ CubePacket.Sources Y X.layout ∧
        Merged.RowInputs V R bank z u l.digits rows order X c ∧
        (∀ i < X.layout.cells, (final (X.layout.call i)).val=X.layout.owner X.publicMem i) ∧
        previous+(Reports.setup.slots+Reports.ticks rows+(a c).cost)+X.validatorCost pub final+X.scalarCost+Y.cost ≤ ticks) :
    ∃ E : Values ≃ Returns prepareSparseTasks pub mac s m, ∀ c, let out := E c
      (∀ i : Fin rows.length, ((Reports.rebit rows (out.val.1.flatMap TeamRAM.Event.choices))[i.val]'(by simp)).bits=
        FiniteScalarRounds.stream F (c i)) ∧
      ∃ (X : Cells.Inputs F) (sparse : ℕ → SparseExterior.Field),
        Cells.Prepared X pub out.val.2.2 length (.sparse sparse) ∧ CubePacket.Prepared Y pub out.val.2.2 ∧
        CubePacket.Sources Y X.layout ∧ Merged.RowInputs V R bank z u l.digits rows order X c ∧
        CellDispatch.Frame.ofMemory pub out.val.2.2=⟨X.layout.team,X.layout.calls,X.layout.cells⟩ ∧
        (∀ i < X.layout.cells, (out.val.2.2 (X.layout.call i)).val=X.layout.owner X.publicMem i) ∧
        previous+traceCost out.val.1+X.validatorCost pub out.val.2.2+X.scalarCost+Y.cost ≤ ticks := by
  let E := matrixReturns start mac s F fields a ready
  refine ⟨E,fun c => ⟨matrixReturns_bits start mac s F fields a ready c,?_⟩⟩
  obtain ⟨X,desc,ok,cube,sites,host,owners,time⟩ := operands c
  obtain ⟨_,_,_,cost,_,image⟩ := matrixReturns_spec start mac s F fields a ready c
  change traceCost (E c).val.1 ≤ Reports.setup.slots+Reports.ticks rows+(a c).cost at cost
  have memEq : (E c).val.2.2=(a c).imageMemory := (a c).eq_imageMemory _ image
  rw [memEq]
  refine ⟨X,desc,ok,cube,sites,host,?_,owners,by omega⟩
  unfold CellDispatch.Frame.ofMemory
  rw [ok.pointer]
  congr 1
  · exact ok.fields.outer.1
  · exact ok.fields.outer.2.2.1
  · exact ok.fields.outer.2.2.2.1

end FiniteEvaluator.SparseTasks

end BorderVNP
end Computability
end OAI
