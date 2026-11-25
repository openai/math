import OAI.Computability.BorderVNP.FiniteEvaluatorMergedLogicalRows
import OAI.Computability.BorderVNP.FiniteEvaluatorSparseInput
import OAI.Computability.BorderVNP.DiagonalExternalFragmentValues

/-! # Logical merged cell scores on the real compressed argument memory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.Merged

open Crossing Packing Packing.Inherited FiniteDiagonal FiniteDiagonal.CellTrace BorderVNP.Cube Cube.Physical
open VPVNP.BurstRAM RoutingISA RoutingISA.CellPacket.Supplement
open scoped Classical BigOperators

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
  {F : Type*} [Field F] [Fintype F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
  (V : FieldRawLayout L S) (R : ℕ) (bank : Ports bits) (z : V.Public R)
  (u : Fin (R+1)) (digits : ℕ) (rows : List Reports.Row)
  (order : Fin rows.length ≃ {c : L.Cell // V.cellOwner R z c=u})
  {Orig : Type} (l : TypedTaskBuilder.Layout) (raw : ℕ → ℕ) (src : ℕ → Batch.Owned Orig)
  (sl : SparseExterior.Layout) (os : ℕ → SparseExterior.Owned) (fields : ℕ → SparseExterior.Field)
  (claim : ℕ → Fin (Fintype.card F) → Fin digits → Bool)
local notation "site₀" i => rowSite V R z u rows order i
local notation "input₀" i => rowInput V R bank z u rows order i
local notation3 "X₀" => Reports.sparseInputs l raw (fun i => (os i).supplemental sl (src i)) fields (fun _ => digits) claim
local notation "global" i => TypedTaskBuilder.globalCell l raw (Fin.val i)

/-- The sparse argument writer changes the two external operand fields only.
The original geometry and private extent remain the validator's, while the
new compressed field gives the logical delivered endpoints and raw suffix. -/
theorem sparse_rowInputs (count : l.before raw l.cells=rows.length)
    (geometry : ∀ i : Fin rows.length, (src i.val).placed.directory=Placement.packet N L.cell (order i).val
      V.siteID S.edgeID S.portID S.site (Reports.fields (site₀ i).size (Fintype.card F) digits))
    (work : ∀ i : Fin rows.length, (src i.val).placed.privateWires=(site₀ i).work)
    (delivered : ∀ i : Fin rows.length, let e := fields (global i)
      SparseExterior.expand e.width [] 0 e.spans=List.ofFn (input₀ i))
    (tail : ∀ i : Fin rows.length, (fields (global i)).tail=FiniteScalarRounds.stream F (claim i.val)) :
    RowInputs V R bank z u digits rows order X₀ (fun i => claim i.val) := by
  have rank (i : Fin rows.length) : l.before raw (global i)=i.val :=
    (TypedTaskBuilder.global_spec l raw (i.isLt.trans_eq count.symm)).2.2
  refine ⟨count,?_,?_,?_,fun _ => rfl,fun _ _ _ => rfl⟩
  · intro i
    change (src (l.before raw (global i))).placed.directory=_
    rw [rank]
    exact geometry i
  · intro i
    change (src (l.before raw (global i))).placed.privateWires=_
    rw [rank]
    exact work i
  · intro i
    let e := fields (global i)
    change SparseExterior.expand e.width e.tail 0 e.spans=_
    rw [SparseExterior.expand_append_tail,delivered i,tail i]

/-- The native signed and scalar host factors on the actual rewritten sparse
memory. The stored owner bytes survive both the descriptor splice and the
subsequent compression pass. -/
theorem sparse_hostFactor {w n : ℕ} (pub : Arg → Word w) (m mt : Memory w)
    (published : readings m=l.published raw) (splice : Reports.MetaOutside l (l.before raw l.cells) src)
    (post : readings mt=SparseExterior.written sl os
      (readings (Batch.written m (fun j => (src j).cell) (l.before raw l.cells))) sl.count)
    (safe : Reports.SparseMetaOutside l sl os)
    (ready : Cells.Prepared X₀ pub mt n (.sparse fields))
    (facts : RowInputs V R bank z u digits rows order X₀ (fun i => claim i.val)) :
    (X₀).hostFactor pub mt=∏ i : Fin rows.length, rowScore V R bank z u digits rows order i (claim i.val) := by
  apply hostFactor_rowScore_memory V R bank z u digits rows order X₀ (fun i => claim i.val) facts pub mt
  · unfold CellDispatch.Frame.ofMemory
    rw [ready.pointer]
    congr 1
    · exact ready.fields.outer.1
    · exact ready.fields.outer.2.2.1
    · exact ready.fields.outer.2.2.2.1
  · intro c hc
    let patched := Batch.written m (fun j => (src j).cell) (l.before raw l.cells)
    let a := l.call c
    have preserved := SparseExterior.written_preserve sl os (readings patched) (i:=0) (Nat.zero_le sl.count)
      a (fun j _ hj => ((safe j hj).2.2 c hc).2)
    have spliceKept := Batch.preserve m (fun j => (src j).cell) (i:=0) (Nat.zero_le (l.before raw l.cells))
      a (fun j _ hj => ((splice j hj).2.2 c hc).2)
    change readings mt a=l.owner raw c
    exact (congrFun post a).trans (preserved.trans ((congrArg Fin.val spliceKept).trans
      ((congrFun published a).trans (l.published_owner raw ready.room hc))))

end FiniteEvaluator.Merged

end BorderVNP
end Computability
end OAI
