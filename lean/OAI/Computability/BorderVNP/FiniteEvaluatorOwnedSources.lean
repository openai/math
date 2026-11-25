import OAI.Computability.BorderVNP.FiniteEvaluatorOwnedFactors
import OAI.Computability.BorderVNP.FiniteEvaluatorTaskOutput
import OAI.Computability.BorderVNP.FiniteEvaluatorMergedLogicalRows
import OAI.Computability.BorderVNP.FiniteEvaluatorSignedPublicEntries

/-! # Source words for the returned owned-cell evaluator

The opening uses the actual task, report, and supplemental regions. The
native row sources below identify the cell packet, the supplied end bits,
and the scalar stream that is shared by the validator and scalar routines.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.OwnedContinuation

open Crossing Packing Packing.Inherited FiniteDiagonal BorderVNP.Cube Cube.Physical
open VPVNP.BurstRAM RoutingISA CellPacket.Supplement
open scoped Classical BigOperators

variable {w n b h K s : ℕ} {F : Type*} [Field F] [Fintype F]

/-- The authenticated opening, report, and task tables of one physical team. -/
structure Opening (pub : Arg → Word w) (mem : Memory w) (Y : CubePacket.Inputs n b h K s F) where
  /-- The physical pin tests, cell copies and bundle-control writer. -/
  stage : OpenSuffix.Inputs
  /-- Addresses of the received packet, cell and selector banks. -/
  arena : CubeArena.Layout
  /-- The task allocation following the fragment and fixed-field storage. -/
  reserved : DiagonalTallyAllocation.BeforeTasks
  /-- Exclusive end of the constant field table. -/
  deckEnd : ℕ
  /-- Pointers to the report rows and subtotal counters. -/
  report : Reports.Layout
  /-- Owned report rows in native visit order. -/
  rows : List Reports.Row
  /-- Shared call table and local task source pointers. -/
  tasks : TypedTaskBuilder.Layout
  /-- The supplemental row metadata for each owned ordinal. -/
  supp : ℕ → Batch.Cell
  /-- Number of supplemental cells physically visited. -/
  count : ℕ
  /-- Base of the four-word supplemental controls. -/
  controls : ℕ
  ready : OpenSuffix.Ready stage (pub 0).val (readings mem) w
  openPlace : OpenSuffix.Placement stage arena reserved (pub 0).val (readings mem)
  writePlace : TaskReadback.Placement pub Y report rows tasks supp count arena.header.packetBase arena.cellBank arena.stop deckEnd
  gap : deckEnd ≤ reserved.start
  source : ∀ out : Memory w, readings out=stage.image (pub 0).val (readings mem) →
    TaskReadback.Setup pub out report rows tasks supp count controls
  scalarCount : report.scalars=Fintype.card F

private theorem written_congr (middle : Memory w) (a b : ℕ → Batch.Cell) {count : ℕ}
    (same : ∀ i < count, a i=b i) : Batch.written middle a count=Batch.written middle b count := by
  induction count with
  | zero => rfl
  | succ i ih => rw [Batch.written,Batch.written,same i i.lt_succ_self,ih (fun j hj => same j (hj.trans i.lt_succ_self))]

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
  {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
  (V : FieldRawLayout L S) (R : ℕ) (bank : Ports bits) (z : V.Public R) (u : Fin (R+1))
  {pub : Arg → Word w} {mem : Memory w} {Y : CubePacket.Inputs n b h K s F} (A : Opening pub mem Y)
  (order : Fin A.rows.length ≃ {c : L.Cell // V.cellOwner R z c=u})
  {Orig : Type} (codec : Cells.Codec) (raw : ℕ → ℕ) (c : TaskReadback.Matrices F A.report.digits A.rows)
  (X : Cells.Inputs F) (owned : ℕ → Batch.Owned Orig)

/-- The genuine geometry and delivered logical bits at the image before the
supplemental splice. The field scanner's physical reports are read from the
same real task bank. -/
structure PacketSources (out : Memory w) (length : ℕ) : Prop where
  prepared : Cells.Prepared X pub out length codec
  cube : CubePacket.Sources Y X.layout
  /-- Owned report rows in native visit order. -/
  rows : Merged.RowInputs V R bank z u A.report.digits A.rows order X c
  layout : X.layout=A.tasks
  publicMem : X.publicMem=raw
  /-- Number of supplemental cells physically visited. -/
  count : A.count=X.count
  same : ∀ i < A.count, A.supp i=(owned i).cell
  apart : Reports.MetaOutside X.layout X.count owned

/-- Numerical field weight of these physically delivered rows, from their
actual decoded directories, their endpoint bits, and their scalar stream. -/
theorem PacketSources.host_rows {out middle : Memory w} {length : ℕ}
    (H : PacketSources V R bank z u A order codec raw c X owned out length)
    (published : readings middle=A.tasks.published raw) (splice : out=Batch.written middle A.supp A.count) :
    X.hostFactor pub out=∏ i, Merged.rowScore V R bank z u A.report.digits A.rows order i (c i) := by
  have post := splice.trans (written_congr middle _ _ H.same)
  rw [H.count] at post
  refine (congrArg (X.hostFactor pub) post).trans ?_
  exact Merged.hostFactor_rowScore_for V R bank z u A.report.digits A.rows order X c H.rows codec pub middle owned
    (by rw [H.layout,H.publicMem]; exact published) H.apart (post ▸ H.prepared)

end FiniteEvaluator.OwnedContinuation

end BorderVNP
end Computability
end OAI
