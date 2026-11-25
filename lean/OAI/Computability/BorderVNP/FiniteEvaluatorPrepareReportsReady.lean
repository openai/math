import OAI.Computability.BorderVNP.FiniteEvaluatorCells
import OAI.Computability.BorderVNP.FiniteEvaluatorPrepareReportsMemory
import OAI.Computability.BorderVNP.CellPacketSupplementalPrepare
import OAI.Computability.BorderVNP.RoutingISATypedTaskPackets

/-! # Constructing the finite-cell evaluator input after the real supplemental splice

The physical seven-word task rows and four-word controls select the owned
packets. The splice rewrites their descriptor intervals. Its counter inputs
are zero on finite-only cells. The proof obtains source storage and ownership
from these physical rows and uses the same chronological supplied scalar bits
for the validator and scalar stages.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.Reports

open VPVNP.BurstRAM RoutingISA RoutingISA.CompactMachine RoutingISA.TypedTaskBuilder
open RoutingISA.CellPacket RoutingISA.CellPacket.Supplement TeamRAM
open scoped Classical

variable {Site : Type} {F : Type*} [Fintype F]

/-- The concrete evaluator inputs obtained from the owned packet table and
the actual scalar report matrices. A global cell selects its packet by its
true local rank in the ownership scan. -/
noncomputable def inputs (l : TypedTaskBuilder.Layout) (raw : ℕ → ℕ) (owned : ℕ → Supplement.Batch.Owned Site)
    (supplied : ℕ → List Bool) (digits : ℕ → ℕ) (claims : ∀ i, FiniteScalarRounds.Index F → Fin (digits i) → Bool) :
    Cells.Inputs F where
  layout := l
  publicMem := raw
  rows i := ⟨(owned i).typed,globalCell l raw i,supplied i,FiniteScalarRounds.stream F (claims i)⟩
  cells i := TypedBatch.cellInput (owned (l.before raw i)).placed
  digits := digits
  claim := claims

/-- The sparse splice only touches its own merged-count and descriptor words.
These public frame, control, tail and call addresses must survive it. -/
def MetaOutside (l : TypedTaskBuilder.Layout) (count : ℕ) (owned : ℕ → Supplement.Batch.Owned Site) : Prop :=
  ∀ j < count,
    (∀ k < 112, (owned j).cell.Outside (l.frame+k)) ∧
    (∀ k < 8, (owned j).cell.Outside (l.control+k)) ∧
    (∀ k < l.cells, (owned j).cell.Outside (l.tails+k) ∧ (owned j).cell.Outside (l.call k))

/-- All conditions of the actual two-call finite cell program after the
supplemental initializer. The true task and source storage conditions follow
from its proved physical readback, and each globally owned call is matched to
its task through the ownership scan. -/
theorem prepared_after_splice {w n controls : ℕ} (pub : Arg → Word w) (m : Memory w)
    (l : TypedTaskBuilder.Layout) (raw : ℕ → ℕ) (owned : ℕ → Supplement.Batch.Owned Site)
    (supplied : ℕ → List Bool) (digits : ℕ → ℕ) (claims : ∀ i, FiniteScalarRounds.Index F → Fin (digits i) → Bool)
    (ptr : (pub 0).val=l.frame) (fields : l.Fields (readings m))
    (width : (m (l.frame+30)).val=w) (num : (m (l.frame+90)).val=l.before raw l.cells)
    (room : l.Room raw w) (arena : l.Arenas raw w (fun i => (owned i).typed))
    (control : l.SourceRange l.control 8) (tails : l.SourceRange l.tails l.cells)
    (initial : ∀ i < l.before raw l.cells, Supplement.Batch.Initial (owned i) l.tasks controls i m)
    (alloc : Supplement.Batch.Allocation l.frame l.tasks controls (l.before raw l.cells) w owned)
    (apart : MetaOutside l (l.before raw l.cells) owned)
    (owner : ∀ c < l.cells, (m (l.call c)).val=l.owner raw c)
    (call : ∀ i < l.before raw l.cells, (owned i).callRow=l.call (globalCell l raw i))
    (zero : ∀ i < l.before raw l.cells, (owned i).extra=[])
    (bank : ∀ i < l.before raw l.cells, (owned i).placed.external=supplied i++FiniteScalarRounds.stream F (claims i))
    (tail : ∀ i < l.before raw l.cells, (m (l.tails+globalCell l raw i)).val=(FiniteScalarRounds.stream F (claims i)).length)
    (scalar : ∀ i < l.before raw l.cells, 2*digits i*Fintype.card F < nativeClock n)
    (cap : ∀ i < l.before raw l.cells, ((owned i).typed.cell.burst w).length ≤ TeamScales.width n (1/2))
    (legal : ∀ i < l.before raw l.cells, (owned i).placed.directory.ProfileWidths ∧
      TypedBatch.cellClock w (TypedBatch.cellInput (owned i).placed) ≤ n^25) :
    Cells.Prepared (inputs l raw owned supplied digits claims) pub
      (Supplement.Batch.written m (fun i => (owned i).cell) (l.before raw l.cells)) n := by
  let count := l.before raw l.cells
  let cs := fun i => (owned i).cell
  let mt := Supplement.Batch.written m cs count
  have keep (a : ℕ) (h : ∀ j < count, (owned j).cell.Outside a) : (mt a).val=(m a).val :=
    congrArg Fin.val (Supplement.Batch.preserve m cs (i:=0) (Nat.zero_le _) a (fun j _ hj => h j hj))
  have outer (j : ℕ) (h : j < 112) := keep (l.frame+j) (fun i hi => (apart i hi).1 j h)
  have inner (j : ℕ) (h : j < 8) := keep (l.control+j) (fun i hi => (apart i hi).2.1 j h)
  have frame : l.Fields (readings mt) := by
    constructor
    · obtain ⟨a,b,c,d,e,f,g,h⟩ := fields.outer
      exact ⟨(outer 0 (by decide)).trans a,(outer 7 (by decide)).trans b,(outer 14 (by decide)).trans c,
        (outer 15 (by decide)).trans d,(outer 72 (by decide)).trans e,(outer 87 (by decide)).trans f,
        (outer 89 (by decide)).trans g,(outer 92 (by decide)).trans h⟩
    · obtain ⟨a,b,c,d,e,f,g,h⟩ := fields.header
      exact ⟨(inner 0 (by decide)).trans a,(inner 1 (by decide)).trans b,(inner 2 (by decide)).trans c,
        (inner 3 (by decide)).trans d,(inner 4 (by decide)).trans e,(inner 5 (by decide)).trans f,
        (inner 6 (by decide)).trans g,(inner 7 (by decide)).trans h⟩
  have dispatch : CellDispatch.Frame.ofMemory pub mt=⟨l.team,l.calls,l.cells⟩ := by
    unfold CellDispatch.Frame.ofMemory
    rw [ptr]
    congr 1
    · exact frame.outer.1
    · exact frame.outer.2.2.1
    · exact frame.outer.2.2.2.1
  have cellAddr (i : ℕ) : (CellDispatch.Frame.ofMemory pub mt).address i=l.call i := by
    rw [dispatch]
    simp [CellDispatch.Frame.address,TypedTaskBuilder.Layout.call,Nat.mul_comm,Nat.add_comm]
  have owns (i : ℕ) (hi : i < l.cells) (hm : (mt (l.call i)).val=l.team) : l.owner raw i=l.team :=
    (owner i hi).symm.trans ((keep (l.call i) (fun j hj => ((apart j hj).2.2 i hi).2)).symm.trans hm)
  change Cells.Prepared (inputs l raw owned supplied digits claims) pub mt n
  refine ⟨ptr,frame,(outer 30 (by decide)).trans width,(outer 90 (by decide)).trans num,
    room,arena,control,tails,fun _ _ => rfl,?_,?_,bank,?_,fun _ _ => rfl,scalar,?_,?_⟩
  · intro i hi
    exact Supplement.Batch.task_row m cs (owned i).typed (initial i hi).taskRow (fun k hk j hj => alloc.taskRows i hi k hk j hj)
  · intro i hi
    have init := initial i hi
    apply Supplement.Batch.typed_stored m cs hi (owned i).placed (owned i).geometry (owned i).callRow
      (owned i).extra rfl init.report init.prefixEnd init.stored init.mergeRoom init.original init.separateCount
    · exact alloc.originals i hi
    · exact alloc.patched i hi
  · intro i hi
    have bound := (global_spec l raw hi).1
    exact (keep _ (fun j hj => ((apart j hj).2.2 _ bound).1)).trans (tail i hi)
  · refine ⟨?_,cap⟩
    intro i hi hm
    rw [cellAddr] at hm ⊢
    rw [dispatch] at hi hm
    have own := owns i hi hm
    let rank := l.before raw i
    have rk : rank < count := l.before_strict raw hi own
    refine ⟨rank,rk,(call rank rk).trans (congrArg l.call (global_at l raw hi own)),?_⟩
    change (Supplement.task (owned rank).layout (owned rank).placed (owned rank).geometry (owned rank).extra).payload =
      CellSparse.Packet.input (owned rank).placed.directory (owned rank).placed.privateWires (owned rank).placed.external
    rw [Supplement.payload_eq,zero rank rk,List.append_nil]
    rfl
  · intro i hi hm
    rw [cellAddr] at hm
    rw [dispatch] at hi hm
    exact legal (l.before raw i) (l.before_strict raw hi (owns i hi hm))

end FiniteEvaluator.Reports

end BorderVNP
end Computability
end OAI
