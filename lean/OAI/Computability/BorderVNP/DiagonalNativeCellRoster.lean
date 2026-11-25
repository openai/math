import OAI.Computability.BorderVNP.DiagonalNativeTypedRows
import OAI.Computability.BorderVNP.DiagonalNativeSparseProtection
import OAI.Computability.BorderVNP.DiagonalTallyAllocatedTaskSource
import OAI.Computability.BorderVNP.CellSparseExteriorBatchRun

/-! # Physical ownership of the cell dispatch rows through private packet preparation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellDispatch

open VPVNP.BurstRAM Evaluator TypedTaskBuilder CellPacket.Supplement.Batch

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- The team and row count come from the live frame. Each first word of a
three-word call row holds the original placement's owner at that global ordinal. -/
structure OwnerTable (pub : Arg → Word w) (m : Memory w) (f : Frame) (owner : ℕ → ℕ) : Prop where
  /-- All three scalar fields of the native directory. -/
  frame : Frame.ofMemory pub m = f
  /-- Its physically stored owner column. -/
  atRow : ∀ i < f.count, readings m (f.address i) = owner i

variable {m mt : Memory w} {f : Frame} {owner : ℕ → ℕ}

/-- A writer preserving the three scalars and first word of each call row
preserves the entire owner table. -/
theorem OwnerTable.kept (old : OwnerTable pub m f owner)
    (fields : ∀ k ∈ [0,14,15], mt ((pub 0).val+k)=m ((pub 0).val+k))
    (keep : ∀ i < f.count, mt (f.address i)=m (f.address i)) : OwnerTable pub mt f owner := by
  constructor
  · rw [←old.frame]
    simp only [Frame.ofMemory,show mt (pub 0).val=m (pub 0).val from fields 0 (by decide),
      fields 14 (by decide),fields 15 (by decide)]
  · intro i hi
    change (mt (f.address i)).val=_
    rw [keep i hi]; exact old.atRow i hi

/-- The native seven-word task builder emits the true owner column, including
every row assigned to a different team and each cell with no private boxes. -/
theorem ownerTable_published (l : TypedTaskBuilder.Layout) (src : ℕ → ℕ)
    (fp : (pub 0).val=l.frame) (fields : l.Fields src) (room : l.Room src w)
    (image : readings m=l.published src) : OwnerTable pub m ⟨l.team,l.calls,l.cells⟩ (l.owner src) := by
  refine ⟨dispatch_frame l src pub m fp fields room image,?_⟩
  intro i hi
  have addr : (Frame.mk l.team l.calls l.cells).address i=l.call i := by
    simp [Frame.address,TypedTaskBuilder.Layout.call,Nat.add_comm,Nat.mul_comm]
  rw [addr,image,l.published_owner src room hi]

/-- Patching the four descriptor triples and merged count of each owned cell
retains the complete global dispatch directory. The native geometry's sorted
markers and the reserved merged-count interval give both write footprints. -/
theorem ownerTable_supplemented {Site : Type} (rows : CellControlRows.Layout) (src : ℕ → ℕ)
    (placed : ℕ → CellPacket.Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List CellSparse.Record)
    (fp : (pub 0).val=rows.frame) (fields : rows.toLayout.Fields src) (room : rows.toLayout.Room src w)
    (image : readings m=rows.toLayout.published src)
    (span : ∀ c < rows.cells, src (rows.sorted+rows.padded+(rows.stops+c))-src (rows.sorted+rows.padded+c)-1 =
      3*((placed c).parts.length+3))
    (low : rows.frame+16 ≤ rows.sorted ∧ rows.frame+16 ≤ rows.merged)
    (high : rows.sorted+rows.padded ≤ rows.calls ∧ rows.merged+rows.cells ≤ rows.calls) :
    let owned := produced rows src placed geom extra
    let count := rows.before src rows.cells
    OwnerTable pub (written m (fun i => (owned i).cell) count)
      ⟨rows.team,rows.calls,rows.cells⟩ (rows.owner src) := by
  intro owned count
  have original := ownerTable_published rows.toLayout src fp fields room image
  apply original.kept
  · intro k hk
    have small : k < 16 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; omega
    apply preserve m _ (i:=0) (Nat.zero_le count)
    intro j _ hj
    obtain ⟨merged,_,_,tail⟩ := SignedTaskArena.produced_addresses rows src placed geom extra room hj span
    change (owned j).layout.merged=rows.merged+_ at merged
    change rows.sorted ≤ (owned j).layout.tail at tail
    change _ ≠ (owned j).layout.merged ∧ (_ < (owned j).layout.tail ∨ _)
    rw [fp]; exact ⟨by omega,Or.inl (by omega)⟩
  · intro i _
    apply preserve m _ (i:=0) (Nat.zero_le count)
    intro j _ hj
    have bound := (global_spec rows.toLayout src hj).1
    obtain ⟨merged,_,endTail,_⟩ := SignedTaskArena.produced_addresses rows src placed geom extra room hj span
    change (owned j).layout.merged=rows.merged+_ at merged
    change (owned j).layout.tail+12 < rows.sorted+rows.padded at endTail
    change i*3+rows.calls ≠ (owned j).layout.merged ∧ (_ ∨ (owned j).layout.tail+12 ≤ i*3+rows.calls)
    exact ⟨by omega,Or.inr (by omega)⟩

/-- Every genuine sparse serializer return preserves the real call header and
owner words using its actual three write regions. -/
theorem OwnerTable.sparse (old : OwnerTable pub m f owner) (l : SparseExterior.Layout)
    (owned : ℕ → SparseExterior.Owned) (fp : (pub 0).val=l.frame) (loaded : l.Loaded (readings m))
    (frame : l.frame+92 < 2^w) (header : l.control+36 < 2^w)
    (initial : ∀ i < l.count, (owned i).Initial l i m)
    (safe : ∀ i < l.count, ∀ j < i, ∀ a, (owned i).Source l i a → (owned j).Outside l j a)
    (registers : ∀ i < l.count, ∀ k ∈ [0,14,15], (owned i).Outside l i (l.frame+k))
    (owners : ∀ i < l.count, ∀ j < f.count, (owned i).Outside l i (f.address j))
    {s : Bank w} (r : Returns SparseExterior.prepare pub mac s m) :
    OwnerTable pub r.val.2.2 f owner := by
  obtain ⟨es,t,next,run,_,effect,_⟩ := SparseExterior.prepare_run (pub:=pub) (mac:=mac) s m l owned fp
    loaded frame header initial safe
  have output := (r.property.unique_of_deterministic SparseExterior.ordinary.1 run).2.2
  rw [output]
  have keep (a : ℕ) (clear : ∀ j < l.count, (owned j).Outside l j a) : next a=m a := by
    apply Fin.ext
    change readings next a=readings m a
    rw [effect]
    exact SparseExterior.written_preserve l owned (readings m) (i:=0) (Nat.zero_le _) a fun j _ hj => clear j hj
  exact old.kept (fun k hk => keep _ (fp ▸ fun i hi => registers i hi k hk))
    (fun j hj => keep _ fun i hi => owners i hi j hj)

/-- The final real typed serializer leaves exactly the dispatch owner roster
given by the preceding physical writers. -/
theorem OwnerTable.typed {gen : CellMacro.Generator.Fragment CellMacro.Generator.IO} {n : ℕ}
    (old : OwnerTable pub m f owner) (rows : TypedRowsAt gen n pub m)
    {s : Bank w} (r : Returns TypedBatch.entry pub mac s m) : OwnerTable pub r.val.2.2 f owner := by
  obtain ⟨es,t,run,_,_⟩ := TypedBatch.entry_run pub mac s m rows.tasks rows.frame rows.width rows.base rows.len
    rows.space rows.allocated rows.stored rows.taskRoom
  rw [(r.property.unique_of_deterministic (by decide) run).2.2]
  obtain ⟨frame,keep⟩ := rows.control.survives
  rw [old.frame] at keep
  refine ⟨frame.trans old.frame,fun i hi => ?_⟩
  change (TypedBatch.written m rows.tasks rows.count (f.address i)).val=_
  rw [keep i hi]; exact old.atRow i hi

end RoutingISA.CellDispatch

end BorderVNP
end Computability
end OAI
