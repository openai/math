import OAI.Computability.BorderVNP.DiagonalNativeCellRoster
import OAI.Computability.BorderVNP.RoutingISAScheduleClockArgumentVisits

/-! # Dispatch owner readback on the complete native signed argument stage -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM CellDispatch TypedTaskBuilder CellPacket.Supplement.Batch

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s : Bank w} {m : Memory w}

/-- All genuine returns from the three argument writers have the published packed
pointers and words at the exact memory produced by their consecutive execution. -/
theorem SparseCallInput.return_memory (src : SparseCallInput pub m)
    (r : Returns (.block [CellPacket.Supplement.Batch.entry,SparseExterior.prepare,TypedBatch.entry]) pub mac s m) :
    r.val.2.2=TypedBatch.written src.compressed src.tasks src.count := by
  obtain ⟨es,t,first,_,_,_⟩ := entry_run (pub:=pub) (mac:=mac) s m src.merge src.frame src.pointer src.length src.base
    src.indirect src.taskRoom src.controlRoom src.source src.apart
  let patched := written m src.merge src.count
  obtain ⟨bs,u,mu,second,_,effect,_⟩ := SparseExterior.prepare_run (pub:=pub) (mac:=mac) t patched src.layout src.owned
    src.root src.loaded (src.root ▸ src.frame) src.header src.initial src.independent
  have same : mu=src.compressed := funext fun a => Fin.ext (congrFun (effect.trans src.image.symm) a)
  subst mu
  obtain ⟨xs,v,last,_,_⟩ := TypedBatch.entry_run pub mac u src.compressed src.tasks src.typed.frame src.typed.width
    src.typed.base src.typed.length src.typed.space src.typed.allocated src.typed.stored src.typed.room
  exact (r.property.unique_of_deterministic (by decide) (first.seq (second.seq last))).2.2

/-- From the true sparse source and its actual encoded writes, the final native
typed return reads the same complete roster as the preceding patched memory. -/
theorem SparseCallInput.return_roster (src : SparseCallInput pub m) (f : Frame) (owner : ℕ → ℕ)
    (old : OwnerTable pub (written m src.merge src.count) f owner)
    (registers : ∀ i < src.layout.count, ∀ k ∈ [0,14,15], (src.owned i).Outside src.layout i (src.layout.frame+k))
    (owners : ∀ i < src.layout.count, ∀ j < f.count, (src.owned i).Outside src.layout i (f.address j))
    (r : Returns (.block [CellPacket.Supplement.Batch.entry,SparseExterior.prepare,TypedBatch.entry]) pub mac s m) :
    OwnerTable pub r.val.2.2 f owner := by
  let patched := written m src.merge src.count
  have keep (a : ℕ) (clear : ∀ i < src.layout.count, (src.owned i).Outside src.layout i a) :
      src.compressed a=patched a := by
    apply Fin.ext
    change readings src.compressed a = readings patched a
    rw [src.image]
    exact SparseExterior.written_preserve src.layout src.owned (readings patched) (i:=0) (Nat.zero_le _) a
      fun i _ hi => clear i hi
  have compact : OwnerTable pub src.compressed f owner := old.kept
    (fun k hk => keep _ (src.root ▸ fun i hi => registers i hi k hk))
    (fun j hj => keep _ fun i hi => owners i hi j hj)
  rw [src.return_memory r]
  obtain ⟨frame,column⟩ := src.typed.control.survives
  rw [compact.frame] at column
  refine ⟨frame.trans compact.frame,fun i hi => ?_⟩
  change (TypedBatch.written src.compressed src.tasks src.count (f.address i)).val=_
  rw [column i hi]; exact compact.atRow i hi

/-- On an actual return of the six signed argument stages, the full native row
count, order and ownership are precisely the ones read by the real typed-task
builder. The allocator's three disjoint windows prove preservation of both the
owner and frame columns through the subsequent sparse writes. -/
theorem ownerTable_on_arguments {Site : Type} (r : Returns SignedPrep.arguments pub mac s m)
    (rows : CellControlRows.Layout) (arena : SignedTaskArena.Layout) (ctl : ℕ)
    (p : ℕ → CellPacket.Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List CellSparse.Record) :
    let parts := (argumentVisitsEquiv pub mac s m).symm r
    let old := readings parts.1.val.2.2
    ∀ src : SparseCallInput pub parts.2.1.val.2.2,
    (pub 0).val=rows.frame → rows.toLayout.Fields old → rows.toLayout.Room old w →
    (∀ c < rows.cells, old (rows.sorted+rows.padded+(rows.stops+c))-old (rows.sorted+rows.padded+c)-1 =
      3*((p c).parts.length+3)) →
    rows.frame+16 ≤ rows.sorted → rows.frame+16 ≤ rows.merged →
    rows.sorted+rows.padded ≤ rows.calls → rows.merged+rows.cells ≤ rows.calls →
    src.merge=(fun i => (produced rows old p geom extra i).cell) → src.count=rows.before old rows.cells →
    src.layout=SparseExterior.batchLayout arena rows.frame ctl src.count →
    (∀ i < src.count, (src.owned i).global < arena.fragments.cells) →
    (∀ i < src.count, (src.owned i).field.bytes.length ≤ arena.fragments.stride) →
    rows.frame+112 ≤ arena.fragments.external → rows.calls=arena.before.limit → rows.cells ≤ arena.cube.cells →
    OwnerTable pub r.val.2.2 ⟨rows.team,rows.calls,rows.cells⟩ (rows.owner old) := by
  intro parts old src fp fields room span low low' high high' merge count layout global width early calls cells
  obtain ⟨es,t,mt,builder,_,image⟩ := TypedTaskBuilder.program_run pub mac parts.1.val.2.1 parts.1.val.2.2 rows.toLayout
    fp fields room
  have actual : readings parts.2.1.val.2.2=rows.toLayout.published old := by
    rw [(parts.2.1.property.unique_of_deterministic (by decide) builder).2.2]
    exact image
  let f := Frame.mk rows.team rows.calls rows.cells
  have patched : OwnerTable pub (written parts.2.1.val.2.2 src.merge src.count) f (rows.owner old) := by
    rw [merge,count]
    exact ownerTable_supplemented rows old p geom extra fp fields room actual span ⟨low,low'⟩ ⟨high,high'⟩
  have guards := SparseExterior.frame_owners_outside arena rows.frame ctl src.count src.owned f global width early calls cells
  have result := src.return_roster f (rows.owner old) patched (by
    rw [layout]
    intro i hi k hk
    have small : k < 112 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk; omega
    exact guards.1 i hi k small) (by rw [layout]; exact guards.2) parts.2.2
  have endState := congrArg (fun r : Returns SignedPrep.arguments pub mac s m => r.val.2.2)
    ((argumentVisitsEquiv pub mac s m).apply_symm_apply r)
  change parts.2.2.val.2.2=r.val.2.2 at endState
  rw [←endState]; exact result

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
