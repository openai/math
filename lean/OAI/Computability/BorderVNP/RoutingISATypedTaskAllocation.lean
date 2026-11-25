import OAI.Computability.BorderVNP.RoutingISATypedTaskPackets

/-! # Allocated scratch, burst and source intervals of the owned task scan

Scratch and burst addresses use fixed strides indexed by the original global
cell. Only the live spans are written. The proofs also apply to a packet whose
reserved descriptor rows are updated by the supplemental sidecar prepass.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.TypedTaskBuilder

open VPVNP.BurstRAM CellDispatch

variable (l : Layout) (mem : ℕ → ℕ)

/-- The order of the compact local table is strictly increasing in the global cell ID. -/
theorem global_strict {i j : ℕ} (ij : i < j) (hj : j < l.before mem l.cells) :
    globalCell l mem i < globalCell l mem j := by
  obtain ⟨_,oi,bi⟩ := global_spec l mem (ij.trans hj)
  obtain ⟨_,oj,bj⟩ := global_spec l mem hj
  by_contra! h
  rcases h.eq_or_lt with eqn|lt
  · rw [eqn] at bj; omega
  · have := l.before_strict mem lt oj; omega

/-- An actual read-only source lies before the scratch arena and outside the call table. -/
structure Layout.SourceRange (base len : ℕ) : Prop where
  /-- End of the supplied input. -/
  end_le : base+len ≤ l.scratch
  /-- This source cannot coincide with a call's published pointer or count. -/
  calls : base+len ≤ l.calls ∨ l.calls+3*l.cells ≤ base

/-- Scalar allocation bounds sufficient for all tasks in their actual ownership order. -/
structure Layout.Arenas (w : ℕ) (tasks : ℕ → TypedBatch.Task) : Prop where
  /-- The global owner table fits below the first scratch word. -/
  calls : l.calls+3*l.cells ≤ l.scratch
  /-- The compact task headers fit below the first scratch word. -/
  table : l.tasks+7*l.cells ≤ l.scratch
  /-- All allocated scratch windows end before the retained bursts. -/
  scratch : l.scratch+l.scratchStride*l.cells ≤ l.bursts
  /-- The seven scalar words retain the allocated starts, including after a supplemental update. -/
  starts : ∀ j < l.before mem l.cells,
    (tasks j).callRow=l.call (globalCell l mem j) ∧
    (tasks j).cell.scratchBase=l.scratch+l.scratchStride*globalCell l mem j ∧
    (tasks j).cell.burstBase=l.bursts+l.burstStride*globalCell l mem j
  /-- Every descriptor range used by a real task. -/
  descriptors : ∀ j < l.before mem l.cells, l.SourceRange (tasks j).cell.descriptorBase (3*(tasks j).cell.chunks.length)
  /-- Every actual external input span, including its compact report/use suffix. -/
  external : ∀ j < l.before mem l.cells, l.SourceRange (tasks j).cell.externalBase (tasks j).cell.external.length
  /-- Actual public and private chunk source ranges. -/
  chunks : ∀ j < l.before mem l.cells, ∀ chunk ∈ (tasks j).cell.chunks,
    chunk.endSource ≤ l.scratch ∧ (chunk.endSource ≤ l.calls ∨ l.calls+3*l.cells ≤ chunk.base)
  /-- A sparse task writes only its actual bit length and actual packed word length. -/
  widths : ∀ j < l.before mem l.cells,
    (tasks j).cell.payload.length ≤ l.scratchStride ∧ ((tasks j).cell.burst w).length ≤ l.burstStride

variable {w : ℕ} {tasks : ℕ → TypedBatch.Task} (room : l.Room mem w) (ar : l.Arenas mem w tasks)

include ar in
/-- A source address below scratch and outside the call table survives every task. -/
theorem below {i a : ℕ} (hi : i < l.before mem l.cells) (ha : a < l.scratch)
    (call : a < l.calls ∨ l.calls+3*l.cells ≤ a) : (tasks i).Outside w a := by
  obtain ⟨cr,sr,br⟩ := ar.starts i hi
  have hc := (global_spec l mem hi).1
  have := ar.scratch
  simp only [TypedBatch.Task.Outside,cr,sr,br,Layout.call]
  rcases call with h|h <;> exact ⟨Or.inl (by omega),Or.inl (by omega),by omega,by omega⟩

include ar room

/-- All reads of a later task survive every earlier packet, and all earlier published
output words survive every later task. No copies of unused stride cells are required. -/
theorem allocated : TypedBatch.Allocated w l.tasks (l.before mem l.cells) tasks := by
  have total := l.before_le mem l.cells
  constructor
  · intro i j hij hj a ha
    have hi := hij.trans hj
    rcases ha with h|h|h|⟨u,hu,h⟩
    · apply below l mem ar hi (by have := ar.table; omega)
      rcases room.ownerTasks with z|z
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
    · have src := ar.descriptors j hj
      apply below l mem ar hi (by have := src.end_le; omega)
      rcases src.calls with z|z <;> omega
    · have src := ar.external j hj
      apply below l mem ar hi (by have := src.end_le; omega)
      rcases src.calls with z|z <;> omega
    · obtain ⟨end',apart⟩ := ar.chunks j hj u hu
      apply below l mem ar hi (by omega)
      rcases apart with z|z <;> omega
  · intro i hi k hk
    obtain ⟨cr,_,br⟩ := ar.starts i hi
    have hc := (global_spec l mem hi).1
    have := ar.calls; have := ar.scratch
    rw [cr,br,Layout.call]
    omega
  · intro i j hij hj a ha
    obtain ⟨ci,si,bi⟩ := ar.starts i (hij.trans hj)
    obtain ⟨cj,sj,bj⟩ := ar.starts j hj
    have ord := global_strict l mem hij hj
    have ciFit := (global_spec l mem (hij.trans hj)).1
    have cjFit := (global_spec l mem hj).1
    have wi := (ar.widths i (hij.trans hj)).2
    have wj := (ar.widths j hj).1
    have sjFit := Nat.mul_le_mul_left l.scratchStride (show globalCell l mem j+1 ≤ l.cells from cjFit)
    have ordered := Nat.mul_le_mul_left l.burstStride (show globalCell l mem i+1 ≤ globalCell l mem j from ord)
    simp only [Nat.mul_succ] at sjFit ordered
    have := ar.scratch; have := ar.calls
    simp only [bi,ci,Layout.call] at ha
    simp only [TypedBatch.Task.Outside,sj,bj,cj,Layout.call]
    rcases ha with h|h|h
    · exact ⟨Or.inr (by omega),Or.inl (by omega),by omega,by omega⟩
    · exact ⟨Or.inl (by omega),Or.inl (by omega),by omega,by omega⟩
    · exact ⟨Or.inl (by omega),Or.inl (by omega),by omega,by omega⟩

/-- Each native initializer obeys its local memory room conditions. -/
theorem task_room {i : ℕ} (hi : i < l.before mem l.cells) : (tasks i).cell.Room w := by
  have hc := (global_spec l mem hi).1
  obtain ⟨_,sr,br⟩ := ar.starts i hi
  obtain ⟨hp,hb⟩ := ar.widths i hi
  have ext := (ar.external i hi).end_le
  have desc := (ar.descriptors i hi).end_le
  have sFit := Nat.mul_le_mul_left l.scratchStride (show globalCell l mem i+1 ≤ l.cells from hc)
  have bFit := Nat.mul_le_mul_left l.burstStride (show globalCell l mem i+1 ≤ l.cells from hc)
  simp only [Nat.mul_succ] at sFit bFit
  have := ar.scratch; have := room.scratch; have := room.bursts
  refine ⟨?_,fun u hu => (ar.chunks i hi u hu).1.trans (by rw [sr]; omega),desc.trans (by rw [sr]; omega),
    Or.inl (ext.trans (by rw [sr]; omega)),Or.inl (by rw [sr,br]; omega),by omega,by rw [sr]; omega,
    by rw [br]; omega,by omega⟩
  by_contra! hn; have hw := Nat.eq_zero_of_le_zero hn; subst w
  have := room.frame
  norm_num at this

/-- Private packet preparation preserves all dispatch fields and every global owner word. -/
theorem control {pub : Arg → Word w} {after : Memory w} (hp : (pub 0).val=l.frame)
    (f : CellDispatch.Frame.ofMemory pub after=⟨l.team,l.calls,l.cells⟩) :
    TypedBatch.ControlLayout pub after tasks (l.before mem l.cells) := by
  constructor
  · intro j hj k hk
    have small : k < 112 := by simp at hk; omega
    have := room.outputs.1
    apply below l mem ar hj (by rw [hp]; have := ar.calls; omega) (Or.inl (by rw [hp]; omega))
  · intro j hj i hi
    rw [f] at hi ⊢
    obtain ⟨cj,sj,bj⟩ := ar.starts j hj
    have hc := (global_spec l mem hj).1
    have := ar.calls; have := ar.scratch
    change i < l.cells at hi
    simp only [CellDispatch.Frame.address,TypedBatch.Task.Outside,sj,bj,cj,Layout.call]
    refine ⟨Or.inl (by omega),Or.inl (by omega),?_,?_⟩ <;> omega

end RoutingISA.TypedTaskBuilder

end BorderVNP
end Computability
end OAI
