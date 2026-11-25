import OAI.Computability.BorderVNP.FiniteEvaluatorCells

/-! # Shared state after the finite-field cell stage

The signed validator may admit several private branch strings. Every
returning cell stage leaves the same register bank and the same pair of
chronologically written memory images, so its continuation can read the
original scalar column and frame in their allocated regions.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.Cells

open VPVNP.BurstRAM RoutingISA TypedTaskBuilder

variable {w n : ℕ} {F : Type*} [Fintype F]
variable (X : Inputs F) {pub : Arg → Word w} {m : Memory w}

/-- Exact memory image of the signed packet stores followed by the scalar stores. -/
def Inputs.post (mem : Memory w) : Memory w :=
  FiniteScalarBatch.written (TypedBatch.written mem X.tasks X.count) X.rows X.count

/-- Both writes preserve all words below the scratch arena and outside the published call table. -/
theorem post_outside {codec : Codec} (h : Prepared X pub m n codec) {a : ℕ} (below : a<X.layout.scratch)
    (apart : a<X.layout.calls ∨ X.layout.calls+3*X.layout.cells≤a) : X.post m a=m a := by
  unfold Inputs.post
  rw [FiniteScalarBatch.written_below _ _ _ _ (fun j hj => by
    have start := (h.arenas.starts j hj).2.1
    change (X.rows j).task.cell.scratchBase = _ at start
    omega)]
  exact TypedBatch.preserve m X.tasks (i:=0) (Nat.zero_le _) a
    (fun j _ hj => TypedTaskBuilder.below X.layout X.publicMem h.arenas hj below apart)

/-- Any word in a protected source column survives the entire stage. -/
theorem post_source {codec : Codec} (h : Prepared X pub m n codec) {base len i : ℕ}
    (range : X.layout.SourceRange base len) (hi : i<len) : X.post m (base+i)=m (base+i) :=
  post_outside X h (by have := range.end_le; omega) (by rcases range.calls with hl|hr <;> omega)

/-- Every word of the 112-word frame survives the entire stage. -/
theorem post_frame {codec : Codec} (h : Prepared X pub m n codec) {i : ℕ} (hi : i<112) :
    X.post m ((pub 0).val+i)=m ((pub 0).val+i) := by
  rw [h.pointer]
  exact post_outside X h (by have := h.arenas.calls; have := h.room.outputs.1; omega)
    (.inl (by have := h.room.outputs.1; omega))

/-- Erasing only the private events exposes the common terminal registers and memory
of any two actual returning runs, even with different private signs and tapes. -/
theorem same_post {mac : TeamOpcode.Macros w 8} {s es t mt fs z mz}
    (left : Runs pub mac code s m es t mt) (right : Runs pub mac code s m fs z mz) : t=z ∧ mt=mz := by
  obtain ⟨_,a⟩ := left.eraseCalls
  obtain ⟨_,b⟩ := right.eraseCalls
  exact (a.unique_of_deterministic (by decide) b).2

/-- On every returning branch, the literal validator and scalar opcodes perform
exactly the specified chronological writes to the live shared memory. -/
theorem post_memory_for [Field F] (codec : Codec) (h : Prepared X pub m n codec) {s es z mz}
    (r : Runs pub (TeamSiteEvents.macros (library F codec) (CompactMachine.nativeClock n)) code s m es z mz) :
    mz=X.post m := by
  let mac := TeamSiteEvents.macros (w:=w) (library F codec) (CompactMachine.nativeClock n)
  let after := TypedBatch.written m X.tasks X.count
  have frameFit : (pub 0).val+90 < 2^w := by rw [h.pointer]; have := h.room.frame; omega
  have source : (m ((pub 0).val+89)).val = X.layout.tasks := h.pointer ▸ h.fields.outer.2.2.2.2.2.2.1
  have space : X.layout.tasks+7*X.count ≤ 2^w := by
    have count := X.layout.before_le X.publicMem X.layout.cells
    have bound := h.room.tasks
    unfold Inputs.count
    omega
  have rooms (i : ℕ) (hi : i<X.count) : (X.tasks i).callRow+2 < 2^w ∧ (X.tasks i).cell.Room w := by
    refine ⟨?_,task_room X.layout X.publicMem h.room h.arenas hi⟩
    rw [(h.arenas.starts i hi).1,Layout.call]
    have one := (global_spec X.layout X.publicMem hi).1
    have bound := h.room.calls
    omega
  obtain ⟨_,t,entry,_,_⟩ := TypedBatch.entry_run pub mac s m X.tasks frameFit (h.pointer ▸ h.width)
    source (h.pointer ▸ h.countWord) space (allocated X.layout X.publicMem h.room h.arenas)
    (fun i hi => ⟨h.stored i hi,h.data i hi⟩) rooms
  obtain ⟨v,mv,_,_,_,first,last⟩ := Runs.seq_iff.mp r
  obtain ⟨u,mu,_,_,_,head,dispatch⟩ := Runs.seq_iff.mp first
  obtain ⟨_,rfl,rfl⟩ := entry.unique_of_deterministic (by decide) head
  have frame : CellDispatch.Frame.ofMemory pub m = ⟨X.layout.team,X.layout.calls,X.layout.cells⟩ := by
    have f := h.fields.outer
    change CellDispatch.Frame.mk _ _ _ = _
    rw [h.pointer]
    exact (congrArg (fun t => CellDispatch.Frame.mk t _ _) f.1).trans
      (congrArg₂ (CellDispatch.Frame.mk _) f.2.2.1 f.2.2.2.1)
  have saved := (control X.layout X.publicMem h.room h.arenas h.pointer frame).survives.1
  have capacity : (CellDispatch.Frame.ofMemory pub after).base+3*(CellDispatch.Frame.ofMemory pub after).count ≤ 2^w := by
    rw [show CellDispatch.Frame.ofMemory pub after = _ from saved,frame]
    exact h.room.calls.le
  obtain ⟨_,_,_,_,_,rfl⟩ := CellDispatch.directory_decode (by omega) capacity dispatch
  obtain ⟨_,_,_,_,_,_,_,only⟩ := FiniteScalarBatch.prepared_field F (CompactMachine.siteLibrary codec.driver)
    (fun _ => signedReturn) pub v m X.layout X.publicMem X.rows X.digits X.claim h.pointer
    h.fields h.width h.countWord h.room h.arenas h.control h.tails h.ids h.stored h.data h.bank h.tail h.stream
    h.scalarClock h.placed.cap
  exact (only _ _ _ last).2.2

/-- The dense private input returns the same chronological packet and scalar stores. -/
theorem post_memory [Field F] (h : Prepared X pub m n) {s es z mz}
    (r : Runs pub (TeamSiteEvents.macros (library F) (CompactMachine.nativeClock n)) code s m es z mz) :
    mz=X.post m :=
  post_memory_for X .dense h r

end FiniteEvaluator.Cells

end BorderVNP
end Computability
end OAI
