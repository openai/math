import OAI.Computability.BorderVNP.CellTeamSupplementalClock
import OAI.Computability.BorderVNP.RoutingISATypedNativeValue

/-! # Live operand words and charged histories through the native private-cell stage -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacket.Supplement.Batch

open VPVNP.BurstRAM CellDispatch CompactMachine

variable {w count : ℕ} {Site : Type}

/-- The typed-task producer writes only its compact rows, the global call owner
column and its returned row count. -/
theorem task_published_outside (l : TypedTaskBuilder.Layout) (m : ℕ → ℕ) (a : ℕ) (clear : ¬ l.outputAt a) :
    l.published m a = m a := by
  have frame : a ≠ l.frame+90 := fun h => clear (.inr (.inr h))
  rw [TypedTaskBuilder.Layout.published,Function.update_of_ne frame,l.image_outside m l.cells le_rfl a clear]

/-- Read back any genuine live descriptor, reference, source field or guessed bit
that lies outside all three mutation regions. This holds for every private signed
call outcome and includes every intermediate store of the packet preparation. -/
theorem preserved_after_calls {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    (l : TypedTaskBuilder.Layout) (m m₁ : Memory w) (owned : ℕ → Owned Site)
    (published : readings m₁=l.published (readings m)) (a : ℕ) (clear : ¬ l.outputAt a)
    (outside : ∀ i < count, (owned i).cell.Outside a ∧ (owned i).typed.Outside w a) :
    let patched := written m₁ (fun i => (owned i).cell) count
    let mt := TypedBatch.written patched (fun i => (owned i).typed) count
    (pub 0).val+15 < 2^w →
    (Frame.ofMemory pub mt).base+3*(Frame.ofMemory pub mt).count ≤ 2^w →
    ∀ {s es t mf}, Runs pub mac callOwnedCells s mt es t mf → mf a=m a := by
  intro patched mt frame room s es t mf run
  obtain ⟨_,_,_,_,_,done⟩ := directory_decode frame room run
  rw [done]
  have typed : mt a=patched a :=
    TypedBatch.preserve patched (fun i => (owned i).typed) (i:=0) (Nat.zero_le count) a
      (fun i _ hi => (outside i hi).2)
  have patch : patched a=m₁ a :=
    preserve m₁ (fun i => (owned i).cell) (i:=0) (Nat.zero_le count) a (fun i _ hi => (outside i hi).1)
  rw [typed,patch]
  apply Fin.ext
  change readings m₁ a=readings m a
  rw [published,task_published_outside l _ a clear]

/-- Accepted histories of the combined supplemental prepass, real typed initializer
and signed directory calls fit the actual accumulated sparse charge. The private
tape clock and probe width apply separately to every instruction. -/
theorem within_prepared {table controls n : ℕ} {pub : Arg → Word w}
    (routines : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w) (owned : ℕ → Owned Site)
    (cells : ℕ → CellInput) (frame : (pub 0).val+92 < 2^w) (pointer : readings m ((pub 0).val+92)+11 < 2^w)
    (width : readings m ((pub 0).val+30)=w) (len : readings m ((pub 0).val+90)=count)
    (base : readings m ((pub 0).val+89)=table) (ctrl : readings m (readings m ((pub 0).val+92)+11)=controls)
    (taskFit : table+7*count ≤ 2^w) (controlFit : controls+4*count ≤ 2^w)
    (init : ∀ i < count, Initial (owned i) table controls i m)
    (alloc : Allocation (pub 0).val table controls count w owned) :
    let rows := fun i => (owned i).typed
    let patched := written m (fun i => (owned i).cell) count
    let mt := TypedBatch.written patched rows count
    let f := Frame.ofMemory pub patched
    let mac := install TypedBatch.cellDriver n routines
    TypedBatch.PlacedRows pub patched rows count n cells → TypedBatch.ControlLayout pub patched rows count →
    f.base+3*f.count ≤ 2^w →
    ∀ bits es, TeamRAM.execute ((prepareArguments.seq callOwnedCells).program.fetch pub mac) ⟨0,s⟩ m bits = some es →
      TeamContraction.Within (nativeCharge owned f mt count) (TeamScales.width n (1/2)) (n^25) es := by
  intro rows patched mt f mac placed control space bits es returned
  obtain ⟨pre,t,prep,cost,flags,_⟩ := prepareArguments_run (pub:=pub) (mac:=mac) s m owned frame pointer width len
    base ctrl taskFit controlFit init alloc
  have ff : Frame.ofMemory pub mt=f := control.survives.1
  have fit : (Frame.ofMemory pub mt).base+3*(Frame.ofMemory pub mt).count ≤ 2^w := ff ▸ space
  have mem := ((CompactBatch.mem_prepared_iff_of (by decide) (by decide) prep
    (mem_choices TypedBatch.cellDriver n routines) (by omega) fit).mp returned).1
  rw [ff] at mem
  obtain ⟨post,hpost,rfl⟩ := Finset.mem_map.mp mem
  have bounded := TypedBatch.directory_within TypedBatch.cellDriver routines placed alloc.typed
    (fun i hi => (init i hi).typedRoom.2) control post hpost
  have ordinary (e : TeamRAM.Event w) (he : e ∈ pre) : e.action.extra ≤ TeamScales.width n (1/2) ∧ e.choices.length ≤ n^25 := by
    have zero := prep.deterministic_extra (by decide) e he
    rw [(flags e he).1]
    exact ⟨by omega,Nat.zero_le _⟩
  change TeamContraction.Within _ _ _ (pre++post)
  refine ⟨?_,fun e he => (List.mem_append.mp he).elim (fun hp => (ordinary e hp).1) (bounded.length e),
    fun e he => (List.mem_append.mp he).elim (fun hp => (ordinary e hp).2) (bounded.choices e)⟩
  rw [VPVNP.RAMBuckets.cost_append]
  exact Nat.add_le_add cost bounded.cost

end RoutingISA.CellPacket.Supplement.Batch

end BorderVNP
end Computability
end OAI
