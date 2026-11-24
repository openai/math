import OAI.Computability.VPVNP.PairNativeFrameRun
import OAI.Computability.VPVNP.CompressorSourceTransport

/-! # External-memory footprint of the terminal vertex's geometry setup -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NativeFrame
open BurstRAM CompressorRecords.SourceTransport
open scoped Fin.CommRing

variable {w : ℕ}

theorem events_writes (degree : ℕ) (header : Word w) (m : Memory w) :
    Writes (fun _ => False) (events degree header m) := by
  intro a v h
  simp [events,preludeEvents,readEvents,fieldEvents,List.mem_replicate] at h

theorem events_after (degree : ℕ) (header : Word w) (m initial : Memory w) :
    after initial (events degree header m) = initial := by
  funext j; exact after_outside initial (events_writes degree header m) (fun hf => hf)

theorem events_reads (degree : ℕ) (header : Word w) (m : Memory w) :
    Reads (fun x => ∃ j : Fin 6, x = (header + (offsets j : Word w)).val) (events degree header m) := by
  intro a v h
  simp only [events,preludeEvents,readEvents,fieldEvents,List.mem_cons,List.mem_append,List.mem_replicate,
    List.not_mem_nil,or_false,reduceCtorEq,and_false,or_self,false_or,Event.read.injEq] at h
  rcases h with h|h|h|h|h|h
  · exact ⟨0,congrArg Fin.val h.1⟩
  · exact ⟨1,congrArg Fin.val h.1⟩
  · exact ⟨2,congrArg Fin.val h.1⟩
  · exact ⟨3,congrArg Fin.val h.1⟩
  · exact ⟨4,congrArg Fin.val h.1⟩
  · exact ⟨5,congrArg Fin.val h.1⟩

end PairSimulation.NativeFrame

end VPVNP
end Computability
end OAI
