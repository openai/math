import OAI.Hierarchy.TraceReceiverSelector
import OAI.ThreeFlat.Diagonal.NavigationTerminalWindow

namespace OAI
/-! # The original selector words in a receiver's initialized archive -/
noncomputable section
namespace Hierarchy.TraceFactorReceiver.Selector
open ThreeFlat Diagonal RAM Computability.VPVNP.BurstRAM PrivateRAM NavigationPass NavigationDirectory
open scoped Fin.CommRing
variable {w n cap p : ℕ} (text : ℕ) (textRoom : text≤w^2) (self : Fin (w^2)→Bool)
variable (index : Word (64*w)) (params : Fin n→Word (64*w)) (sel : Fin (cap+1)→Bool)
local notation "head" => GridReceiverHeader.header text textRoom self index params sel

/-- The reads remain valid through initialization and registration whenever
the original selector window survives in the same RAM. -/
theorem window (input : ℕ→Bool) (room : (head).length≤p)
    (stored : headerReads text textRoom self index params sel input)
    (a : Archive) (ss : List Stage) (next : Memory (64*w))
    (flag : a.phase=phase w n text) (old : a.oldHistory=phase w n text+1)
    (fresh : a.newHistory=phase w n text+1) (size : a.pairCapacity=cap)
    (below : phase w n text+(cap+1)≤a.seed)
    (keep : ∀ i : Fin (cap+1),next (phase w n text+i.val)=
      TickMountedPins.memory (w:=64*w) (fun j : Fin p=>input j.val) (phase w n text+i.val)) :
    a.RawWindow ss (body sel) next ∧ next a.phase=((sel 0).toNat : Word (64*w)) := by
  have reads (i : Fin (cap+1)) := (keep i).trans (word_at text textRoom self index params sel input room stored i)
  refine ⟨⟨by omega,by omega,by omega,?_⟩,?_⟩
  · intro j hj
    have h : j<cap := size ▸ hj
    simp only [Archive.hist,PackedStageArchive.Layout.source,old,fresh,ite_self,body,dite_eq_left h]
    simpa only [Fin.val_succ,Nat.add_assoc,Nat.add_comm 1 j] using reads (Fin.succ ⟨j,h⟩)
  · simpa only [flag,Fin.val_zero,Nat.add_zero] using reads 0

end Hierarchy.TraceFactorReceiver.Selector
end

end OAI
