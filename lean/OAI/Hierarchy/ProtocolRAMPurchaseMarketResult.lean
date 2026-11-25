import OAI.Hierarchy.ProtocolRAMPurchaseMarketRun
import OAI.Hierarchy.ProtocolRAMRunMemory

namespace OAI
/-! # Deterministic all-stage purchase result for a mutable commodity address -/

namespace Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section
variable {z d k : ℕ}

/-- Read the final memory of the literal program, using its publicly computed clock. -/
def result (sh : Shelf) (S : PurchaseSampler) (k depth : ℕ) (frozen : Mem z d) :=
  runMemory (sh.program S z d k depth) (sh.clock S z d k depth) frozen

theorem run (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ)
    (hd : 1≤d) (phase : PhasePrice) (T : ℝ) (kind : ℕ) (frozen fixture : Mem z d)
    (input : sh.Incoming (k:=k) S π depth phase T kind frozen)
    (prepared : ∀ i : Key z d k, sh.Prepared S depth fixture i frozen)
    (room : sh.flagsBase S z d k depth+count z d k*paths z S.degree depth<2^wordBits z d copies) :
    let out := sh.result S k depth frozen
    (sh.program S z d k depth).Exec frozen out (sh.clock S z d k depth) ∧
      sh.Untouched (k:=k) S depth frozen out ∧ (∀ i : Key z d k, sh.Views S π depth phase T kind frozen i out) ∧
      ∀ (i : Key z d k) (r : Fin (paths z S.degree depth)),
        out (sh.flagsBase S z d k depth+i.val*paths z S.degree depth+r.val)=
          MarkTape.encode (wordBits z d copies) ((sh.decisions S π depth phase T kind frozen i)[r.val]'(by simp)) := by
  obtain ⟨out,exec,frame,views,picks⟩ := sh.execute S π depth hd phase T kind frozen fixture input prepared room
  have eqn : sh.result S k depth frozen=out := runMemory_eq _ _ _ _ exec
  dsimp only
  rw [eqn]
  exact ⟨@exec, frame, views, picks⟩

end
end Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf

end OAI
