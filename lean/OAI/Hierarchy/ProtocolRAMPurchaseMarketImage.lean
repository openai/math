import OAI.Hierarchy.ProtocolRAMPurchaseMarketResult

namespace OAI
/-! # Exact low-level memory updates of every chronological purchase scan -/

namespace Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseCT
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {z d k : ℕ}

def fullImage (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ)
    (enc : ∀i : Key z d k,StageEncoding i) (m : Mem z d) : Mem z d :=
  let visited:=ProtocolRAMFrozenSweep.output (fun i=>sh.stageImage S π depth i (enc i)) (List.finRange _) m
  ProtocolRAMPurchaseFlagPack.output (fun i : Key z d k=>sh.flagBank S depth i) (paths z S.degree depth)
    (sh.flagsBase S z d k depth) visited

/-- The full native run equals the specified sequence even at owner scratch,
gate-compiler temporaries, padding, and untouched locations. -/
theorem result_eq_fullImage (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (depth : ℕ)
    (hd : 1≤d) (phase : PhasePrice) (T : ℝ) (kind : ℕ) (m fixture : Mem z d)
    (input : sh.Incoming (k:=k) S π depth phase T kind m)
    (prepared : ∀i : Key z d k,sh.Prepared S depth fixture i m)
    (enc : ∀i : Key z d k, StageEncoding i)
    (ct : ∀i,(sh.L S depth i).CTLoaded (banks (stage i)) (advisedStage z d π (stage i)) (enc i) m)
    (room : sh.flagsBase S z d k depth+count z d k*paths z S.degree depth<2^wordBits z d copies) :
    sh.result S k depth m=sh.fullImage S π depth enc m := by
  let cpu:=fun i : Key z d k=>sh.stageProgram S depth i
  let f:=fun i : Key z d k=>sh.stageImage S π depth i (enc i)
  let visited:=ProtocolRAMFrozenSweep.output f (List.finRange _) m
  have stepAt:=sh.frozenStepAt S π depth hd phase T kind m fixture input prepared enc ct
  obtain ⟨ran,_,_⟩:=ProtocolRAMFrozenSweep.run_exact cpu (sh.stageClock S depth) f
    (sh.Untouched (k:=k) S depth m) (sh.Prepared S depth fixture) (sh.Views S π depth phase T kind m)
    stepAt m (fun _ _=>rfl) prepared
  let R:=paths z S.degree depth
  let source:=fun i : Key z d k=>sh.flagBank S depth i
  have cap (i : Key z d k) : R≤(source i).size := (ProtocolRAMPurchaseSampler.lt_span R).le
  obtain ⟨packed,_,_,_,_⟩:=ProtocolRAMPurchaseFlagPack.pack source R (sh.flagsBase S z d k depth) visited
    (fun i=>sh.source_fit S depth i hd room) cap room
  exact runMemory_eq _ _ _ _ (ran.then packed)

end
end Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf

end OAI
