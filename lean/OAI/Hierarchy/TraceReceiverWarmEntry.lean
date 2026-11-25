import OAI.Hierarchy.TraceReceiverWarmSources

namespace OAI
/-! # Reading a bounded native journal after the low owner and high codebook mounts -/

namespace Hierarchy.TraceReceiverWarmEntry
open ThreeFlat Diagonal PhysicalStage NavigationPass TickWorkspace RAM
open RAM.NavigationNodeRows Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section

/-- A journal has no recorded address beyond its heap end. Complete its read
map there with the actual entry words, which include the mounted S38 library. -/
def seen {W : ℕ} (stop : ℕ) (registered entry : Memory W) : Memory W :=
  fun i=>if i< stop then registered i else entry i

theorem visits {F Pins : Type} [Field F] {W K heads heap d l : ℕ} {cur ctr : Word W}
    {A : State d l} (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r)
    (L : A.Words Pins) (C : r.Charges) (O : A.ArchiveSites) (path : r.ArchivePath h C O)
    (registered entry : Memory W) (allow : StaticMotif F→Prop)
    (actual : r.WordVisits (RecordedWordStep K cur ctr heads heap registered Pins allow) h J L C O path) :
    r.WordVisits (RecordedWordStep K cur ctr heads heap (seen heap registered entry) Pins allow) h J L C O path :=
  r.wordVisits_mono _ _ (fun R i L w O c p=>RecordedWordStep.transfer
    (fun _i hi=>ite_eq_left hi) R i L w O c p) h J L C O path actual

/-- Low S5/S11/S18 writes and the high S38 codebook are handled separately.
Only the genuine active part of the registered journal has to survive.
The saved charge/node arrays and directory are from the physical registrar. -/
theorem warm {W u heap : ℕ} {b : Banks} {xs : List NodeRow} {reg saved entry : Memory W}
    (source : NativeNavigation.WarmSources u b xs entry saved entry)
    (below : heap≤base u 40)
    (frame : ∀ i,base u 20≤ i→i<heap→entry i=reg i) :
    NativeNavigation.WarmSources u b xs (seen heap reg entry) saved entry := by
  refine ⟨?_,?_,source.published,source.kind,source.directory⟩
  · intro i lo _
    by_cases hi : i<heap
    · simpa [seen,hi] using frame i lo hi
    · simp [seen,hi]
  · intro i lo _
    have bound:=apart (u:=u) (by decide : 40<49)
    simp [seen,show ¬i<heap by omega]

end
end Hierarchy.TraceReceiverWarmEntry

end OAI
