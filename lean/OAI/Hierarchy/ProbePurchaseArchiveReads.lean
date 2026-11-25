import OAI.Hierarchy.ProtocolRAMCatalystPurchasedBirth
import OAI.Hierarchy.ProbeRetainedLive
import OAI.Hierarchy.ProbeObservedReplay

namespace OAI
/-! # The same affirmative decisions, tiles and public header at the chronological replay score -/

noncomputable section
namespace Hierarchy.ProtocolRAM.StripDirectory
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage PurchaseFrozen
open scoped Classical

variable {z d k q goods : ℕ}
local notation "W" => Native.wordBits z d Native.copies

/-- Starting with the actual archive at this purchase's first reserve
boundary, transport just its genuine cells through all events and both
preceding threshold scans of the current inner attempt. -/
theorem ArchiveReads.replay {sh : Shelf} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^z))}
    {depth start : ℕ} {phase : PhasePrice} {T : ℝ} {kind : ℕ} {frozen : Shelf.Mem z d}
    (C : Calendar.Chart W q goods) (mem : Memory W) (p h j b : ℕ)
    (A : ArchiveReads sh S π depth start phase T kind frozen (Calendar.reserveState C mem p h 0) k)
    (ready : Calendar.mounted C (Calendar.purchaseTail C.mesh p h j b) (Calendar.reserveState C mem p h 0))
    (archive : ∀ x,ArchiveCell (z:=z) (d:=d) (k:=k) sh S depth start x→
      ∀ e∈Calendar.purchaseTail C.mesh p h j b,Calendar.protected C x e)
    (step : Calendar.ready C (.attempt (.inner p h j b)) (Calendar.innerState C mem p h j b))
    (before : ∀ x,ArchiveCell (z:=z) (d:=d) (k:=k) sh S depth start x→
      let a:=Calendar.Attempt.inner p h j b
      x< C.stopAt a ∧ x<(C.frozen a).start ∧ x<(Calendar.repair C a).tests.excess.out ∧
        x<(Calendar.repair C a).tests.payload.out) :
    ArchiveReads sh S π depth start phase T kind frozen (Calendar.replayScoreMemory C mem p h j b) k := by
  apply A.change
  intro x hx
  let a:=Calendar.Attempt.inner p h j b
  let B:=Calendar.repair C a
  let state:=Calendar.innerState C mem p h j b
  obtain ⟨guard,frozen,excess,payload⟩ := before x hx
  change B.tests.payload.after (B.tests.excess.after (Calendar.prepared C a state)) x=_
  rw [B.tests.payload.frame _ x payload,B.tests.excess.frame _ x excess]
  change (C.frozen a).after ((Calendar.guard C a).apply state) x=_
  rw [(C.frozen a).frame _ x step.2.1 (Or.inl frozen)]
  have unchanged : (Calendar.guard C a).apply state x=state x := by
    have below : x < C.stopAt a := guard
    simp [Calendar.guard,Pass.apply,image,ThreeFlat.RAM.fillSegment,not_le.mpr below]
  exact unchanged.trans (Calendar.purchase_archive C mem p h j b x ready (archive x hx))

end Hierarchy.ProtocolRAM.StripDirectory
end

end OAI
