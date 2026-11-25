import OAI.Hierarchy.ProtocolRAMCalendarFailureVote
import OAI.Hierarchy.ProtocolRAMCalendarElection

namespace OAI
/-! # Native threshold readiness from the incoming market tape -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseFrozen PurchaseStage AttemptGate
open scoped Classical BigOperators Fin.CommRing

/-- Static sizes and confined operands of a single checked score pass. Its
total is supplied independently from the actual incoming stock and ROMs. -/
structure CheckLayout (c : Check) (w cut : ℕ) : Prop where
  score : c.term.Fits w cut
  afterCut : cut≤c.out
  addresses : c.out+(c.rows+1)<2^w
  threshold : c.bound<2^w

theorem CheckLayout.ready_of_below {w cut : ℕ} (c : Check) (s : CheckLayout c w cut)
    (before after : Memory w) (same : Below cut after before) (sum : (∑i,c.score before i)<2^w) :
    c.Ready after := by
  refine ⟨ProtocolRAMGeneratedWrite.fits_mono c.term s.afterCut s.score,s.addresses,s.threshold,?_⟩
  have agree : c.score after=c.score before :=
    funext fun i=>congrArg Fin.val (same.expr c.term (i.val:Word w) s.score le_rfl)
  simpa only [agree] using sum

private theorem keep_check {w cut : ℕ} (c : Check) (m base : Memory w)
    (keep : Below cut m base) (ol : cut≤c.out) : Below cut (c.after m) base := by
  intro x low
  exact (c.frame m x (low.trans_le ol)).trans (keep x low)

/-- The three tests become ready in order. A frozen scanner receipt, together
with geometry and three incoming finite sums, suffices before the event runs. -/
theorem Market.native_tests_ready {z d k q g : ℕ} (v : Market z d k) (B : Repair q g)
    (m : Shelf.Mem z d) (frozen : v.ready m)
    (left : CheckLayout B.tests.excess (wordBits z d copies) v.failures.base)
    (right : CheckLayout B.tests.payload (wordBits z d copies) v.failures.base)
    (disc : CheckLayout B.tests.discrepancy (wordBits z d copies) v.failures.base)
    (sumLeft : (∑i,B.tests.excess.score m i)<2^wordBits z d copies)
    (sumRight : (∑i,B.tests.payload.score m i)<2^wordBits z d copies)
    (sumDisc : (∑i,B.tests.discrepancy.score m i)<2^wordBits z d copies) :
    TestsReady B (v.prefix.after m) := by
  have start : v.failures.base≤v.prefix.start := by
    change v.failures.base ≤ min v.failures.base v.shelf.firstBase
    exact le_min le_rfl ((Nat.le_add_right ..).trans frozen.2.1)
  have first : Below v.failures.base (v.prefix.after m) m := by
    intro x low
    exact v.prefix.frame m x frozen (.inl (low.trans_le start))
  have second := keep_check _ _ _ first left.afterCut
  have third := keep_check _ _ _ second right.afterCut
  exact ⟨CheckLayout.ready_of_below _ left m _ first sumLeft,
    CheckLayout.ready_of_below _ right m _ second sumRight,
    CheckLayout.ready_of_below _ disc m _ third sumDisc⟩

end Hierarchy.ProtocolRAM.Calendar
end

end OAI
