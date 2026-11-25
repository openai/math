import OAI.Hierarchy.DescentPhysicalFundedRoom

namespace OAI
/-! # Access to original warm registers before the funded setup begins -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.Chronology DescentFallbackPeriod.Projected DescentSIMDLookup
open DescentFundedCensus Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} {u : a.DateInputs floor w} (z : u.FinalInputs)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "A" => (v).actor
local notation "actorBase" => (v).middle.stop b
local notation "scene" => (A).scene actorBase
local notation "rc" => a.rootPhase u.shape floor u.count u.hub u.g u.Y u.roots w
local notation "P" => a.stencilPhase u.shape floor u.count u.hub u.g u.Y
local notation "stop₀" => (v).finalEnd b
local notation "F₀" => (v).funded
local notation "fund" => (v).fundedEnd b
local notation "Q" => (v).venue.census
local notation "rows" => (A).hosts*(A).chunksPerHost
local notation "rank" => (v).middle.rootDepth
local notation "nodes" => (v).middle.rotorBits

theorem FinalInputs.prior_funding_ports (ready : u.Ready) (safe : z.Room)
    (_shapes : (Q).jobs=(A).shapes) (occupied : 0<(A).shapes) :
    (∀j : Fin (2*(F₀).capacity),(.lookup ((rc).tapped (j.cast (congrArg (2*·) z.signedCount))) .row:Expr).Fits w stop₀) ∧
    z.ports.stencil.Fits w stop₀ ∧ (∀j:Fin (Q).jobs,(FinalInputs.presence (a:=a) (floor:=floor) j).Fits w stop₀) ∧
    ∀s t,(z.ports.bank s t).Fits w stop₀:=by
  obtain ⟨_,_,a₁,a₂,a₃,a₄,a₅,a₆,a₇⟩:=ready.ordered
  have before:(v).actorEnd b≤ stop₀:=by omega
  have top:stop₀<2^w:=((F₀).room stop₀).trans_lt safe.fund
  have fromRoot:(rc).preparedEnd u.book=actorBase:=ready.rootEnd
  have old:(rc).projectionEnd≤(rc).preparedEnd u.book:=by
    have lim:=u.book.limits (rc).projectionEnd (v).middle.signedHosts (2^(v).middle.stencil.c) (v).middle.signedLanes
    exact lim.1.trans (lim.2.1.trans (lim.2.2.trans (Nat.le_add_right ..)))
  have actorStart:actorBase≤(v).actorEnd b:=ready.ordered.2.1
  have prepared:(rc).preparedEnd u.book≤ stop₀:=fromRoot.le.trans (actorStart.trans before)
  have signEnd:(rc).signedEnd≤ stop₀:=(Nat.le_add_right ..).trans (old.trans prepared)
  have taps (j : Fin (2*(F₀).capacity)):= (rc).tapped_fits (j.cast (congrArg (2*·) z.signedCount))
    (signEnd.trans_lt top)
  have sceneFit:=DateInputs.prior_actor_bank (a:=a) ready
  have f:(scene).Fits w stop₀:=⟨sceneFit.1,sceneFit.2.1,sceneFit.2.2.trans before⟩
  have multi:rows≤(A).shapes*rows:=by
    exact Nat.le_mul_of_pos_left rows occupied
  have crop:2^Nat.clog 2 rows≤(scene).size:=
    Nat.pow_le_pow_right (by decide) (Nat.clog_mono_right 2 multi)
  have pane:(P).output+2^Nat.clog 2 rows≤ stop₀:=
    (Nat.add_le_add ((Nat.le_add_right ..).trans (((rc).origin_le_projection.trans old).trans
        (fromRoot.le.trans (scene_after (A) actorBase)))) crop).trans f.2.2
  exact ⟨fun j=>⟨⟨(taps j).1,(taps j).2.1,(taps j).2.2.trans signEnd⟩,trivial⟩,
    ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (pane.trans_lt top),pane⟩,trivial⟩,
    fun _=>⟨f,trivial,trivial⟩,fun s t=>ProtocolRAMGeneratedWrite.fits_mono _ prepared
      ((rc).gathered_fits u.book u.bookFits (s,.inr t))⟩

include z in
/-- The sector's original actor bits at their actual whole-array addresses. -/
theorem FinalInputs.prior_funding_actors {h g M q : ℕ} (ready : u.Ready)
    (shapes : (Q).jobs=(A).shapes) (count : (Q).jobs=q) (size : rows=h*chunks g M)
    (cells : Fin q→Fin h→Fin g→Cell 1) (m : Memory w)
    (observed : ∀j (p:Row h g M),m ((FinalInputs.predecessor u).actor.base+j.val*(h*chunks g M)+(row h g M p).val)=
      ((data (cells j) p).val:Word w)) :
    ∀j:Fin q,DescentPackedZip.Source (FinalInputs.presence (a:=a) (floor:=floor) (j.cast count.symm)) (cells j) M m:=by
  intro j pos
  let i:Fin rows:=⟨(row h g M pos).val, by rw [size];exact (row h g M pos).isLt⟩
  have seen:=z.funded_presence_read ready shapes m (j.cast count.symm) i
  have stored:=observed j pos
  rw [show (FinalInputs.predecessor u).actor.base=(scene).base from rfl] at stored
  rw [show (row h g M pos).val=i.val from rfl,seen]
  simpa [i,size,Nat.add_assoc] using stored

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
