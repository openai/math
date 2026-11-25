import OAI.Hierarchy.DescentFrontEarlierRoot
import OAI.Hierarchy.DescentPreparedSenderRoom
import OAI.Hierarchy.DescentResetPrefixRoom
import OAI.Hierarchy.DescentPhysicalResetActors

namespace OAI
/-! # Numeric bounds of the original operands at the beginning of a reset's peer scans -/
namespace Hierarchy.DescentContactSenderDate.Layout
open DescentSIMDLookup DescentPackedColony DescentPacking.PackedMatch.Local.Stage ProtocolRAM
variable {D L cap n r Ht b w low high H G M : ℕ} {u : Prior D L cap n r}
theorem prior_fits_before {nextHeight nextBits : ℕ}
    (safe : (⟨low,H,G,M⟩:Layout D L cap n r Ht b).PriorFits u w) (le : low ≤ high) :
    (⟨high,H,G,M⟩:Layout D L cap n r nextHeight nextBits).PriorFits u w :=
  ⟨fun j=>ProtocolRAMGeneratedWrite.fits_mono _ le (safe.board j),
   fun x j=>Chooser.accessible_before _ _ (safe.route x j) le,
   ProtocolRAMGeneratedWrite.fits_mono _ le safe.host,ProtocolRAMGeneratedWrite.fits_mono _ le safe.ones⟩
end Hierarchy.DescentContactSenderDate.Layout

namespace Hierarchy.DescentDatedAddressBook.CandidateFront.EarlierBanks
open DescentSIMDLookup DescentPackedColony DescentPacking.PackedMatch.Local.Stage DescentContactSenderDate
open DescentFallbackPeriod DescentFallbackPeriod.Projected DescentSixParty.Chronology ProtocolRAM Computability.VPVNP.BurstRAM
noncomputable section
variable {D cap n r H G M w : ℕ} (old : EarlierBanks D r cap n)

structure Bounds (H G M w cut : ℕ) : Prop where
  window : ∀j,(old.window j).Fits w cut
  tagged : ∀x,Accessible old.ports (old.window (.inl (1,x))) H G M w cut
  page : ∀s t,(old.roots s t).Fits w cut
  starts : old.actorStarts.Fits w cut
  scene : old.actorData.Fits w cut
  roster : old.oldRoster.Fits w cut
  positions : H*D ≤ old.oldRoster.size
  sender : (⟨cut,H,G,M⟩:Layout D (2^r) cap n r 0 0).PriorFits old.donor w
  donorRoster : old.donor.routes.roster.Fits w cut
  donorRows : H*D ≤ old.donor.routes.roster.size

theorem transfer_bounds {c cut : ℕ} (hc : cap=c) (safe : old.Bounds H G M w cut) :
    ((congrArg (fun z=>EarlierBanks D r z n) hc).mp old).Bounds H G M w cut := by
  subst c
  exact safe

variable {N K R c hm l t field Ht : ℕ}
  (rc : Receiver D cap N n r c H G K R M hm l t field Ht w) (book : RootBook n r D (2^r) cap field)
  (src : RootSources D (2^r) cap) (oldId oldHub : Bank) (directory : DescentResetNewActorDirectory.Layout) (scene : Bank)
local notation "rows" => H*chunks (2^c) M
local notation "window" => bankAt rc.stencil rc.tapped t D rc.signedEnd H (2^c) M

/-- Bounds for the actual root catalog, old signed rows and earlier sender board.
They hold before inspecting any selector or any contents of the input RAM. -/
theorem from_root_bounds (area : src.OperandRoom H (2^c) M w (rc.headerEnd book))
    (routes : ∀x,src.tagged x=window (.inl (1,x))) (wires : ∀x j,rows ≤ (src.signed x j).size)
    (idFit : oldId.Fits w rc.origin) (held : rc.preparedEnd book ≤ directory.endAddress)
    (sceneFit : scene.Fits w directory.endAddress) (top : directory.endAddress < 2^w) :
    (fromRoot rc book src oldId oldHub directory scene).Bounds H (2^c) M w directory.endAddress := by
  have headEnd : rc.headerEnd book ≤ rc.preparedEnd book:=Nat.le_add_right ..
  obtain ⟨header,repeatCut,repeatEnd⟩:=book.limits rc.projectionEnd H (2^c) M
  have pro : rc.projectionEnd ≤ directory.endAddress:=header.trans (repeatCut.trans (repeatEnd.trans (headEnd.trans held)))
  have port:=area.remoteShape 0
  have before:=headEnd.trans held
  have oldSender:=rc.sender_prior_fits book (rankTicket r n) src oldId area wires idFit (held.trans_lt top)
  have fromRoots : directory.flags.base ≤ directory.endAddress:=by
    change directory.first+directory.pitch ≤ directory.first+(4*directory.pitch+1+4*directory.sites)
    omega
  refine ⟨fun j=>Chooser.bank_before (rc.window_fits j (pro.trans_lt top)) pro,?_,
    fun s j=>(rc.privatePage_room book s j directory.endAddress held top).1,
    Chooser.bank_before (directory.fits top).1 fromRoots,sceneFit,Chooser.bank_before port.roster before,
    port.rosterRoom,?_,Chooser.bank_before port.roster before,port.rosterRoom⟩
  · intro x
    change Accessible src.peers (window (.inl (1,x))) H (2^c) M w directory.endAddress
    rw [←routes]
    exact Chooser.accessible_before _ _ (area.remoteShape x) before
  · exact DescentContactSenderDate.Layout.prior_fits_before (Ht:=Ht) (b:=field) oldSender held

end
end Hierarchy.DescentDatedAddressBook.CandidateFront.EarlierBanks

end OAI
