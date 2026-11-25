import OAI.Hierarchy.DescentPreparedSenderPrior
import OAI.Hierarchy.DescentRootOperandRoom
import OAI.Hierarchy.DescentPackedMatchChooserFrame

namespace OAI
/-! # Address bounds of the sender board carried out of the original reset roots -/
namespace Hierarchy.DescentFallbackPeriod.Projected.Receiver
open DescentSixParty.Chronology DescentResetHostSize DescentPackedColony DescentSIMDLookup
open DescentSharedLeafLookup DescentPacking.PackedMatch.Local.Stage DescentContactSenderDate
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable {D cap N n r c H G K R M h l t b Ht w : ℕ}
    (a : Receiver D cap N n r c H G K R M h l t b Ht w) (book : RootBook n r D (2^r) cap b)
    (root : Code r×Option (Fin (2^n))) (src : RootSources D (2^r) cap) (oldId : Bank)
local notation "groups" => 2^c
local notation "pg" => ((false,.inr root) : RootPage r (2^n))
local notation "ar" => RootTemplates.arena (a.headerEnd book) H groups M r n D
local notation "idx" => (rootIndex r (2^n) pg).val
local notation "hdr" => book.rankHeader a.projectionEnd H groups M pg
local notation "roof" => a.preparedEnd book
local notation "stage" => (Layout.mk roof H groups M : Layout D (2^r) cap n r Ht b)

theorem sender_prior_fits (area : src.OperandRoom H groups M w (a.headerEnd book))
    (rows : ∀lo j,H*chunks groups M ≤ (src.signed lo j).size)
    (idFit : oldId.Fits w a.origin) (top : roof < 2^w) :
    (stage).PriorFits (src.senderPrior H n r oldId hdr) w := by
  have low : a.headerEnd book ≤ roof:=Nat.le_add_right ..
  have cuts:=book.limits a.projectionEnd H groups M
  have head : a.origin ≤ a.headerEnd book:=a.origin_le_projection.trans (cuts.1.trans (cuts.2.1.trans cuts.2.2))
  have first : (ar).first (idx+1) ≤ roof:=Nat.add_le_add_left
    (Nat.mul_le_mul_left _ (rootIndex r (2^n) pg).isLt) _
  have tail_ : (ar).output idx ≤ (ar).first (idx+1):=by
    rw [←RootArena.end_row]
    exact Nat.le_add_right ..
  have bound : (ar).middle idx ≤ roof:=(show (ar).middle idx ≤ (ar).output idx from Nat.le_add_right ..).trans
    (tail_.trans first)
  have real:=a.rank_readable_of_top book false root (bound.trans_lt top)
  have banks (bank : Bank) (member : bank∈[(hdr).ranks,(hdr).start,(hdr).cut,(hdr).broadcast]) :
      bank.Fits w roof:=Chooser.bank_before (real.fit bank member) bound
  have access:=Chooser.accessible_before src.peers (src.tagged 0) (area.remoteShape 0) low
  refine ⟨?_,?_,⟨Chooser.bank_before idFit (head.trans low),trivial⟩,?_⟩
  · intro i
    obtain ⟨part,rfl⟩:=finSumFinEquiv.surjective i
    cases part with
    | inl j=>
      have fits := ProtocolRAMGeneratedWrite.fits_mono _ low (src.matrix_fit area j)
      simp only [RootSources.senderPrior, Equiv.symm_apply_apply, Sum.elim_inl]
      unfold RootSources.matrixRow at fits
      generalize DescentRotorWindowArchive.ix.symm j = u at fits ⊢
      rcases u with (((i|⟨j,i⟩)|⟨i,j⟩)|(⟨i,j⟩|⟨p,j,f⟩)) <;> exact fits
    | inr j=>
      simp only [RootSources.senderPrior,Equiv.symm_apply_apply,Sum.elim_inr]
      exact ⟨banks _ (by simp),⟨banks _ (by simp),trivial⟩,banks _ (by simp),
        ⟨banks _ (by simp),trivial⟩,trivial⟩
  · intro lo j
    exact {access with source:=Chooser.bank_before (area.ports lo j) low,srcRoom:=rows lo j}
  · exact ⟨banks _ (by simp),⟨banks _ (by simp),trivial⟩,trivial⟩

end
end Hierarchy.DescentFallbackPeriod.Projected.Receiver

end OAI
