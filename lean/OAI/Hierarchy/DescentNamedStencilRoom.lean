import OAI.Hierarchy.DescentStencilNativeRoom
import OAI.Hierarchy.DescentNamedResetRootPagesFit

namespace OAI
/-! # The early reset estimator and rotation fit in the complete native date -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentGLControlCode DescentGLPacked.BankImage DescentPlainTerminal.Suffix DescentSixParty.Chronology ProtocolRAM
open private middle_le_metadata from OAI.Hierarchy.DescentNamedResetRootPagesFit
noncomputable section
set_option quotPrecheck false
private theorem stencil_before_stop (v : ResetMiddle) (base : ℕ) :
    v.afterStencil base≤v.stop base :=by
  unfold ResetMiddle.stop
  rw [show v.rootHeader (v.afterProjection base)=v.afterProjection base+v.rootHeader 0 from root_header_affine ..]
  unfold ResetMiddle.afterProjection DescentFallbackPeriod.Projected.start ResetMiddle.afterSigned
    ResetMiddle.signedCharts SignedFields.stop SignedFields.joinStop ResetMiddle.retileEnd
    SignedFields.Retile.stop DescentSIMDLookup.Subwords.destination
  simp only [Dated.extent, RootTemplates.privateEnd, RootArena.first, RootArena.stride, Nat.add_assoc]
  exact Nat.le_add_right _ _

variable (a : PhysicalReset) (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y w : ℕ)
local notation "start" => a.stageStart floor
local notation "P" => a.stencilPhase sh start count hub g Y

theorem stencil_end_before_full :
    (P).endAddress≤a.fullEnd floor :=by
  rw [a.stencil_end sh start count hub g Y]
  exact (stencil_before_stop a.successor.middle (a.rebased start)).trans
    (middle_le_metadata a.successor (a.rebased start))

theorem stencil_room_of_end
    (cut : (P).S.c≤a.high+a.re+a.e) (endRoom : a.fullEnd floor<2^w)
    (operands : StencilBook.Geometry (P).S (P).X (P).base (P).bank w)
    (short : (P).S.M*max ((P).S.n*Stencil.count (P).S.r ((P).S.degree+(P).S.degree))
      ((P).S.t*2^(P).S.r)≤w/2) (word : (P).S.n*(P).S.M≤w) : (P).Room w :=
  a.stencil_native_room sh start count hub g Y w cut
    ((a.stencil_end_before_full sh floor count hub g Y).trans_lt endRoom) operands short word

end
noncomputable section Epoch
open DescentCompiler DescentWalshPrecision
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
  (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
  (e previous M nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
  (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor

theorem named_chip_cut : (a).successor.middle.stencil.c≤(a).high+(a).re+(a).e :=by
  change S.groupWidth k tail age≤((S.groupWidth k tail age+k)-_)+(_-k-e)+e
  omega
end Epoch

end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
