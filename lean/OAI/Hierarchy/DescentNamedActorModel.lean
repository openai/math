import OAI.Hierarchy.DescentResetCanvasInputBanks
import OAI.Hierarchy.DescentNamedIngressCode
import OAI.Hierarchy.DescentCalendarResetIngress
import OAI.Hierarchy.DescentNamedActorDirectory

namespace OAI
/-! # The calendar and the named reset read the same packed predecessor tokens -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
  (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
  (e previous M nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
  (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cc" => S.groupWidth k tail age
local notation "nbits" => k+S.localWalshBits p (cc+k) f (quota S.rounds)+2
local notation "tbits" => 2*k+n+2

/-- All legal old signed sockets address the same retained page in the two
presentations of this one physical program. -/
theorem named_actor_model (L : DescentResetCanvasIngress.Layout) (rows : L=(a).ingress)
    (D₀ : ℕ) (actual : D₀=venue.degree) :
    fromCalendar S k tail age G.b p f D₀ payload e nbits tbits cal (L.tokenAt floor) io.roster (a).successor=a := by
  subst L
  subst D₀
  calc
    _ = atIngress (a).ingress floor a rfl rfl := by
      change {(a) with previousToken:=fun j=>(a).ingress.tokenAt floor j.1.val j.2.val} =
        {(a) with previousToken:=fun j=>(a).ingress.tokens floor (j.1,j.2)}
      have tokenEq : (fun j : Fin (2^(a).k) × Fin (a).c => (a).ingress.tokenAt floor j.1.val j.2.val) =
          (fun j => (a).ingress.tokens floor (j.1, j.2)) := by
        funext j
        exact (a).ingress.tokenAt_slot floor j.1 j.2
      exact congrArg (fun tokens : Fin (2^(a).k) × Fin (a).c → ProtocolRAM.Bank =>
        ({(a) with previousToken := tokens} : PhysicalReset)) tokenEq
    _ = _ := (named_ingress_bound floor G S board k tail age p f g drift degree payload e previous M nextM C packet
      oldLanes primitiveLanes printedBits venue io).symm

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
