import OAI.Hierarchy.DescentNamedEarnedPreflightRates
import OAI.Hierarchy.DescentChosenExteriorHeadWidths

namespace OAI
/-! # A reached terminal itinerary from the original total selector route -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost DescentDatedSeedStartup
open DescentMixedRouter DescentResetInvoice DescentTerminalEpochChart DescentTerminalEpochDecoder
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (t f g rate τ β h n degree C : ℕ)
    (x : ShellSource F h) {cut frozen : ℕ}
local notation "J" => Nat.log 2 h/(2*β)
local notation "S" => stageNumbers G t J f g rate x.sites (tail τ J)
local notation "k" => groupBits t J (hostRate t rate) (capRate G t g) (cutRate t f g)
local notation "p" => headGrain G S k h

theorem normalized_issued_preflight (ordinary : OrdinaryRates G S k cut)
    (reset : ResetRates G S k (atRound t) n degree C f g cut frozen)
    (branch:G.b≤2^(capRate G t g)) (positive:0<p) (shorten:reentryRate degree C*(1-(2-G.rate)/4)^t≤1/2) :
    IssuedPreflightAt G t f g rate τ β n degree C (max 1 (max reset.bitsR (C*reset.bitsR))) x := by
  let s:=(S).firstWidth G.b p
  have fit:s<2^s:=Nat.lt_two_pow_self
  let cert:=normalized_epochs_issued_joint x.X G S ordinary reset branch positive x.opened shorten
  let route:=normalizedRoute x.X G S ordinary reset branch positive x.opened shorten s fit
  let ballot:=route.follow (fun _=>false)
  refine ⟨positive,by positivity,by positivity,ordinary.radix,cert.choose,ballot,?_⟩
  exact ⟨issued x.X G S ordinary reset branch positive x.opened shorten ballot⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
