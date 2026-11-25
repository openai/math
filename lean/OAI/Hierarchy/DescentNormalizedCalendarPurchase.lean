import OAI.Hierarchy.DescentNormalizedStagePrice
import OAI.Hierarchy.DescentProfiledUniformRates

namespace OAI
/-! One fixed word-to-height ratio buys the actual whole dated calendar on
all normalized original inputs. The ratio is chosen before the epoch tail. -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
open DescentCompiler.TerminalScale DescentDatedAddressBook PhysicalReset RegisteredReset DescentHostDegree
open DescentPackedEpochShelves DescentPackedProfileTape DescentPackedProfileInstall DescentWideSeedFlags Filter
open scoped BigOperators
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ}
  (board : NonlinearExpanders.Graph n d) (op : RotorSpec) (t f g resetCost cut drift bound : ℕ)
set_option hygiene false
local notation "J_" h:arg B:arg => Nat.log 2 h/(2*B)

def NormalizedRuns (branch : G.b ≤ 2^(capRate G t g)) (head ratio τ B h : ℕ) : Prop :=
  ∀M,2^h ≤ M → M ≤ (2^h)^2 → (∃a,M=2^a) →
  let j:=J_ h B
  let tb:=tail τ j
  let k:=groupBits t j (hostRate t resetCost) (capRate G t g) (cutRate t f g)
  let S:=stageNumbers G t j f g resetCost M tb
  let p:=headGrain G S k h
  let w:=ratio*h
  ∀{cp pins : ℕ} (X : Approximation F cp pins) (ordinary : OrdinaryRates G S k cut)
    (reset : ResetRates G S k (atRound t) n d op.C f g cut tb),reset.board=board →
    ∀(positive : 0 < p) (room : 10*(X.size+1) ≤ M)
      (shorten : reentryRate d op.C*(1-(2-G.rate)/4)^t ≤ 1/2)
      (fit : S.firstWidth G.b p < 2^w) (H degree wire hist : ℕ),M ≤ H → H ≤ hostRows M → degree ≤ bound →
      let steps:=(normalizedPackedChart X G S ordinary reset branch positive room shorten w fit).layout
      let W:=NativeBranch.binLimit (k:=k) S
      let q:=headArity G S
      let bins:=terminalBinCount X G S p q W n d op.C f g+1
      let raw:=terminalRawRows X G S p q n d op.C f g
      let v:=originalSeedHead G op drift X steps S k tb h H degree wire hist bins raw
      let lo:=selectorBase X S.copies (v.width G) h steps.length
      let menu:=fromProfiles G S board op k tb p f g drift degree h lo (v.base G h-1) steps
      let traces:=traceAt X G S ordinary reset branch positive room shorten
      v.Ready G board op t f g drift h w head ∧
       (∑i∈Finset.range S.length,(instruction (w:=w) traces menu (v.position G op t f g drift h) i).tariff)*2^j ≤
         2*(M*(S.copies*p))

theorem normalized_calendar_purchase (saving : ℕ) (branch : G.b ≤ 2^(capRate G t g)) :
    ∃addr head : ℕ,∀ratio, t+1+max addr head+2 ≤ ratio →
      ∃minTail : ℕ,∀τ ≥ minTail,∃minBus : ℕ,∀B ≥ minBus,∀ᶠ h:ℕ in atTop,
        ProfiledRate.Covers G board op t f g resetCost τ drift bound B h addr ∧
        NormalizedRuns G board op t f g resetCost cut drift bound branch head ratio τ B h :=by
  obtain ⟨addr,addresses⟩:=ProfiledRate.uniform_addresses G board op t f g resetCost drift bound
  obtain ⟨head,seedThreshold,seeds⟩:=normalized_seed_entry G board op t f g resetCost drift n d op.C branch
  refine ⟨addr,head,?_⟩
  intro ratio enough
  let driftR:=drift+1
  obtain ⟨T,bills⟩:=calendar_with_word G board op t f g resetCost cut ratio drift driftR bound (quota t)
    addr head saving enough (addresses driftR (quota t))
  refine ⟨max T (max 1 (2*localSocketRate G t g)),?_⟩
  intro τ tailPaid
  have later : T ≤ τ:=(le_max_left ..).trans tailPaid
  have seedTail : max 1 (2*localSocketRate G t g) ≤ τ:=(le_max_right ..).trans tailPaid
  obtain ⟨Q,hardware⟩:=bills τ later
  refine ⟨max Q (seedThreshold τ),?_⟩
  intro B reserve
  filter_upwards [hardware B ((le_max_left ..).trans reserve),
    seeds τ B seedTail ((le_max_right ..).trans reserve),eventually_ge_atTop 1] with h hw source positiveH
  refine ⟨hw.1,?_⟩
  intro M low high dyadic j tb k S p w cp pins X ordinary reset chosen live room shorten fit H degree wire hist lower upper cap
  dsimp only
  have strict:head*h<w:=by
    have headBound:=le_max_right addr head
    have below : head < ratio:=by omega
    exact Nat.mul_lt_mul_of_pos_right below positiveH
  have seed:=source M low high dyadic X ordinary reset live room shorten w fit H degree wire hist lower upper strict
  have reserveDrift:drift+1 ≤ scale j driftR:= by
    unfold scale
    exact (Nat.le_mul_of_pos_right (drift+1) (Nat.succ_pos _)).trans Nat.lt_two_pow_self.le
  exact ⟨seed,normalized_stage_price G board op t f g resetCost drift bound τ B h M H degree wire hist cut w
    X ordinary reset branch live room shorten fit addr head ratio driftR hw.2.2.2.2 hw.1 seed chosen cap
    reserveDrift low high hw.2.2.2.1 le_rfl⟩

theorem normalized_calendar_at_ratio (saving : ℕ) (branch : G.b ≤ 2^(capRate G t g)) :
    ∃purchaseLeast head : ℕ,∀ratio ≥ purchaseLeast,
      ∃minTail : ℕ,∀τ ≥ minTail,∃minBus : ℕ,∀B ≥ minBus,∀ᶠ h:ℕ in atTop,
        NormalizedRuns G board op t f g resetCost cut drift bound branch head ratio τ B h :=by
  obtain ⟨addr,head,calendar⟩:=normalized_calendar_purchase G board op t f g resetCost cut drift bound saving branch
  refine ⟨t+1+max addr head+2,head,?_⟩
  intro ratio enough
  obtain ⟨T,work⟩:=calendar ratio enough
  refine ⟨T,?_⟩
  intro τ bought
  obtain ⟨Q,height⟩:=work τ bought
  exact ⟨Q,fun B funded=>(height B funded).mono fun _ receipt=>receipt.2⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
