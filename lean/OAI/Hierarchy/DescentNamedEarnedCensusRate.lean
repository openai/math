import OAI.Hierarchy.DescentEarnedCensusPrefix
import OAI.Hierarchy.DescentNamedEarnedLastRate
import OAI.Hierarchy.DescentTerminalPaidCensusRoom

namespace OAI
/-! # A single word width for the complete post-date readout and final verdict -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost DescentMixedRouter DescentResetInvoice
open DescentTerminalGraphVolume DescentDatedAddressBook Catalyst ThreeFlat.Routing Filter
open DescentTerminalCompiledPrefix DescentTerminalPreflightSpace DescentTerminalLocalPortBook ProtocolRAM
open AddressPlan DescentTerminalVertexFields DescentTerminalLast
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F)
  (t f g reset τ B n depth C : ℕ) (op : RotorSpec) (drift : ℕ)
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "S_" h:arg x:arg => stageNumbers G t (J_ h) f g reset (ShellSource.sites x) (tail τ (J_ h))
local notation "k_" h:arg => groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "q_" h:arg x:arg => 2^Nat.clog 2 (NativeBranch.localLimit G (S_ h x))*(G.b^(t*(J_ h))*G.b)
local notation "W_" h:arg x:arg => NativeBranch.binLimit (k:=k_ h) (S_ h x)
local notation "piece_" h:arg x:arg => h/(16*((q_ h x)*(W_ h x)))
local notation "fmt_" h:arg x:arg => earnedFormat G op (S_ h x) (q_ h x) ((W_ h x)*(piece_ h x)) drift
local notation "cfg_" x:arg L:arg => earnedShell G t f g reset τ B n depth C x L
local notation "I_" x:arg L:arg => earnedInput G t f g reset τ B n depth C op drift x L
local notation "start_" x:arg z:arg => (earnedPreflight G t f g reset τ B n depth C op drift x).maskBase
  (censusScanBase G t f g reset τ B n depth C op drift x z)

/-- The original scalar purchases on the chosen calendar. -/
structure CensusCut : Prop where
  large : 20≤B
  reserve : 2*localSocketRate G t g≤τ
  packing : 2*(localSocketRate G t g+(τ+groupRate G t f g reset+4))+Nat.clog 2 G.b*(t+1)≤B
  router : 2*((τ+groupRate G t f g reset+4)+(localSocketRate G t g+Nat.clog 2 G.b*(t+1))+2)≤B
  cohorts : 2*(τ+groupRate G t f g reset+(6*(terminalDegree G t f g reset+1)+19))≤B
  books : 2*bookRate G t f g reset τ≤B
  preflight : 2*(6*PreflightCalendar.fieldExponent G t f g reset τ+11)≤B

/-- The complete charged census for the actual publicly generated readout.
The earlier public identity can use the actual raw row count and its actual code alphabet. -/
def CensusWordAt (headRate rate h : ℕ) : Prop :=
  ∀(x:ShellSource F h) (z:CensusReplay (k_ h)) (L:TerminalPlacement)
    (channels:MaskAllocation.Channels (S_ h x).radix),
    IssuedPreflightAt G t f g reset τ B n depth C drift x→z.ReadyAt G t f g reset τ B headRate x→
    let cfg:=cfg_ x L
    let origin:=start_ x z
    let high:=last (fmt_ h x) cfg (I_ x L) channels origin
    high≤2^(rate*h) ∧ ∀(bins codes raw publicRows w:ℕ),
      DescentTerminalPublicIdentity.total bins (W_ h x) (q_ h x) (piece_ h x) codes raw publicRows≤origin→
      (2*rate+7)*h≤w→
      trailingStop (trailingCut high cfg.terminal.rows) raw cfg.terminal.pool
        (codes*2^((q_ h x)*((W_ h x)*(piece_ h x))))+1<2^w

def CensusWord (headRate rate : ℕ) : Prop :=
  ∀ᶠ h:ℕ in atTop,CensusWordAt G t f g reset τ B n depth C op drift headRate rate h

set_option maxHeartbeats 900000 in
theorem earned_census_rate (headRate:ℕ) (branch:G.b≤2^(capRate G t g)) :
    ∃rate:ℕ,∀τ B,CensusCut G t f g reset τ B→
      CensusWord G t f g reset τ B n depth C op drift headRate rate :=by
  obtain ⟨A,scan⟩:=earned_scan_uniform G t f g reset n depth C op drift headRate branch
  obtain ⟨M,mask⟩:=earned_mask_uniform G t f g reset n depth C op drift branch
  obtain ⟨T,terminal⟩:=earned_last_uniform G t f g reset n depth C op drift branch
  let P:=max A (max M T)
  refine ⟨P+2,?_⟩
  intro τ B bill
  obtain ⟨big,reserve,packing,router,cohorts,books,preflight⟩:=bill
  filter_upwards [scan τ B big preflight,mask τ B (by omega) preflight,
    terminal τ B big reserve packing router cohorts books,eventually_ge_atTop 1] with h early census read hp
  intro x z L R issued live
  dsimp only
  let U:=censusScanBase G t f g reset τ B n depth C op drift x z
  let age := Nat.log 2 h/(2*B)
  let stage := stageNumbers G t age f g reset x.sites (tail τ age)
  let groupBits' := groupBits t age (hostRate t reset) (capRate G t g) (cutRate t f g)
  let W := NativeBranch.binLimit (k:=groupBits') stage
  let q := 2^Nat.clog 2 (NativeBranch.localLimit G stage)*(G.b^(t*age)*G.b)
  let piece := h/(16*(q*W))
  let V := earnedFormat G op stage q (W*piece) drift
  let origin := (earnedPreflight G t f g reset τ B n depth C op drift x).maskBase U
  let cfg := earnedShell G t f g reset τ B n depth C x L
  let I := earnedInput G t f g reset τ B n depth C op drift x L
  let E:=2^(P*h)
  have bounded {k:ℕ} (rel:k≤P) : 2^(k*h)≤E:=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ rel)
  have prefixPaid : U≤E:=(early x z issued live).trans (bounded (Nat.le_max_left ..))
  have maskPaid : origin≤U+2^(M*h):=census x issued U
  have maskWords:=bounded ((Nat.le_max_left M T).trans (Nat.le_max_right A _))
  have tailPaid : last V cfg I R origin≤origin+2^(T*h):=read x L R origin
  have tailWords:=bounded ((Nat.le_max_right M T).trans (Nat.le_max_right A _))
  have shift : 4*E≤2^((P+2)*h):=by
    change 2^2*2^(P*h)≤_
    rw [←Nat.pow_add,Nat.add_mul]
    apply Nat.pow_le_pow_right (by decide)
    have:=Nat.mul_le_mul_left 2 hp
    omega
  have finalRoom : last V cfg I R origin≤2^((P+2)*h):=
    (show last V cfg I R origin≤4*E by omega).trans shift
  refine ⟨finalRoom,?_⟩
  intro bins codes raw publicRows w purchased word
  exact census_word_of_readout V cfg I R origin bins W q piece
    codes raw publicRows h (P+2) w purchased finalRoom hp word

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
