import OAI.Hierarchy.DescentTerminalCalibratedShape
import OAI.Hierarchy.DescentNamedShellAddress
import OAI.Hierarchy.DescentTerminalEarnedTables
import OAI.Hierarchy.DescentTerminalEarnedLiteralRoom
import OAI.Hierarchy.DescentTerminalEarnedRates
import OAI.Hierarchy.DescentTerminalFieldSum

namespace OAI
/-! # Uniform address rates of the physically placed terminal on the original purchased shell -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost DescentMixedRouter DescentResetInvoice
open DescentTerminalGraphVolume DescentDatedAddressBook Catalyst ThreeFlat.Routing Filter
noncomputable section
set_option quotPrecheck false
open DescentTerminalCompiledPrefix DescentTerminalPreflightSpace DescentTerminalLocalPortBook ProtocolRAM
open AddressPlan
variable {F : Type} [Field F] (G : PoweredGadget F) (t f g reset τ B n depth C : ℕ)

local notation "src_" h:arg => ShellSource F h
local notation "age_" h:arg => Nat.log 2 h/(2*B)
local notation "st_" h:arg x:arg => stageNumbers G t (age_ h) f g reset (ShellSource.sites x) (tail τ (age_ h))
local notation "kb_" h:arg => groupBits t (age_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "bw_" h:arg x:arg => NativeBranch.binLimit (k:=kb_ h) (st_ h x)
local notation "j_" h:arg x:arg => Nat.clog 2 (NativeBranch.localLimit G (st_ h x))
local notation "unit_" h:arg => G.b^(t*(age_ h))*G.b
local notation "q_" h:arg x:arg => 2^(j_ h x)*(unit_ h)
local notation "p_" h:arg x:arg => (bw_ h x)*(h/(16*((q_ h x)*(bw_ h x))))
local notation "pins_" x:arg => Fintype.card (Port (ShellSource.ports x) (ShellSource.X x).width)
local notation "normal_" h:arg x:arg => terminalWireBudget (ShellSource.X x) G (st_ h x) (p_ h x) n depth C f g
local notation "pool_" h:arg x:arg => terminalPool (ShellSource.X x) G (st_ h x) (p_ h x) (q_ h x) (bw_ h x) n depth C f g
local notation "raw_" h:arg x:arg => terminalRawRows (ShellSource.X x) G (st_ h x) (p_ h x) (q_ h x) n depth C f g
local notation "dim_" h:arg x:arg => (st_ h x).groupWidth (kb_ h) (tail τ (age_ h)) 0+kb_ h
local notation "pub_" h:arg x:arg => (pins_ x)*2^((j_ h x)+((dim_ h x)-2*(j_ h x)))


/-- Locations and incoming banks can vary across the calendar while the literal domains are fixed. -/
structure TerminalPlacement where
  spec : Spec
  template : Shape
  other : AddressPlan.Input
  begin_ : ℕ
  rom : ℕ
  codes : ℕ
  front : ℕ
  peer : Bank
  wings : Fin spec.scalar.blocks→Fin (2*spec.cap)→Bank
  totals : Bank
  modulo : Bank
  homes : Bank
  boundary : ℕ

variable (op : RotorSpec) (drift : ℕ) {height : ℕ} (x : ShellSource F height) (L : TerminalPlacement)
local notation "st" => st_ height x
local notation "k" => kb_ height
local notation "W" => bw_ height x
local notation "q" => q_ height x
local notation "p" => p_ height x
local notation "bins" => calibratedBins x.X G t (age_ height) f g reset x.sites τ height n depth C
local notation "piece" => height/(16*(q*W))
local notation "rows" => pool_ height x
local notation "V" => (st).groupCount (st).length*2^k
local notation "A" => NativeBranch.localLimit G st
local notation "fmt" => earnedFormat G op st q p drift
local notation "totalBits" => max 1 (V*actualSpan G st op q p drift)
local notation "routes" => RouteSources.Tables.mk 4 V (V*A) A (Book.tokenBits (V*A)) W q bins
private theorem positive_sites : 0<x.sites:=by have:=x.opened;omega

def earnedShell := calibrated_shell x.X G t (age_ height) f g reset x.sites τ height n depth C
  L.template rows (positive_sites x)
local notation "cfg" => earnedShell G t f g reset τ B n depth C x L

def earnedInput := L.spec.reachedInput L.begin_ L.rom q piece W bins L.codes L.front L.peer L.wings
  L.totals L.modulo L.homes L.boundary cfg fmt L.other routes V totalBits
local notation "inputs" => earnedInput G t f g reset τ B n depth C op drift x L

theorem shell_word_fields {bound : ℕ}
    (sized : (st).hostSize (st).length+rows+(pub_ height x)+((raw_ height x)+rows)≤bound) :
    (cfg).sites≤bound ∧ (cfg).terminal.pool≤bound ∧ (cfg).terminal.plane.rawRows≤bound ∧
      (cfg).terminal.plane.publicRows≤bound ∧ (cfg).terminal.plane.headerRows≤bound :=by
  change (st).hostSize (st).length≤bound ∧ rows≤bound ∧ (raw_ height x)≤bound ∧
    (pub_ height x)≤bound ∧ rows≤bound
  omega

theorem earned_counts_at
    (tables : EarnedTables G op drift st k (j_ height x) ((dim_ height x)-2*(j_ height x)) W q p height) :
    EarnedCounts height cfg inputs :=by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_,tables.exterior⟩
  intro j
  exact L.spec.reached_need L.begin_ L.rom q piece W bins L.codes L.front L.peer L.wings
    L.totals L.modulo L.homes L.boundary cfg fmt L.other V A totalBits rfl
    tables.book tables.keys tables.headers j

/-- The calendar only needs a source on attained heights, including when the small heights have no eligible host. -/
def EarnedAt (h : ℕ) (cfg₀ : Shape) (input₀ : AddressPlan.Input) : Prop :=
  ∃x₀ : ShellSource F h,∃l : TerminalPlacement,
    cfg₀=earnedShell G t f g reset τ B n depth C x₀ l ∧
    input₀=earnedInput G t f g reset τ B n depth C op drift x₀ l

theorem earned_calendar_rates (cfgs : ℕ→Shape) (ins : ℕ→AddressPlan.Input)
    (realized : ∀ᶠ h:ℕ in atTop,EarnedAt G t f g reset τ B n depth C op drift h (cfgs h) (ins h))
    (branch : G.b≤2^(capRate G t g)) (big : 20≤B) (reserve : 2*localSocketRate G t g≤τ)
    (packing : 2*(localSocketRate G t g+(τ+groupRate G t f g reset+4))+Nat.clog 2 G.b*(t+1)≤B)
    (router : 2*((τ+groupRate G t f g reset+4)+(localSocketRate G t g+Nat.clog 2 G.b*(t+1))+2)≤B)
    (cohorts : 2*(τ+groupRate G t f g reset+(6*(terminalDegree G t f g reset+1)+19))≤B)
    (books : 2*bookRate G t f g reset τ≤B) : CofinalRates cfgs ins :=by
  obtain ⟨R,spaces⟩:=shell_address G t f g reset τ B n depth C
  have all_:=earned_tables G op drift t f g reset τ B branch big reserve packing router cohorts books
  apply earned_rates
  · filter_upwards [all_,realized] with h tables found
    obtain ⟨x₀,l,atCfg,atInput⟩:=found
    rw [atCfg,atInput]
    exact earned_counts_at G t f g reset τ B n depth C op drift x₀ l (tables x₀.sites)
  all_goals
    refine ⟨R,?_⟩
    filter_upwards [spaces,realized] with h volumes found
    obtain ⟨x₀,l,atCfg,atInput⟩:=found
    intro _
    rw [atCfg]
    have volume:=volumes x₀
    first
    | change (st_ h x₀).hostSize (st_ h x₀).length≤2^(R*h);omega
    | change (pool_ h x₀)≤2^(R*h);omega
    | change (pub_ h x₀)≤2^(R*h);omega
    | change (raw_ h x₀)≤2^(R*h);omega

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
