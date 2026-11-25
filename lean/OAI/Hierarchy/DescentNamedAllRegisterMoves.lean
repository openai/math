import OAI.Hierarchy.DescentNamedRegisterTimeline
import OAI.Hierarchy.DescentNamedOrdinaryMachine
import OAI.Hierarchy.DescentNamedOrdinaryPorts

namespace OAI
/-! # One actual native instruction stream and successor register bank on every ballot -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Computability.VPVNP.BurstRAM PrivateRAM
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
local notation "trace" => SeedNamed.issued X G S ordinary reset branch positive room shorten
variable (w : ℕ)

local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
variable {n₀ δ : ℕ} (b : RegisterTimeline.Menu n₀ δ) (initial : RegisterTimeline.Position)
local notation "cursor" => RegisterTimeline.calendar (w:=w) traces b initial
local notation "issue" => RegisterTimeline.issued (w:=w) traces b
local notation "prog" => RegisterTimeline.instruction (w:=w) traces b initial

variable (gain : b.gain=g) (grain : b.p=p) (arity : b.f=f)
local notation "reg" i:arg a:arg => VenueProgram.Registered.atAge G S b.op b.gain k i b.p b.tail b.f b.drift b.degreeLimit
  b.payload (b.seats i) (a:Position).floor (a:Position).ports b.ordinary
local notation "room₀" i:arg a:arg => DatePorts.MachineFits (a:Position).ports G S b.op b.gain k i b.p b.tail b.f b.drift
  b.degreeLimit b.payload (b.seats i) (a:Position).floor b.ordinary
local notation "cpu" i:arg a:arg pos:arg ok:arg => DatePorts.commonOrdinary (a:Position).ports G S b.op b.gain k i b.p b.tail b.f
  b.drift b.degreeLimit b.payload (b.seats i) (a:Position).floor b.ordinary w (b.profile i) b.header pos ok

attribute [local irreducible] SeedNamed.issued Origin.source

include gain grain arity in
theorem ordinary_registered_move (i : ℕ) (a : Position) (e : RunTrace.Events traces i)
    (move : Move w) (ordinaryAt : e.2.isReset=false) (hit : issue i e a move) :
    ∃(pos : 0<k) (fits : room₀ i a),move=⟨cpu i a pos fits,(reg i a).next G,(reg i a).roof G⟩ :=by
  subst g
  subst p
  subst f
  obtain ⟨walk,event⟩:=e
  cases event with
  | reset before R after cut=>cases ordinaryAt
  | ordinary before ticket after cut=>
    obtain ⟨pos,roomDate,rfl⟩:=hit
    let br := SeedNamed.issued X G S ordinary reset branch positive room shorten walk
    dsimp only [traceAt] at before after cut
    obtain ⟨ok,code⟩:=Branch.registered_machine X G S br ticket before after cut b.op b.tail b.drift b.degreeLimit
      b.payload (b.seats i) (a:Position).floor (a:Position).ports b.ordinary w (b.profile i) b.header pos roomDate
    obtain ⟨ports,_,roof⟩:=Branch.ordinary_ports_at X G S br ticket before after cut b.op b.tail b.drift b.degreeLimit
      b.payload (b.seats i) (a:Position).floor (a:Position).ports b.ordinary roomDate.paths
    exact ⟨pos,ok,by rw [code,ports,roof]⟩

include gain grain arity in
theorem ordinary_registers_shared (i : ℕ) (a : Position) (l r : RunTrace.Events traces i)
    (x y : Move w) (left : l.2.isReset=false) (right : r.2.isReset=false)
    (hx : issue i l a x) (hy : issue i r a y) : x=y :=by
  obtain ⟨_,_,rfl⟩:=ordinary_registered_move X G S ordinary reset branch positive room shorten w b gain grain arity i a l x left hx
  obtain ⟨_,_,rfl⟩:=ordinary_registered_move X G S ordinary reset branch positive room shorten w b gain grain arity i a r y right hy
  rfl

include gain grain arity in
theorem all_registered_moves (i : ℕ) (a : Position) (l r : RunTrace.Events traces i)
    (x y : Move w) (hx : issue i l a x) (hy : issue i r a y) : x=y :=
  RegisterTimeline.same_kind traces b i a
    (fun u v=>event_kind X G S ordinary reset branch positive room shorten i u.1 v.1 u.2 v.2)
    (ordinary_registers_shared X G S ordinary reset branch positive room shorten w b gain grain arity i a) l r x y hx hy

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
