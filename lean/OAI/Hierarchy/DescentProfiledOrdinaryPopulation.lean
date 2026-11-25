import OAI.Hierarchy.DescentIssuedRangeRoom
import OAI.Hierarchy.DescentNamedAllRegisterMoves
import OAI.Hierarchy.DescentRegisteredGeometry
import OAI.Hierarchy.DescentRegisteredProfileMenu
import OAI.Hierarchy.DescentRotorSpecOfRates

namespace OAI
/-! # Operand host capacity on each selected prefix of the profiled calendar -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline

open Computability.VPVNP.BurstRAM PrivateRAM DescentDatedAddressBook
noncomputable section
variable {F P : Type} [Field F] {G : PoweredGadget F} {S : DescentCompiler.AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C→RunTrace G q ε S k wire hist final bits d)
    {n degree : ℕ} (b : Menu n degree) (initial : Position)
local notation "steps" => issued (w:=w) traces b
local notation "cursor" => calendar (w:=w) traces b initial
variable (c : C)
local notation "t" => traces c

private theorem noninitialPopulationOnTrace
    (lastMove : ∀j (e : RunTrace.Events traces j),∃ mv : Move w,
      issued (w:=w) traces b j e (calendar (w:=w) traces b initial j) mv ∧
      calendar (w:=w) traces b initial (j+1) = mv.next)
    (numberOrdinary :
      ∀ {U : MarkedWorld F d P bits} {age z D z' D' : ℕ} {rate : ℝ}
        {src : Reached U G q ε S k age z D wire hist} {nneg : 0 ≤ ε}
        {T : StageInput U G rate ε} {ballot : (T.result nneg).Choice}
        {norm : Normalize ((T.result nneg).state ballot)}
        {dst : Reached norm.result G q ε S k (age+1) z' D' wire hist}
        (ticket : OrdinaryLink src nneg T ballot norm dst)
        (prev : Path (t).first src) (rest : Path dst (t).last),
        (prev.ordinary ticket).append rest = (t).path →
        ∀ at_ : Position, Fintype.card dst.V ≤
          (DatePorts.ordinaryPorts at_.ports ticket b.op b.gain b.tail b.p b.f b.drift b.degreeLimit
            b.payload (b.seats age) at_.floor b.ordinary).operandHosts)
    {U : MarkedWorld F d P bits} {i z D : ℕ} {r : Reached U G q ε S k i z D wire hist}
    (before : Path (t).first r) (remaining : Path r (t).last)
    (joined : before.append remaining = (t).path) (positiveAge : 0 < i) :
    Fintype.card r.V ≤ (cursor i).ports.operandHosts := by
  cases before with
  | here => exact (Nat.lt_irrefl 0 positiveAge).elim
  | @ordinary _ age _ _ _ _ src prev _ he T ballot norm dst ticket =>
    obtain ⟨mv,posted,position⟩ := lastMove age ⟨c,.ordinary prev ticket remaining joined⟩
    rw [position]
    obtain ⟨_,_,rfl⟩ := posted
    exact numberOrdinary ticket prev remaining joined _
  | @reset _ age _ _ _ _ _ _ _ _ _ src prev ctl closed =>
    obtain ⟨mv,posted,position⟩ := lastMove age ⟨c,.reset prev closed remaining joined⟩
    rw [position]
    obtain ⟨_,_,rfl⟩ := posted
    exact closed.next.valid.host
end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open RegisterTimeline Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
    {k cut tail n h C f g p : ℕ} (ordinary : OrdinaryRates G S k cut)
    (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
    (branch : G.b≤2^S.capGain) (positive : 0<p) (room : 10*(X.size+1)≤S.initialSites)
    (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds≤1/2)
local notation "s" => S.firstWidth G.b p
local notation "traces" => traceAt X G S ordinary reset branch positive room shorten
local notation "trace" => SeedNamed.issued X G S ordinary reset branch positive room shorten
local notation "run" => (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose
local notation "wire" => S.epochPower^S.priceExponent
local notation "price" => (1/((s:ℝ)*(wire:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "pins" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port nP X.width)))
variable (w : ℕ) (fit : S.firstWidth G.b p < 2^w) (dateTail drift degree payload lo header : ℕ) (initial : Position)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit
local notation "op" => RotorSpec.ofRates reset
local notation "menu" => fromProfiles G S reset.board op k dateTail p f g drift degree payload lo header (ch).layout
local notation "cursor" => calendar (w:=w) traces menu initial
local notation "step" => RegisterTimeline.issued (w:=w) traces menu
attribute [local irreducible] SeedNamed.issued Origin.source

set_option maxHeartbeats 1000000 in
theorem profiled_prefix_population (pre : Geometry G S menu k w 0 initial)
    (placed : ∀i (e : RunTrace.Events traces i),fitsAt traces menu initial (w:=w) i e)
    (walk : (Epochs.finish G _ _ run).Choice)
    (originSize : Fintype.card (trace walk).origin.source.V≤ initial.ports.operandHosts)
    {U : MarkedWorld F 0 pins (fun _=>s*1)} {i z D : ℕ} {prior : Reached U G price fee S k i z D wire s}
    (before : Path (trace walk).origin.source prior) (remaining : Path prior (trace walk).target)
    (joined : before.append remaining=(trace walk).path) :
    Fintype.card prior.V≤(cursor i).ports.operandHosts :=by
  have fixed (j : ℕ) (a b : RunTrace.Events traces j) (x y : Move w)
      (hx : step j a (cursor j) x) (hy : step j b (cursor j) y) : x=y :=
    all_registered_moves X G S ordinary reset branch positive room shorten w menu rfl rfl rfl
      j (cursor j) a b x y hx hy
  exact (issued_prefix_operand_geometry (w:=w) X G S ordinary reset branch positive room shorten
    reset.board op dateTail drift degree payload header (menu).seats (menu).profile (menu).ordinary initial walk fixed
    pre.room (fun j e _=>placed j e (geometry_on_event traces menu initial fixed (fun c=>(trace c).calendar)
      (fun c=>(trace c).kinds) pre placed e.1 j e.2)) originSize pre.format.width (U:=U) (r:=prior) before remaining joined).1

set_option maxHeartbeats 1000000 in
/-- At a positive date the final instruction in the prefix supplies its own output host capacity. -/
theorem profiled_noninitial_operand_hosts (pre : Geometry G S menu k w 0 initial)
    (placed : ∀i (e : RunTrace.Events traces i),fitsAt traces menu initial (w:=w) i e)
    (walk : (Epochs.finish G _ _ run).Choice)
    {U : MarkedWorld F 0 pins (fun _=>s*1)} {i z D : ℕ} {prior : Reached U G price fee S k i z D wire s}
    (before : Path (trace walk).origin.source prior) (remaining : Path prior (trace walk).target)
    (joined : before.append remaining=(trace walk).path) (positiveAge : 0< i) :
    Fintype.card prior.V≤(cursor i).ports.operandHosts :=by
  let common:=all_registered_moves X G S ordinary reset branch positive room shorten w menu rfl rfl rfl
  have lastMove (j : ℕ) (e : RunTrace.Events traces j) :
      ∃mv : Move w,step j e (cursor j) mv ∧ cursor (j+1)=mv.next :=by
    have geo:=geometry_on_event traces menu initial (fun t a b x y=>common t (cursor t) a b x y)
      (fun c=>(trace c).calendar) (fun c=>(trace c).kinds) pre placed e.1 j e.2
    obtain ⟨mv,posted,_,_⟩:=placed j e geo
    exact ⟨mv,posted,(returned traces menu initial j e mv posted
      (fun other y hy=>common j (cursor j) other e y mv hy posted)).2⟩
  let beforeAt : Path (traces walk).first prior := by
    dsimp only [traceAt]
    exact before
  let afterAt : Path prior (traces walk).last := by
    dsimp only [traceAt]
    exact remaining
  have joinedAt : beforeAt.append afterAt = (traces walk).path := by
    dsimp only [traceAt, beforeAt, afterAt]
    exact joined
  refine @RegisterTimeline.noninitialPopulationOnTrace F pins _ G S (fun _ => s*1) 0 k wire s S.length w price fee
    _ traces _ _ menu initial walk lastMove ?_ U i z D prior beforeAt afterAt joinedAt positiveAge
  intro V age grain degree₀ grain' degree' rate src nonneg T ballot norm dst ticket prev rest eqn at_
  dsimp only [traceAt] at prev rest eqn
  exact @Branch.registered_ordinary_card F _ cp nP X G S k n h C f g p _ _ _ ordinary.radix run walk
    (trace walk) V age grain degree₀ grain' degree' rate src T nonneg ballot norm dst ticket prev rest eqn
    op dateTail drift degree payload ((menu).seats age) at_.ports (menu).ordinary at_.floor

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
