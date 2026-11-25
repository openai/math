import OAI.Hierarchy.DescentNamedBranchMachine
import OAI.Hierarchy.DescentRecordedResetElapsed
import OAI.Hierarchy.DescentNamedSourceSorted
import OAI.Hierarchy.DescentSnapshotCutGrain

namespace OAI
/-! # The recorded rotor, date, incoming grain and sorted cable order at each real reset -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentCompiler DescentMixedRouter DescentResetInvoice
open Catalyst CatalystSubstitution CorrectionBatch Computability.BorderVNP.Crossing
open ThreeFlat Routing
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
set_option hygiene false
set_option maxHeartbeats 800000
local notation "cert" => SeedNamed.normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "run" => (cert).choose
local notation "last" => Epochs.finish G _ _ run
local notation "s" => S.firstWidth G.b p
local notation "order" => inputOrder X G S ordinary reset branch positive room shorten
local notation "trace" => SeedNamed.issued X G S ordinary reset branch positive room shorten
local notation "price" => (1/((s:ℝ)*(S.epochPower^S.priceExponent:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "pins" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port nP X.width)))
local notation "widths" => (fun _ : pins=>s*1)


variable (walk : (last).Choice)
variable {U : MarkedWorld F 0 pins widths} {i z D : ℕ}
  {r : Reached U G price fee S k i z D (S.epochPower^S.priceExponent) s}
  {n₁ h₁ C₁ f₁ g₁ cut₁ tail₁ : ℕ} {ctl : ResetRates G S k D n₁ h₁ C₁ f₁ g₁ cut₁ tail₁}
  (before : Path (trace walk).origin.source r) (B : ClosedReset r ctl)
  (after_ : Path B.next (trace walk).target) (joined : (before.reset B).append after_=(trace walk).path)

private theorem recorded_prefix {Pin : Type} {bits : Pin → ℕ} {dim wire hist : ℕ}
    {q ε : ℝ} {U₀ U₁ U₂ : MarkedWorld F dim Pin bits} {i₀ i₁ i₂ z₀ z₁ z₂ D₀ D₁ D₂ : ℕ}
    {x : Reached U₀ G q ε S k i₀ z₀ D₀ wire hist}
    {y : Reached U₁ G q ε S k i₁ z₁ D₁ wire hist}
    {lastSite : Reached U₂ G q ε S k i₂ z₂ D₂ wire hist}
    (scale : ℕ) (op : RotorSpec) (l : Path x y) (r₃ : Path y lastSite)
    (yes : (l.append r₃).recorded scale ∧ (l.append r₃).OnlyRotor op) :
    l.recorded scale ∧ l.OnlyRotor op := by
  induction r₃ with
  | here => exact yes
  | ordinary prev link ih => exact ih yes
  | reset prev bank ih => exact ih ⟨yes.1.1,yes.2.1⟩

/-- The physical menu stores the full multigraph multiplicity table and its dimensions. -/
theorem rotor_control_fields {D₀ D₁ n₀ n₁ h₀ h₁ C₀ C₁ f₀ f₁ g₀ g₁ c₀ c₁ t₀ t₁ : ℕ}
    (left : ResetRates G S k D₀ n₀ h₀ C₀ f₀ g₀ c₀ t₀) (right : ResetRates G S k D₁ n₁ h₁ C₁ f₁ g₁ c₁ t₁)
    (same : RotorSpec.ofRates left=RotorSpec.ofRates right) :
    n₀=n₁ ∧ h₀=h₁ ∧ C₀=C₁ ∧ f₀=f₁ ∧ g₀=g₁ ∧ D₀=D₁ ∧ left.bitsR=right.bitsR ∧ HEq left.board right.board:=by
  have nn : n₀=n₁:=congrArg RotorSpec.n same
  have hh : h₀=h₁:=congrArg RotorSpec.regularity same
  refine ⟨nn,hh,congrArg RotorSpec.C same,congrArg RotorSpec.rowExponent same,congrArg RotorSpec.reserveExponent same,
    congrArg RotorSpec.stageDegree same,congrArg RotorSpec.w same,?_⟩
  have arcs {l r : RotorSpec} (eqn:l=r) : HEq l.arcs r.arcs:=by cases eqn;rfl
  subst n₁
  subst h₁
  have identical : left.board.arcs=right.board.arcs:=eq_of_heq (arcs same)
  apply heq_of_eq
  cases a:left.board;cases b:right.board;simp only [a,b] at identical
  subst_vars;rfl

private theorem chosenRotor (walk : (last).Choice) :
    (trace walk).path.OnlyRotor (RotorSpec.ofRates reset) := by
  delta SeedNamed.issued
  exact ((cert).choose_spec.2.2.choose_spec.choose_spec walk).choose_spec.2.2.1.2

private theorem controls_on_cut {Pin : Type} [Fintype Pin] {bits : Pin → ℕ}
    {dim wire hist : ℕ} {q ε : ℝ} (t : RunTrace G q ε S k wire hist S.length bits dim)
    {U : MarkedWorld F dim Pin bits} {i z D : ℕ} {r : Reached U G q ε S k i z D wire hist}
    {n₁ h₁ C₁ f₁ g₁ cut₁ tail₁ : ℕ} {ctl : ResetRates G S k D n₁ h₁ C₁ f₁ g₁ cut₁ tail₁}
    (before : Path t.first r) (B : ClosedReset r ctl) (after_ : Path B.next t.last)
    (joined : (before.reset B).append after_ = t.path) (rec : t.path.recorded p)
    (operator : t.path.OnlyRotor (RotorSpec.ofRates reset))
    (kinds : t.path.kinds = kindCalendar S.rounds S.height) (first : t.firstGrain = S.grainAt G.b p 0)
    (shortens : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2) :
    B.Recorded p ∧ RotorSpec.ofRates ctl=RotorSpec.ofRates reset ∧ tail₁=tail ∧ 0 < i ∧
      SourceSorted U r.order ∧ z=S.grainAt G.b p (i+1) := by
  have seen := recorded_prefix G S p (RotorSpec.ofRates reset) (before.reset B) after_
    (by rw [joined]; exact ⟨rec,operator⟩)
  have elapsed := Chronology.elapsed_at_reset shortens (reset_kind_on_cut B before after_ joined kinds)
  exact ⟨seen.1.2,seen.2.2,(Nat.pow_right_inj (by decide : 1<2)).mp (ctl.base.symm.trans reset.base),
    elapsed,before.final_sourceSorted elapsed,Path.Event.resetGrain (t:=t) kinds first before B after_ joined⟩

attribute [local irreducible] SeedNamed.issued Origin.source

include X G S ordinary reset branch positive room shorten walk before after_ joined in
theorem profiled_reset_controls :
    B.Recorded p ∧ RotorSpec.ofRates ctl=RotorSpec.ofRates reset ∧ tail₁=tail ∧ 0< i ∧
      SourceSorted U r.order ∧ z=S.grainAt G.b p (i+1):=by
  apply controls_on_cut G S reset (traceAt X G S ordinary reset branch positive room shorten walk)
    before B after_ joined
  · exact (trace walk).recorded
  · exact chosenRotor X G S ordinary reset branch positive room shorten walk
  · exact (trace walk).kinds
  · rfl
  · exact shorten

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
