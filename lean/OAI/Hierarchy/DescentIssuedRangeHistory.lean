import OAI.Hierarchy.DescentRangeHistoryCuts
import OAI.Hierarchy.DescentRangePaddingCuts
import OAI.Hierarchy.DescentDatedBranchEvents

namespace OAI
/-! Recover all three retained range digits from the registered events of a single branch. -/
namespace Hierarchy.DescentRetainedRangeDigits
open DescentSixParty DescentSixParty.Chronology DescentCompiler DescentTerminalSliceRuns DescentSIMDLookup
open DescentKernelHistory DescentPrimitivePalette DescentLocalArchiveOrder DescentEpochTagKeys DescentBundleHistory
open DescentOrderedReset DescentResetAttachments DescentRouterBank DescentRotor DescentResetGates Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}

variable {p R : ℕ} {G : PoweredGadget F} {S : AtomSchedule} {q ε : ℝ} {k wire hist : ℕ}
variable {W₀ : MarkedWorld F d P bits} {z₀ D₀ age z₁ D₁ : ℕ}
    {start : Reached W₀ G q ε S k 0 z₀ D₀ wire hist} {now : Reached W G q ε S k age z₁ D₁ wire hist}
variable (hp : 0<p) (a : Archive W₀)
variable (pages : ∀{V : MarkedWorld F d P bits} {i g D : ℕ} {tick : Reached V G q ε S k i g D wire hist},
    (prev : Path start tick)→(whole : prev.whole p)→Register (prev.archive p hp a whole).bit)
variable (one : 1≤R) (pins : ∀v,p∣bits v) (sh : WorldShape p R a.bit)

variable (path : Path start now)

include hp a pages one pins sh in
/-- The postdate's live slots and its count-zero padding at an event of this branch. -/
def rangeAtEvent {i : ℕ} (e : path.Event i) : Prop := by
  cases e with
  | ordinary before ticket after joined =>
    exact ∀(whole : (before.ordinary ticket).whole p) (aligned : (before.ordinary ticket).aligned p R),
      LastCopy hp a pages one pins sh (before.ordinary ticket) whole aligned ∧
      LastCountPadding hp a pages one pins sh (before.ordinary ticket) whole aligned
  | reset before closed after joined =>
    exact ∀(whole : (before.reset closed).whole p) (aligned : (before.reset closed).aligned p R),
      LastCopy hp a pages one pins sh (before.reset closed) whole aligned ∧
      LastCountPadding hp a pages one pins sh (before.reset closed) whole aligned

theorem range_history (whole:path.whole p) (aligned:path.aligned p R)
    (ordinary : ∀i (e : path.Event i),e.isReset=false → rangeAtEvent hp a pages one pins sh path e)
    (reset : ∀i (e : path.Event i),e.isReset=true → rangeAtEvent hp a pages one pins sh path e) :
    Copies hp a pages one pins sh path whole aligned ∧ CountPadding hp a pages one pins sh path whole aligned :=by
  have step {U:MarkedWorld F d P bits} {i g D:ℕ} {r:Reached U G q ε S k i g D wire hist}
      (before:Path start r) (after_:Path r now) (cut:before.append after_=path)
      (witness:before.whole p) (agree:before.aligned p R) :
      LastCopy hp a pages one pins sh before witness agree ∧ LastCountPadding hp a pages one pins sh before witness agree :=by
    cases before with
    | here=>exact ⟨trivial,trivial⟩
    | ordinary prev ticket=>exact ordinary _ (.ordinary prev ticket after_ cut) rfl witness agree
    | reset prev closed=>exact reset _ (.reset prev closed after_ cut) rfl witness agree
  exact ⟨Copies_of_cuts hp a pages one pins sh path whole aligned
      (fun before after_ cut witness agree=>(step before after_ cut witness agree).1),
    CountPadding_of_cuts hp a pages one pins sh path whole aligned
      (fun before after_ cut witness agree=>(step before after_ cut witness agree).2)⟩

end
end Hierarchy.DescentRetainedRangeDigits

end OAI
