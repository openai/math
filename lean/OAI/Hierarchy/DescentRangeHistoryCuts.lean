import OAI.Hierarchy.DescentReachedRangeHistory

namespace OAI
/-! # The three native range words on cuts of one selected path -/
namespace Hierarchy.DescentRetainedRangeDigits
open DescentSixParty DescentSixParty.Chronology DescentCompiler DescentTerminalSliceRuns DescentSIMDLookup
open DescentKernelHistory DescentPrimitivePalette DescentLocalArchiveOrder DescentEpochTagKeys DescentBundleHistory
open DescentOrderedReset DescentResetAttachments DescentRouterBank DescentRotor DescentResetGates Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}

variable {p R : ℕ} {G : PoweredGadget F} {S : AtomSchedule} {q ε : ℝ} {k wire hist : ℕ}
variable {W₀ : MarkedWorld F d P bits} {a₀ z₀ D₀ age z₁ D₁ : ℕ}
    {start : Reached W₀ G q ε S k a₀ z₀ D₀ wire hist} {now : Reached W G q ε S k age z₁ D₁ wire hist}
variable (hp : 0<p) (a : Archive W₀)
variable (pages : ∀{V : MarkedWorld F d P bits} {i g D : ℕ} {tick : Reached V G q ε S k i g D wire hist},
    (prev : Path start tick)→(whole : prev.whole p)→Register (prev.archive p hp a whole).bit)
variable (one : 1≤R) (pins : ∀v,p∣bits v) (sh : WorldShape p R a.bit)

include hp a pages one pins sh in
/-- The retained words, and the descriptors of newborn reset lanes, written by
the current event. This consists only of equalities for this single memory change. -/
def LastCopy (path : Path start now) (whole : path.whole p) (aligned : path.aligned p R) : Prop := by
  cases path with
  | here=>exact True
  | @ordinary _ i z D z' D' cap prev u he T c norm target ticket=>
    let old:=prev.archive p hp a whole
    let prior:=pages prev whole
    let newPage:=pages (prev.ordinary ticket) whole
    exact ∀x y,roots ticket old x=Sum.inl y →
      ∀j,j<(repeatFields ((archiveShape hp one pins a sh prev whole aligned.1).nodeFields y).flatten).length → ∀f,newPage.word x j f=prior.word y j f
  | @reset _ i z D _ _ _ _ _ _ _ cap prev ctl b=>
    let old:=prev.archive p hp a whole.1
    let prior:=pages prev whole.1
    let newPage:=pages (prev.reset b) whole
    let origin:=resetOrigin b hp whole.2 old
    let key:=DescentOrderedReset.grains _ b.count b.order
    let fit : b.reset.unit=b.reset.unit/p*p := (Nat.div_mul_cancel whole.2).symm
    let lane:=b.reset.laneProgram key (b.reset.unit/p) p hp fit
    let device:=fun v=>ofProgram (fun e=>boundaryWidth b.reset.bank v e/p)
      (b.reset.laneWidth_eq (b.reset.unit/p) p fit v) hp (lane v)
    exact (∀x y,origin x=Sum.inl y → ∀j,j<(repeatFields ((archiveShape hp one pins a sh prev whole.1 aligned.1).nodeFields y).flatten).length →
      ∀f,newPage.word x j f=prior.word y j f) ∧
      (∀x v,origin x=Sum.inr (Sum.inr v) → ∀j,j<(repeatFields ((device v.1).sliceFields v.2).flatten).length →
        ∀f,newPage.word x j f=atSlot (device v.1) v.2 j f)

private theorem appendSteps {U V : MarkedWorld F d P bits} {i₁ z₂ D₂ i₂ z₃ D₃:ℕ}
    {r:Reached U G q ε S k i₁ z₂ D₂ wire hist} {u:Reached V G q ε S k i₂ z₃ D₃ wire hist}
    (x:Path start now) (y:Path now r) (z:Path r u) :
    x.append (y.append z)=(x.append y).append z :=by
  induction z with
  | here=>rfl
  | ordinary old t ih=>exact congrArg (fun walk=>walk.ordinary t) ih
  | reset old B ih=>exact congrArg (fun walk=>walk.reset B) ih

/-- Dated memory equalities are needed only on prefixes of this very branch. -/
theorem Copies_of_cuts (path:Path start now) (whole:path.whole p) (aligned:path.aligned p R)
    (onCut : ∀{U:MarkedWorld F d P bits} {i g D:ℕ} {r:Reached U G q ε S k i g D wire hist},
      ∀(before:Path start r) (after_:Path r now),before.append after_=path →
      ∀(witness:before.whole p) (agree:before.aligned p R),
        LastCopy hp a pages one pins sh before witness agree) :
    Copies hp a pages one pins sh path whole aligned :=by
  have build {U:MarkedWorld F d P bits} {i g D:ℕ} {r:Reached U G q ε S k i g D wire hist}
      (before:Path start r) (after_:Path r now) (cut:before.append after_=path)
      (witness:before.whole p) (agree:before.aligned p R) :
      Copies hp a pages one pins sh before witness agree :=by
    induction before with
    | here=>trivial
    | ordinary prior step ih=>
      exact ⟨ih ((Path.here.ordinary step).append after_)
        ((appendSteps prior (Path.here.ordinary step) after_).trans cut) witness agree.1,
        onCut (prior.ordinary step) after_ cut witness agree⟩
    | reset prior closed ih=>
      exact ⟨ih ((Path.here.reset closed).append after_)
        ((appendSteps prior (Path.here.reset closed) after_).trans cut) witness.1 agree.1,
        onCut (prior.reset closed) after_ cut witness agree⟩
  exact build path .here rfl whole aligned

end
end Hierarchy.DescentRetainedRangeDigits

end OAI
