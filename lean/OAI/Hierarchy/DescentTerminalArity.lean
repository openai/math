import OAI.Hierarchy.DescentRetainedArity
import OAI.Hierarchy.DescentCalendarNodeWidths
import OAI.Hierarchy.DescentNormalizedEpochs

namespace OAI
namespace Hierarchy.DescentSixParty
open DescentKernelHistory DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
    {S : AtomSchedule} {q ε : ℝ} {i₀ z₀ D₀ i₁ z₁ D₁ w hist k : ℕ}
variable {W₀ W₁ : MarkedWorld F d P bits} {first : Reached W₀ G q ε S k i₀ z₀ D₀ w hist}
    {last : Reached W₁ G q ε S k i₁ z₁ D₁ w hist}

theorem Chronology.Path.arities (p : ℕ) (hp : 0<p) (a : Chronology.Archive W₀) (path : Chronology.Path first last)
    (whole : path.whole p) (pre : a.bit.ArityBound (max 8 (2^S.capGain))) :
    (path.archive p hp a whole).bit.ArityBound (max 8 (2^S.capGain)) := by
  induction path with
  | here=>exact pre
  | ordinary prior ticket ih=>
    apply BitDescription.ArityBound.follow
    apply BitDescription.ArityBound.scanned (ih whole)
    exact Nat.le_max_left ..
  | @reset A i z D n h C f g cut tail src prior ctl b ih=>
    let before:=prior.archive p hp a whole.1
    have old : before.bit.ArityBound (max 8 (2^S.capGain)) := ih whole.1
    have grains : (BitDescription.granular A b.count (z*G.b) b.fit before.bit).ArityBound (max 8 (2^S.capGain)):=old
    apply BitDescription.ArityBound.follow
    apply BitDescription.ArityBound.lane_reset grains
    · exact (show 2≤8 by decide).trans (Nat.le_max_left ..)
    · rw [b.width]
      exact ctl.gate_arity.trans (Nat.le_max_right ..)

variable {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
  {n h C f g p : ℕ}
local notation "wire" => S.epochPower^S.priceExponent
local notation "s" => S.firstWidth G.b p
local notation "q₀" => (1/((s:ℝ)*(wire:ℝ)):ℝ)
local notation "ε₀" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => q₀*(wire:ℝ)
local notation "resetDepth" => GroupStage.depthBound (atRound S.rounds) n f g
local notation "start" => initialGroup X S.copies s

theorem NativeBranch.node_arity {he : 0≤ε₀} {hu : 0≤u} {radix : S.radix=2^k} {R : ℕ}
    {r : Epochs G hu he (h:=h) (C:=C) (Ht:=resetDepth) (t:=S.rounds) S.height start}
    {c : (Epochs.finish G hu he r).Choice} (b : NativeBranch X G S radix R r c) (hp : 0<p) : (NativeBranch.archive X G S b hp).bit.ArityBound (max 8 (2^S.capGain)) := by
  apply Chronology.Path.arities
  intro v n
  exact (BitDescription.initial_arity_bound X S.copies s (Chronology.epochsSource G r c) v n).trans
    ((show 3≤8 by decide).trans (Nat.le_max_left ..))

end
end Hierarchy.DescentSixParty

end OAI
