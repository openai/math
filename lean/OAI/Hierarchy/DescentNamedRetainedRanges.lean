import OAI.Hierarchy.DescentReachedRangeHistory
import OAI.Hierarchy.DescentNamedTerminalSliceLayout

namespace OAI
/-! # Decode retained rotor components at the named terminal choice -/
namespace Hierarchy.DescentSixParty.SeedNamed.Palette
open DescentCompiler DescentKernelHistory DescentBundleHistory DescentInitialHost DescentColonies
open DescentRotor DescentResetGates DescentEpochTagKeys DescentPrimitivePalette Chronology
open DescentPackedSeed DescentMixedRouter DescentResetInvoice DescentTerminalSliceRuns DescentTerminalCombinedRole Catalyst Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
variable {F : Type} [Field F]

open DescentRetainedRangeDigits DescentSIMDLookup
section SourceTags
open private encodedOrigin renameEncoding carryEncoding changeEncoding from
  OAI.Hierarchy.DescentNamedPrimitivePalette
open private Origin.archive_eq from OAI.Hierarchy.DescentNamedHistoryShape
open private transportArchive from OAI.Hierarchy.DescentNamedOriginalArchive

section
variable {P : Type} {d : ℕ} {bits : P → ℕ} {W V : MarkedWorld F d P bits}
    {G : PoweredGadget F} {op : RotorSpec} {s z p : ℕ} {dict : Label G s z op → List (List Bool) → F}

private def noRotor {a : Archive W} (code : Encoding (Label G s z op) dict a.bit) : Prop :=
  ∀ x, classify G p s (code.atNode x) ≠ .rotor

private theorem changed_noRotor (a b : Archive W) (same : a = b)
    (code : Encoding (Label G s z op) dict a.bit) (ok : noRotor (a := a) (p := p) code) :
    noRotor (a := b) (p := p) (changeEncoding a b same code) := by
  cases same
  exact ok

private theorem package_noRotor (a : Archive W) (pkg : ArchiveTransport a V) (same : W = V)
    (identity : pkg = transportArchive a same)
    (code : Encoding (Label G s z op) dict a.bit) (ok : noRotor (a := a) (p := p) code) :
    noRotor (a := pkg.data) (p := p) (carryEncoding pkg code) := by
  subst pkg
  cases same
  exact ok

private theorem renamed_noRotor (a : Archive W) (places : Equiv.Perm W.graph.Site)
    (edges : Equiv.Perm W.graph.Edge) (code : Encoding (Label G s z op) dict a.bit)
    (ok : noRotor (a := a) (p := p) code) :
    noRotor (a := renamedArchive a places edges) (p := p) (renameEncoding a places edges code) := by
  intro x
  exact ok ⟨places.symm x.1,x.2⟩
end

attribute [local irreducible] Origin.archivePackage Origin.source
private theorem seed_not_rotor {cp pins : ℕ} {X : Approximation F cp pins} {G : PoweredGadget F}
    {S : AtomSchedule} {q fee : ℝ} {k s z wire p : ℕ}
    {c : (initialGroup X S.copies s).Choice} {digits : Fin S.copies ≃ Fin (S.groupCount 0) × Block k}
    (o : Origin (G := G) (S := S) (s := s) (q := q) (fee := fee) (z := z) (wire := wire) X c digits)
    (op : RotorSpec) (menu : Runnable F op) :
    ∀ x, classify G p s ((encodedOrigin (p := p) o op menu).atNode x) ≠ .rotor := by
  change noRotor (a := o.archive) (p := p) (encodedOrigin (p := p) o op menu)
  apply changed_noRotor o.archivePackage.data o.archive (Origin.archive_eq o).symm
  apply package_noRotor _ o.archivePackage (linked_world X c digits o.seed) (by unfold Origin.archivePackage; rfl)
  apply renamed_noRotor (seedArchive X S.copies s c) (site o.raw) (edge o.raw)
  rintro ⟨⟨_,_⟩,u⟩ eqn
  cases eqn


end SourceTags

open private encodedOrigin chosenArchive from OAI.Hierarchy.DescentNamedPrimitivePalette
open private Origin.archiveShape from OAI.Hierarchy.DescentNamedHistoryShape
attribute [local irreducible] Origin.archivePackage Origin.source encodedOrigin Origin.archiveShape encodePath
open DescentLocalArchiveOrder
private def readsAtView {P : Type} {d s Z p R : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {op : RotorSpec} {B : BitDescription W}
    (dict : Label G s Z op → List (List Bool) → F) (enc : Encoding (Label G s Z op) dict B) (sh : WorldShape p R B) (page : Register B)
: Prop :=
  ∀ (v : W.graph.Site) (n : ((enc.view dict).recipe v).Node) (_tag : classify G p s (((enc.view dict).recipe v).tag n)=.rotor)
    (j : Fin (repeatFields (((Encoding.viewShape dict enc sh).sites v).sliceFields n).flatten).length) (f : Fin 3),
    page.word ⟨v,n⟩ j.val f = atSlot ((Encoding.viewShape dict enc sh).sites v) n j.val f

private theorem rangeAtView {P : Type} {d s Z p R : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {op : RotorSpec} {B : BitDescription W}
    (dict : Label G s Z op → List (List Bool) → F) (enc : Encoding (Label G s Z op) dict B) (sh : WorldShape p R B) (page : Register B)
    (read : ∀ x : NodeOrder.All B, classify G p s (enc.atNode x)=.rotor →
      ∀ j, j < (repeatFields (sh.nodeFields x).flatten).length → ∀ f, page.word x j f = atSlot (sh.sites x.1) x.2 j f)
    : readsAtView dict enc sh page := by
  intro v n tag j f
  exact (read ⟨v,n⟩ tag j.val j.isLt f).trans (of_fields (sh.sites v) n ((Encoding.viewShape dict enc sh).sites v) n rfl j.val f)

section
variable {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
local notation "wire₀" => S.epochPower^S.priceExponent
local notation "s₀" => S.firstWidth G.b p
local notation "q₀" => (1/((s₀:ℝ)*(wire₀:ℝ)):ℝ)
local notation "ε₀" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => q₀*(wire₀:ℝ)
local notation "depthBound_" => GroupStage.depthBound (atRound S.rounds) n f g
local notation "pinSizes_" => (fun _ => dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (grainAt_multiple S G.b 0) G.b) 1)
local notation "widthDiv_" => dvd_mul_of_dvd_left (grainAt_multiple S G.b 0) G.b
private theorem rangesOnBranch {he : 0≤ε₀} {hu : 0≤u} {radix : S.radix=2^k}
    {r : Epochs G hu he (h:=h) (C:=C) (Ht:=depthBound_) (t:=S.rounds) S.height
      (initial X S.copies s₀ (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c)
    (hp : 0 < p) (stride : 1 ≤ R) (op : RotorSpec) (menu : Runnable F op) (fixed : b.path.OnlyRotor op)
    (pages : RangePages b.origin.source hp b.origin.archive)
    (free : ∀x, classify G p s₀ ((encodedOrigin (p:=p) b.origin op menu).atNode x) ≠ .rotor)
    (history : Copies hp b.origin.archive pages stride pinSizes_ (Origin.archiveShape b.origin p R hp stride widthDiv_)
       b.path (b.path.recorded_whole p b.recorded) b.aligned) :
    let encoded := encodePath op menu b.path hp (b.path.recorded_whole p b.recorded) fixed b.origin.archive (encodedOrigin (p:=p) b.origin op menu)
    let sh := Branch.bundleShape X G S (r:=r) (c:=c) b hp stride
    ∀ x : NodeOrder.All (Branch.archive X G S (r:=r) (c:=c) b hp).bit, classify G p s₀ (encoded.atNode x) = .rotor →
      ∀ j, j < (repeatFields (sh.nodeFields x).flatten).length → ∀ f, (pages b.path (b.path.recorded_whole p b.recorded)).word x j f = atSlot (sh.sites x.1) x.2 j f :=
  reached_ranges hp b.origin.archive pages stride pinSizes_ (Origin.archiveShape b.origin p R hp stride widthDiv_)
    op menu (encodedOrigin (p:=p) b.origin op menu) b.path (b.path.recorded_whole p b.recorded) b.aligned fixed free history
private def branchReads {he : 0≤ε₀} {hu : 0≤u} {radix : S.radix=2^k}
    {r : Epochs G hu he (h:=h) (C:=C) (Ht:=depthBound_) (t:=S.rounds) S.height
      (initial X S.copies s₀ (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c)
    (hp : 0 < p) (stride : 1 ≤ R) (op : RotorSpec) (menu : Runnable F op) (fixed : b.path.OnlyRotor op)
    (pages : RangePages b.origin.source hp b.origin.archive)
    : Prop :=
  let code := encodePath op menu b.path hp (b.path.recorded_whole p b.recorded) fixed b.origin.archive (encodedOrigin (p:=p) b.origin op menu)
  readsAtView (G:=G) (s:=s₀) (Z:=S.grainAt G.b p 0) (p:=p) («R»:=R)
    (B:=(Branch.archive X G S (r:=r) (c:=c) b hp).bit)
    (dictionary (s:=s₀) (Z:=S.grainAt G.b p 0) G op menu p) code
    (Branch.bundleShape X G S (r:=r) (c:=c) b hp stride) (pages b.path (b.path.recorded_whole p b.recorded))

private theorem branchReadsOfHistory {he : 0≤ε₀} {hu : 0≤u} {radix : S.radix=2^k}
    {r : Epochs G hu he (h:=h) (C:=C) (Ht:=depthBound_) (t:=S.rounds) S.height
      (initial X S.copies s₀ (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c)
    (hp : 0 < p) (stride : 1 ≤ R) (op : RotorSpec) (menu : Runnable F op) (fixed : b.path.OnlyRotor op)
    (pages : RangePages b.origin.source hp b.origin.archive)
    (history : Copies hp b.origin.archive pages stride pinSizes_ (Origin.archiveShape b.origin p R hp stride widthDiv_)
       b.path (b.path.recorded_whole p b.recorded) b.aligned) :
    branchReads X G S (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (p:=p) (r:=r) (c:=c) b hp stride op menu fixed pages := by
  unfold branchReads
  apply rangeAtView
  exact rangesOnBranch X G S (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (p:=p) (r:=r) (c:=c) b hp stride op menu fixed pages (seed_not_rotor (p:=p) b.origin op menu) history

private def branchRangeRule {he : 0≤ε₀} {hu : 0≤u} {radix : S.radix=2^k}
    {r : Epochs G hu he (h:=h) (C:=C) (Ht:=depthBound_) (t:=S.rounds) S.height
      (initial X S.copies s₀ (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c)
    (hp : 0 < p) (stride : 1 ≤ R) (op : RotorSpec) (menu : Runnable F op) (fixed : b.path.OnlyRotor op)
    : Prop :=
  ∀ pages : RangePages b.origin.source hp b.origin.archive,
    Copies hp b.origin.archive pages stride pinSizes_ (Origin.archiveShape b.origin p R hp stride widthDiv_)
      b.path (b.path.recorded_whole p b.recorded) b.aligned →
    branchReads X G S (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (p:=p) (R:=R) (r:=r) (c:=c) b hp stride op menu fixed pages

private theorem branchRangeRuleHolds {he : 0≤ε₀} {hu : 0≤u} {radix : S.radix=2^k}
    {r : Epochs G hu he (h:=h) (C:=C) (Ht:=depthBound_) (t:=S.rounds) S.height
      (initial X S.copies s₀ (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c)
    (hp : 0 < p) (stride : 1 ≤ R) (op : RotorSpec) (menu : Runnable F op) (fixed : b.path.OnlyRotor op)
    : branchRangeRule X G S (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (p:=p) (R:=R) (r:=r) (c:=c) b hp stride op menu fixed :=
  fun pages history => branchReadsOfHistory X G S (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (p:=p) (R:=R) (r:=r) (c:=c) b hp stride op menu fixed pages history

end

variable {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b≤2^S.capGain) (positive : 0<p) (room : 10*(X.size+1)≤S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds≤1/2)
set_option quotPrecheck false
local notation "cert" => SeedNamed.normalized_epochs_issued_joint (p:=p) X G S ordinary reset branch positive room shorten
local notation "last" => Epochs.finish G _ _ (cert).choose
local notation "initialWidth_" => S.firstWidth G.b p
local notation "rot" => RotorSpec.ofRates reset
local notation "strideN_" => max 1 (max reset.bitsR (C*reset.bitsR))
local notation "branchAt" c_:arg => ((cert).choose_spec.2.2.choose_spec.choose_spec c_).choose
local notation "outputAt" c_:arg => relabel X G S ordinary reset branch positive room shorten c_
local notation "shapeAt" c_:arg => leafShape X G S ordinary reset branch positive room shorten c_
local notation "stride_" => Nat.le_max_left 1 (max reset.bitsR (C * reset.bitsR))
local notation "divides_" => dvd_mul_of_dvd_left (grainAt_multiple S G.b 0) G.b

local notation "wholeAt" b_:arg => (b_).path.recorded_whole p (b_).recorded
local notation "pins_" => (fun _ => dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (grainAt_multiple S G.b 0) G.b) 1)
local notation "seedShape" b_:arg => Origin.archiveShape (b_).origin p strideN_ positive stride_ divides_

private def selectedBranch (c : (last).Choice) := branchAt c

private theorem selectedRotor (c : (last).Choice) :
    (selectedBranch X G S ordinary reset branch positive room shorten c).path.OnlyRotor rot :=
  ((cert).choose_spec.2.2.choose_spec.choose_spec c).choose_spec.2.2.1.2

attribute [local irreducible] branchRangeRule selectedBranch

/-- The range register at a selected terminal choice reads the three fields of its rotor slice. -/
theorem terminal_ranges (c : (last).Choice) :
    branchRangeRule X G S (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (p:=p) (R:=strideN_) (r:=(cert).choose) (c:=c)
    (selectedBranch X G S ordinary reset branch positive room shorten c) positive stride_ rot reset.menu
    (selectedRotor X G S ordinary reset branch positive room shorten c) :=
  branchRangeRuleHolds X G S (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (p:=p) (R:=strideN_) (r:=(cert).choose) (c:=c)
    (selectedBranch X G S ordinary reset branch positive room shorten c) positive stride_ rot reset.menu
    (selectedRotor X G S ordinary reset branch positive room shorten c)

end
end Hierarchy.DescentSixParty.SeedNamed.Palette

end OAI
