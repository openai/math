import OAI.Hierarchy.DescentNamedRetainedRanges
import OAI.Hierarchy.DescentResetIssuedRange

namespace OAI
/-! # Read the three printed terminal range digits from the chosen reset's real operand words -/
namespace Hierarchy.DescentSixParty.SeedNamed.Palette
open DescentCompiler DescentKernelHistory DescentBundleHistory DescentInitialHost DescentColonies
open DescentRotor DescentResetGates DescentEpochTagKeys DescentPrimitivePalette Chronology
open DescentPackedSeed DescentMixedRouter DescentResetInvoice DescentTerminalSliceRuns DescentTerminalCombinedRole Catalyst Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
variable {F : Type} [Field F]

open DescentRetainedRangeDigits DescentSIMDLookup
open DescentLocalArchiveOrder DescentDatedAddressBook DescentSIMDLookup DescentPackedColony DescentDatedPriorOperand Computability.VPVNP.BurstRAM
open private Origin.archiveShape from OAI.Hierarchy.DescentNamedHistoryShape
open private encodedOrigin from OAI.Hierarchy.DescentNamedPrimitivePalette
open private readsAtView branchReadsOfHistory selectedBranch selectedRotor from
  OAI.Hierarchy.DescentNamedRetainedRanges

private theorem physicalDigit {P : Type} {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {B : BitDescription W} (v : ResetOutput) {w : ℕ} (base : ℕ) (mem : Memory w) (pos : 0 < v.receiver.lanes)
    (blocks : NodeOrder.All B → Fin v.receiver.blocks) (hosts : NodeOrder.All B → Fin v.receiver.hosts)
    (groups : NodeOrder.All B → Fin v.receiver.groups) (slots : NodeOrder.All B → Fin v.nodes)
    (reg : Register B) (registers : reg = fromRAM (PriorResetArchive.reset v base) v.rangeLayout v.nodeBits mem pos blocks hosts groups slots)
    (pitch : v.receiver.lanes = v.receiver.groups) (word : v.nodeBits*v.nodes*v.receiver.lanes ≤ w)
    (x : NodeOrder.All B) {n : ℕ} (fit : n ≤ v.argumentSlots)
    (sp : Fin 3→Fin v.argumentSlots→Fin v.receiver.hosts→Fin v.receiver.groups→Cell (v.nodeBits*v.nodes))
    (observed : ∀ j f, Reads (v.terminalField base (DescentRetainedRangeDigits.page f) j (blocks x)) (sp f j) v.receiver.groups mem)
    (j : Fin n) (f : Fin 3) {value : ℕ} (retained : reg.word x j.val f = value) :
    ((encode v.nodeBits v.nodes).symm (sp f (j.castLE fit) (hosts x) (groups x)) (slots x)).val = value := by
  have seen : Reads (v.terminalField base (DescentRetainedRangeDigits.page f) (j.castLE fit) (blocks x))
      (sp f (j.castLE fit)) v.receiver.lanes mem := by rw [pitch]; exact observed _ _
  have decoded := v.issued_range base mem pos blocks hosts groups slots x (j.castLE fit) f
    (fun i h g => (encode v.nodeBits v.nodes).symm (sp f (j.castLE fit) h g) i)
    (by simpa only [Equiv.apply_symm_apply] using seen) word
  exact decoded.symm.trans ((congrArg (fun t : Register B => t.word x j.val f) registers.symm).trans retained)

private def issuedView {P : Type} {depth s Z p R : ℕ} {bits : P → ℕ} {W : MarkedWorld F depth P bits}
    {G : PoweredGadget F} {op : RotorSpec} {B : BitDescription W}
    (dict : Label G s Z op → List (List Bool) → F) (enc : Encoding (Label G s Z op) dict B)
    (sh : WorldShape p R B) (reg : Register B) (history : Prop) : Prop :=
  ∀ (v : ResetOutput) {w : ℕ} (base : ℕ) (m : Memory w) (pos : 0 < v.receiver.lanes)
    (blocks : NodeOrder.All B → Fin v.receiver.blocks) (hosts : NodeOrder.All B → Fin v.receiver.hosts)
    (groups : NodeOrder.All B → Fin v.receiver.groups) (slots : NodeOrder.All B → Fin v.nodes),
    history → reg = fromRAM (PriorResetArchive.reset v base) v.rangeLayout v.nodeBits m pos blocks hosts groups slots →
    v.receiver.lanes = v.receiver.groups → v.nodeBits*v.nodes*v.receiver.lanes ≤ w →
    ∀ (vertex : W.graph.Site) (node : ((enc.view dict).recipe vertex).Node),
    classify G p s (((enc.view dict).recipe vertex).tag node) = .rotor →
    ∀ (fit : (repeatFields (((Encoding.viewShape dict enc sh).sites vertex).sliceFields node).flatten).length ≤ v.argumentSlots)
      (sp : Fin 3 → Fin v.argumentSlots → Fin v.receiver.hosts → Fin v.receiver.groups → Cell (v.nodeBits*v.nodes)),
    (∀ j f, Reads (v.terminalField base (DescentRetainedRangeDigits.page f) j (blocks ⟨vertex,node⟩)) (sp f j) v.receiver.groups m) →
    ∀ (j : Fin (repeatFields (((Encoding.viewShape dict enc sh).sites vertex).sliceFields node).flatten).length) (f : Fin 3),
    ((encode v.nodeBits v.nodes).symm (sp f (j.castLE fit) (hosts ⟨vertex,node⟩) (groups ⟨vertex,node⟩)) (slots ⟨vertex,node⟩)).val =
      atSlot ((Encoding.viewShape dict enc sh).sites vertex) node j.val f

private theorem issuedOfRead {P : Type} {depth s Z p R : ℕ} {bits : P → ℕ} {W : MarkedWorld F depth P bits}
    {G : PoweredGadget F} {op : RotorSpec} {B : BitDescription W}
    (dict : Label G s Z op → List (List Bool) → F) (enc : Encoding (Label G s Z op) dict B)
    (sh : WorldShape p R B) (reg : Register B) (history : Prop)
    (read : history → readsAtView dict enc sh reg) : issuedView dict enc sh reg history := by
  intro v w base m pos blocks hosts groups slots copies registers pitch word vertex node tag fit sp observed j f
  exact physicalDigit (B:=B) v base m pos blocks hosts groups slots reg registers pitch word ⟨vertex,node⟩ fit sp observed j f
    (read copies vertex node tag j f)

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
private def issuedRule {he : 0≤ε₀} {hu : 0≤u} {radix : S.radix=2^k}
    {r : Epochs G hu he (h:=h) (C:=C) (Ht:=depthBound_) (t:=S.rounds) S.height
      (initial X S.copies s₀ (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c)
    (hp : 0 < p) (stride : 1 ≤ R) (op : RotorSpec) (menu : Runnable F op) (fixed : b.path.OnlyRotor op)
    : Prop :=
  ∀ pages : RangePages b.origin.source hp b.origin.archive,
    let code := encodePath op menu b.path hp (b.path.recorded_whole p b.recorded) fixed b.origin.archive (encodedOrigin (p:=p) b.origin op menu)
    issuedView (G:=G) (s:=s₀) (Z:=S.grainAt G.b p 0) (p:=p) («R»:=R)
      (B:=(Branch.archive X G S (r:=r) (c:=c) b hp).bit)
      (dictionary (s:=s₀) (Z:=S.grainAt G.b p 0) G op menu p) code
      (Branch.bundleShape X G S (r:=r) (c:=c) b hp stride) (pages b.path (b.path.recorded_whole p b.recorded))
      (Copies hp b.origin.archive pages stride pinSizes_ (Origin.archiveShape b.origin p R hp stride widthDiv_)
        b.path (b.path.recorded_whole p b.recorded) b.aligned)

private theorem issuedRuleHolds {he : 0≤ε₀} {hu : 0≤u} {radix : S.radix=2^k}
    {r : Epochs G hu he (h:=h) (C:=C) (Ht:=depthBound_) (t:=S.rounds) S.height
      (initial X S.copies s₀ (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c)
    (hp : 0 < p) (stride : 1 ≤ R) (op : RotorSpec) (menu : Runnable F op) (fixed : b.path.OnlyRotor op)
    : issuedRule X G S (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (p:=p) (R:=R) (r:=r) (c:=c) b hp stride op menu fixed := by
  intro pages
  apply issuedOfRead
  intro copies
  exact branchReadsOfHistory X G S (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (p:=p) (R:=R) (r:=r) (c:=c) b hp stride op menu fixed pages copies
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

attribute [local irreducible] issuedRule selectedBranch

/-- Decode the three rotor range fields from the selected reset's packed operand word. -/
theorem issued_terminal_digits (c : (last).Choice) :
    issuedRule X G S (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (p:=p) (R:=strideN_) (r:=(cert).choose) (c:=c)
    (selectedBranch X G S ordinary reset branch positive room shorten c) positive stride_ rot reset.menu
    (selectedRotor X G S ordinary reset branch positive room shorten c) :=
  issuedRuleHolds X G S (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (p:=p) (R:=strideN_) (r:=(cert).choose) (c:=c)
    (selectedBranch X G S ordinary reset branch positive room shorten c) positive stride_ rot reset.menu
    (selectedRotor X G S ordinary reset branch positive room shorten c)

end
end Hierarchy.DescentSixParty.SeedNamed.Palette

end OAI
