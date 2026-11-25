import OAI.Hierarchy.DescentNamedInitialCircuit
import OAI.Hierarchy.DescentNamedOriginalExterior
import OAI.Hierarchy.DescentNamedTerminalLeaf
import OAI.Hierarchy.DescentExteriorChoice
import OAI.Hierarchy.DescentTerminalFullPins
import OAI.Hierarchy.DescentTerminalFromChip

namespace OAI
/-! # Seed and terminal factors on the full physical candidate -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open DescentTerminalGraphPositions DescentTerminalGraphVolume DescentTerminalCableOrder DescentKernelHistory
open DescentBundleHistory DescentPrimitivePalette DescentRotor DescentResetGates CorrectionBatch
open DescentTerminalBinReaddress DescentTerminalPorts Computability.BorderVNP.Crossing
open DescentExterior DescentExteriorShelf DescentTerminalChipRuntime DescentTerminalChipPins
open ThreeFlat Routing
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g W q piece : ℕ}
local notation "p" => W*piece
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0<W*piece) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
local notation "s" => S.firstWidth G.b p
local notation "last" => Epochs.finish G _ _ (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose
local notation "trace" => issued X G S ordinary reset branch positive room shorten
variable (w : ℕ) (fit : S.firstWidth G.b (W*piece) < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit
local instance : Fintype (ch).Pin := (ch).finite
variable {j rest : ℕ} (base : S.baseGroups=2^tail) (width : S.groupWidth k tail 0+k=j+(j+rest))
local notation "E" => Fintype.card (Port P X.width)
local notation "Old" => (ch).Pin ⊕ Hidden E j rest s
local notation "originalPins" => Port ((S.copies*s)*P) (CorrectionFrame.copiesWidth (S.copies*s) X.width)
local notation "mix" => fun c => Branch.publicLayout X G S (trace c) positive base width
local notation "power" => NativeBranch.copy_power S (radix:=ordinary.radix) base width

/-- The old part of the candidate contains one chart choice and its canonical exterior proposal. -/
def wideChoicePrior (x : originalPins→Bool) (z : Old→Bool) : Option (last).Choice :=
  proposed (ch).read mix (DescentExterior.publicRows X (Branch.copyInput X s power x)) z

local notation "prior" => wideChoicePrior X G S ordinary reset branch positive room shorten w fit base width

theorem wideChoice_single (x : originalPins→Bool) (c : (last).Choice) : ∃!z,prior x z=some c :=
  proposed_unique _ _ _ (packedChart_once X G S ordinary reset branch positive room shorten w fit) c

variable {K : ℕ} (cfg : DescentTerminalCompiledPrefix.Shape)
local notation "All" => DescentTerminalFullPins.Candidate Old K W q piece cfg.terminal.plane.rawRows
local notation "liftSeed" => DescentTerminalFullPins.history (old:=Old) ∘ Sum.inl ∘ (ch).seed

local notation "chip" => wideChoiceCircuit (K:=K) (W:=W) (q:=q) (piece:=piece) X G S ordinary reset branch positive room shorten w fit (j:=j) (rest:=rest) cfg

theorem wideChoice_weight (x : originalPins→Bool) (all : All→Bool) (c : (last).Choice)
    (hit : prior x (all ∘ DescentTerminalFullPins.history)=some c) :
    TypedWiring.value chip all = (last).weight c := by
  have seen := ((proposed_eq _ _ _ _ c).mp hit).1
  calc
    _ = TypedWiring.value (DescentTerminalSeedChip.circuit X (ch).seed)
        (all ∘ DescentTerminalFullPins.history ∘ Sum.inl) := by
      rw [wideChoiceCircuit,DescentTerminalSeedChip.value,DescentTerminalSeedChip.value]; rfl
    _ = _ := packedChart_weight X G S ordinary reset branch positive room shorten w fit _ c seen

variable (age : 0<S.height) (wFit : NativeBranch.binLimit (k:=k) S ≤ W)
    (qFit : NativeBranch.localLimit G S ≤ q) (qh : 0<q)
variable (pool : terminalPool X G S (W*piece) q W n h C f g ≤ cfg.terminal.pool)
    (raw : terminalRawRows X G S (W*piece) q n h C f g ≤ cfg.terminal.plane.rawRows)
local notation "leaf" => fun c => normalizedLeaf X G S ordinary reset branch positive room shorten c base width age
  wFit qFit qh cfg pool raw
local notation "Raw" => RowBit cfg.terminal.plane.rawRows (q*p)→Bool
local notation "rot" => RotorSpec.ofRates reset
local notation "R" => max 1 (max reset.bitsR (C*reset.bitsR))
local notation "cap" => NativeBranch.privateSlotCapacity G S R
local notation "atomArity" => max 8 (2^S.capGain)
local notation "old" => DescentPrimitivePalette.codec (G:=G) («s»:=s) («Z»:=S.grainAt G.b p 0) rot
local notation "dict" => DescentPrimitivePalette.dictionary («s»:=s) («Z»:=S.grainAt G.b p 0) G rot reset.menu p
local notation "seedOne" => Nat.le_max_left 1 (max reset.bitsR (C*reset.bitsR))
local notation "contents" => fun x c pay => ((leaf) c).contents cfg (K₀:=K) pay (packagePins X S.copies s x)

/-- Every accepted full candidate contributes the original seed numerator times the actual
terminal graph factor, using the native cable order on paid bits. -/
theorem wideChoice_factors (dataRoom : q*p ≤ w) (machine : sliceWidth W q piece ≤ w)
    (word : Nat.log 2 (NativeBranch.privateMax G S p)+1 ≤ w) (x : originalPins→Bool)
    (z : Old⊕DescentTerminalChipPins.Inputs K W q piece→Bool) (c : (last).Choice) (pay : Raw)
    (accepted : finalChoice dataRoom (fun _ => prior x) ((contents) x) pay z=some c) :
    TypedWiring.value chip (Sum.elim z pay) *
      ((∏ t:Unit,(2:F)^(Branch.unitExponent X G S (trace c) positive seedOne t)) *
      (∏ i,DescentTerminalChronologicalBooks.menu
        (fun bin args => bundleScalar p dict ((DescentBundleTagKeys.codec old atomArity cap p R).read bin) args)
        ((((leaf) c).keys cfg (arity:=atomArity) (groups:=cap) (stride:=R) old machine pay
          (packagePins X S.copies s x)) i))) =
    (last).weight c * ∏ v,((last).state c).graph.read ((last).state c).tables
      (((leaf) c).assignment cfg pay) (packagePins X S.copies s x) v := by
  have earlier := ((DescentTerminalProposalCheck.extend_iff _ _ _ _ c).mp accepted).1
  rw [wideChoice_weight (K:=K) X G S ordinary reset branch positive room shorten w fit base width cfg x
    (Sum.elim z pay) c earlier]
  exact congrArg ((last).weight c * ·) (normalizedLeaf_factors X G S ordinary reset branch positive room shorten
    c base width age wFit qFit qh cfg pool raw machine word pay (packagePins X S.copies s x))

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
