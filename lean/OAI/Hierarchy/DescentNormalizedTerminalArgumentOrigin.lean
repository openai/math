import OAI.Hierarchy.DescentNamedNormalizedChart
import OAI.Hierarchy.DescentNamedTerminalArgumentOrigin
import OAI.Hierarchy.DescentTerminalArchivePointers
import OAI.Hierarchy.DescentNamedPrimitivePalette
import OAI.Hierarchy.DescentNamedLeafOrder

namespace OAI
/-! # The original source names on the normalized common leaf -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open DescentTerminalGraphPositions DescentTerminalGraphVolume DescentTerminalCableOrder DescentKernelHistory
open DescentBundleHistory DescentPrimitivePalette DescentRotor DescentResetGates CorrectionBatch
open DescentTerminalBinReaddress DescentTerminalPorts Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin
  Branch.archive Branch.bundleShape

open DescentTerminalPointerIssue DescentTerminalPointerDigits DescentLocalPrivateNames

private theorem retag_pointer_origin {P U V : Type} [Fintype P] {bits : P → ℕ}
    {d p D cap N A K : ℕ} (net : Network d P bits) (v : net.Site)
    {r : BitRecipe U (Boundary net v) (boundaryWidth net v)}
    (shape : Shape p r) (remap : U → V) (positive : 0 < p) (birth : r.Node ↪ ℕ)
    (nodes : Fintype.card r.Node ≤ N) (arity : ∀ u, (shape.recipe positive).arity u ≤ A)
    (aliases : Slot (shape.recipe positive) ↪ Fin K) (rank : Boundary net v ↪ ℕ)
    (port : Attached net v ↪ ℕ) (t : CellInputs D cap N A)
    (source : DescentTerminalPointerIssue.Origin net v (shape.recipe positive) birth nodes arity aliases rank port t) :
    DescentTerminalPointerIssue.Origin net v ((shape.retag remap).recipe positive) birth nodes arity aliases rank port t :=
  by
    refine ⟨source.population, source.arities, ?_, source.cable, source.exterior⟩
    intro s h used
    let raw := shape.recipe positive
    let relabeled := (shape.retag remap).recipe positive
    let h₀ : raw.UsedWord := ⟨h.val, h.property⟩
    have reads (j : Slot raw) : read raw j = some h₀ ↔ read relabeled j = some h := by
      obtain ⟨u, i⟩ := j
      exact (read_some raw u i h₀).trans (read_some relabeled u i h).symm
    have same : firstAlias raw aliases h₀ = firstAlias relabeled aliases h := by
      apply le_antisymm
      · obtain ⟨j, atSlot, readAt⟩ := firstAlias_read relabeled aliases h
        rw [← atSlot]
        exact firstAlias_le raw aliases j h₀ ((reads j).mpr readAt)
      · obtain ⟨j, atSlot, readAt⟩ := firstAlias_read raw aliases h₀
        rw [← atSlot]
        exact firstAlias_le relabeled aliases j h ((reads j).mp readAt)
    exact (source.privateWord s h₀ used).trans
      (congrArg (fun x : Fin K => DescentOperandStateBanks.Pointer.privateWord x.val) same)

section GeneralBranch
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)



open DescentGL DescentColonies DescentExterior PinCohorts
open DescentLocalArchiveOrder DescentTerminalChronologicalBooks
attribute [local irreducible] Branch.localNodes

variable {tail N A oldNodes oldArgs : ℕ}
variable (stride : 1≤R)
local notation "raw_" => Branch.archive X G S b hp
local notation "N_" => ((Epochs.finish G hu he r).state c).graph
local notation "rawShape" => Branch.bundleShape X G S b hp stride
local notation "numbers_" => Branch.localNodes X G S b hp
local notation "oldptr_" => Reached.argumentPointer b.target (raw_).bit numbers_ rawShape hp (fun z=>z.1.val) oldArgs

private def RetaggedBranchOrigin
    (base : S.baseGroups = 2^tail) {V : Type} (rename : (raw_).bit.Tag → V)
    (v : (N_).Site) : Prop :=
  let recipe := (((rawShape).sites v).retag rename).recipe hp
  let birth := (numbers_ v).toEmbedding.trans Fin.valEmbedding
  ∀(nn : Fintype.card recipe.Node≤N)
    (aa : ∀u,recipe.arity u≤A)
    (on_ : Fintype.card recipe.Node≤oldNodes)
    (oa_ : ∀u,recipe.arity u≤oldArgs)
    (t : CellInputs b.target.placement.degree b.target.placement.cap N A) (matrix roster : ℕ)
    (_ : matrix=(matrixCode (Branch.pinSpine X G S b hp base).matrix).val)
    (_ : roster=Branch.frozenRosterCode X G S b hp base (b.target.home v))
    (_ : t.n=Fintype.card recipe.Node)
    (_ : ∀u,t.arity (row recipe
      birth nn u)=recipe.arity u)
    (_ : ∀j:Slot recipe,
      t.pointer (slot recipe
        birth nn aa j)=oldptr_ ⟨v,j.1⟩ j.2.val),
   DescentTerminalPointerIssue.Origin N_ v recipe
      birth nn aa
      (slot recipe birth on_ oa_)
      (Branch.leafOperands X G S b hp base v)
      ((Branch.densePinEquiv X G S b hp base v).toEmbedding.trans Fin.valEmbedding)
      (reindexed t (terminalPin (S.groupWidth k tail 0+k) (S.groupWidth k tail S.length+k) b.path.frozen matrix roster))

private theorem retag_branch_origin
    (base : S.baseGroups = 2^tail) {V : Type} (rename : (raw_).bit.Tag → V)
    (v : (N_).Site)
    : RetaggedBranchOrigin X G S b hp (N:=N) (A:=A) (oldNodes:=oldNodes) (oldArgs:=oldArgs) stride base rename v := by
  intro nn aa on_ oa_ t matrix roster matrixAt rosterAt pop widths physical
  apply retag_pointer_origin N_ v ((rawShape).sites v) rename hp
  exact Branch.terminal_argument_origin X G S b hp base stride v nn aa on_ oa_ t matrix roster
    matrixAt rosterAt pop widths physical
open DescentDatedPriorOperand DescentOperandStateBanks DescentPackedColony DescentSIMDLookup
open Chronology Chronology.DatePorts ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
private def RetaggedArchiveOrigin
    (base : S.baseGroups = 2^tail) {V : Type} (rename : (raw_).bit.Tag → V)
    (v : (N_).Site) (s₀ Z : ℕ) (op : RotorSpec) : Prop :=
  let recipe := (((rawShape).sites v).retag rename).recipe hp
  let birth := (numbers_ v).toEmbedding.trans Fin.valEmbedding
  let coord := Reached.NodeCells.coordinate b.target v
  ∀ (aa : ∀ u, recipe.arity u ≤ A) (on_ : Fintype.card recipe.Node ≤ oldNodes)
    (ports : DatePorts) (space : RangeRoom ports b.target (raw_).bit) {d₀ bw : ℕ},
    let x := coord.2.2.cast (congrArg (2^·) space.radix)
    let host : Fin ports.operandHosts := ⟨coord.1.val,space.hosts v⟩
    let group := coord.2.1.cast space.groups
    ∀ (label : NodeOrder.All (raw_).bit → Label G s₀ Z op)
      (flags : Fin (2^ports.venue.k) → Fin ports.nodes → Fin ports.operandHosts → Fin ports.venue.groups → ℕ)
      (prior current : Memory bw)
      (_ : ArchiveRead ports b.target (raw_).bit numbers_ space rawShape op label
        (Reached.argumentPointer b.target (raw_).bit numbers_ rawShape hp (fun z => z.1.val) ports.argumentsPerNode) flags prior)
      (config : Widths) (_ : config.nodeCapacity = some ports.nodes) (_ : ∀ f, config.pointer f = ports.operandBits)
      (_ : ports.operandBits*ports.nodes*ports.operandLanes ≤ bw) (_ : chunks ports.venue.groups ports.operandLanes = 1)
      (physA : ∀ u, recipe.arity u ≤ ports.argumentsPerNode)
      (pages : Gather.Pages (2^ports.venue.k) b.target.placement.cap A)
      (t : CellInputs b.target.placement.degree b.target.placement.cap ports.nodes A)
      (_ : ∀ (j : Slot recipe) (f : Fin 4), current ((pages.pointers f (j.2.castLE (aa j.1)) x).base+host.val) =
        prior ((previousBank ports.rangeLayout ports.archive.arguments x
          (DescentOperandStateBanks.page (f.castLE (by decide : 4≤7)) (j.2.castLE (physA j.1)))).base+host.val))
      (_ : ports.operandBits*ports.nodes*(group.val+1) ≤ d₀)
      (_ : SourceRead config (pages.source (d:=d₀) current x host) group.val t)
      (matrix roster : ℕ)
      (_ : matrix = (matrixCode (Branch.pinSpine X G S b hp base).matrix).val)
      (_ : roster = Branch.frozenRosterCode X G S b hp base (b.target.home v))
      (_ : t.n = Fintype.card recipe.Node)
      (_ : ∀ u, t.arity (row recipe birth (space.capacity v) u) = recipe.arity u),
      DescentTerminalPointerIssue.Origin N_ v recipe birth (space.capacity v) aa (slot recipe birth on_ physA)
        (Branch.leafOperands X G S b hp base v)
        ((Branch.densePinEquiv X G S b hp base v).toEmbedding.trans Fin.valEmbedding)
        (reindexed t (terminalPin (S.groupWidth k tail 0+k) (S.groupWidth k tail S.length+k) b.path.frozen matrix roster))

private theorem retag_archive_branch_origin
    (base : S.baseGroups = 2^tail) {V : Type} (rename : (raw_).bit.Tag → V)
    (v : (N_).Site) (s₀ Z : ℕ) (op : RotorSpec) :
    RetaggedArchiveOrigin X G S b hp (A:=A) (oldNodes:=oldNodes) stride base rename v s₀ Z op := by
  dsimp only [RetaggedArchiveOrigin]
  intro aa on_ ports space d₀ bw label flags prior current archive config capacity width packed single physA pages t
    hold fits read matrix roster matrixAt rosterAt pop widths
  apply retag_branch_origin X G S b hp stride base rename v (space.capacity v) aa on_ physA
    t matrix roster matrixAt rosterAt pop widths
  exact archive.terminal_live_pointers hp config capacity width packed single v aa physA pages current t
    hold fits read pop widths

end GeneralBranch

variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g W q piece : ℕ}
local notation "p" => W*piece
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0<(W*piece)) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
variable (c : (Epochs.finish G _ _ (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose).Choice)
local notation "b" => issued X G S ordinary reset branch positive room shorten c
variable (base : S.baseGroups=2^tail) (v : ((Epochs.finish G _ _ (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose).state c).graph.Site) {N A oldNodes oldArgs : ℕ}
local notation "stride_" => (Nat.le_max_left 1 (max reset.bitsR (C*reset.bitsR)))

/-- The final pointer uses the original archive name, before relabeling the gate
operations. The same rectangular private aliases and port names apply in the
normalized recipe. -/
theorem normalized_terminal_origin :
    RetaggedBranchOrigin X G S (r:=((normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose))
    (c:=c) b positive (N:=N) (A:=A) (oldNodes:=oldNodes) (oldArgs:=oldArgs) stride_ base
    (Palette.atLeaf X G S ordinary reset branch positive room shorten c).code v :=
  retag_branch_origin X G S (r:=((normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose))
    (c:=c) b positive (N:=N) (A:=A) (oldNodes:=oldNodes) (oldArgs:=oldArgs) stride_ base
    (Palette.atLeaf X G S ordinary reset branch positive room shorten c).code v

/-- Original archive rows give the normalized leaf all live names after the four raw pages are retained. -/
theorem normalized_archive_pointer_origin :
    RetaggedArchiveOrigin X G S (r:=((normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose))
    (c:=c) b positive (A:=A) (oldNodes:=oldNodes) stride_ base
    (Palette.atLeaf X G S ordinary reset branch positive room shorten c).code v
    (S.firstWidth G.b p) (S.grainAt G.b p 0) (RotorSpec.ofRates reset) :=
  retag_archive_branch_origin X G S (r:=((normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose))
    (c:=c) b positive (A:=A) (oldNodes:=oldNodes) stride_ base
    (Palette.atLeaf X G S ordinary reset branch positive room shorten c).code v
    (S.firstWidth G.b p) (S.grainAt G.b p 0) (RotorSpec.ofRates reset)

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
