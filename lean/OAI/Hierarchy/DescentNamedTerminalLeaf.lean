import OAI.Hierarchy.DescentNamedLeafOrder
import OAI.Hierarchy.DescentNamedLeafPurchase
import OAI.Hierarchy.DescentNamedPrivateSlots
import OAI.Hierarchy.DescentNamedPrimitivePalette
import OAI.Hierarchy.DescentNamedTerminalArity
import OAI.Hierarchy.DescentNamedUnitExponent
import OAI.Hierarchy.DescentTerminalBranchLibrary

namespace OAI
/-! # The terminal leaf of the physically selected common history -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open DescentTerminalGraphPositions DescentTerminalGraphVolume DescentTerminalCableOrder DescentKernelHistory
open DescentBundleHistory DescentPrimitivePalette DescentRotor DescentResetGates CorrectionBatch
open DescentTerminalBinReaddress DescentTerminalPorts Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin
attribute [local irreducible] Branch.archive Branch.bundleShape

variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g W q piece : ℕ}
local notation "p" => W*piece
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0<W*piece) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "last" => Epochs.finish G _ _ (cert).choose
variable (c : (Epochs.finish G _ _ (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose).Choice)
local notation "b" => issued X G S ordinary reset branch positive room shorten c
local notation "world" => (last).state c
local notation "net" => (world).graph
local notation "s" => S.firstWidth G.b p
local notation "Z" => S.grainAt G.b p 0
local notation "rot" => RotorSpec.ofRates reset
local notation "U" => Label G s Z rot
local notation "R" => max 1 (max reset.bitsR (C*reset.bitsR))
local notation "cap" => NativeBranch.privateSlotCapacity G S R
local notation "nodeCap" => S.epochPower^S.localTokenExponent
local notation "venues" => S.groupCount S.length*2^k
local notation "palette" => Palette.relabel X G S ordinary reset branch positive room shorten c
local notation "sh" => Palette.leafShape X G S ordinary reset branch positive room shorten c
local notation "archive" => Branch.archive X G S b positive

variable {j rest : ℕ} (base : S.baseGroups=2^tail) (width : S.groupWidth k tail 0+k=j+(j+rest))
variable (age : 0<S.height) (wFit : NativeBranch.binLimit (k:=k) S ≤ W)
  (qFit : NativeBranch.localLimit G S ≤ q) (qh : 0<q)
local notation "ord" => Branch.leafOrder X G S b positive base width
local notation "seedOne" => (Nat.le_max_left 1 (max reset.bitsR (C*reset.bitsR)))

/-- Keep the caller's physical arena shape and install the two common row capacities
that follow from the normalized terminal income. Both numbers precede the choice. -/
def buyLeafRows (cfg : DescentTerminalCompiledPrefix.Shape) : DescentTerminalCompiledPrefix.Shape :=
  {cfg with terminal:={cfg.terminal with pool:=terminalPool X G S (W*piece) q W n h C f g
                                         plane:={cfg.terminal.plane with rawRows:=terminalRawRows X G S (W*piece) q n h C f g}}}

variable (cfg : DescentTerminalCompiledPrefix.Shape)
variable (pool : terminalPool X G S (W*piece) q W n h C f g ≤ cfg.terminal.pool)
variable (raw : terminalRawRows X G S (W*piece) q n h C f g ≤ cfg.terminal.plane.rawRows)

local notation "actualOrder" => DescentTerminalCableOrder.order (world).graph (b).target.home (b).target.order
  (W*piece) (Branch.leafExternal X G S b positive base width)
  (((b).target.placement.site (b).target.vertex (b).target.valid.coordinates).trans Fin.valEmbedding)
  (Branch.leafOperands X G S b positive base)

set_option maxHeartbeats 700000 in
/-- The scalar circuit, original exterior order, stable cable order and argument
aliases come from one and the same selected native history. -/
def normalizedLeaf : DescentTerminalEmitter.Branch.Leaf cfg world (b).target U W q piece cap nodeCap cap venues where
  home := (b).target.home
  native := (b).target.order
  external := Branch.leafExternal X G S b positive base width
  nodes := ((b).target.placement.site (b).target.vertex (b).target.valid.coordinates).trans Fin.valEmbedding
  ops := Branch.leafOperands X G S b positive base
  bit := (palette).recipe
  shape := (sh).sites
  hp := positive
  birth v := (Branch.localNodes X G S b positive v).toEmbedding.trans Fin.valEmbedding
  hidden v :=
    (DescentLocalPrivateNames.firstAlias (((sh).sites v).recipe positive)
      (Branch.privateSlot X G S b positive seedOne age branch v)).trans Fin.valEmbedding
  wp := Nat.pos_of_mul_pos_right positive
  qp := qh
  space := (issued_purchase X G S ordinary reset branch positive room shorten c q W qh
    (Nat.pos_of_mul_pos_right positive) actualOrder rfl).trans pool
  countsFit := Branch.operand_count_fit X G S b positive seedOne age branch
  atoms := Branch.site_nodes X G S b positive age
  refs := Branch.arguments_fit X G S b positive seedOne age branch
  vertsFit := (b).target.occurrence_bound
  fit i := (Branch.final_rows X G S b positive qFit qh ord rfl i).trans wFit
  volume := Nat.le_trans (@issued_volume F _ cp P X G S k cut tail n h C f g (W*piece) ordinary reset branch positive room shorten c q qh) (Nat.mul_le_mul_right (q*(W*piece)) raw)

local notation "leaf" => normalizedLeaf X G S ordinary reset branch positive room shorten c base width age
  wFit qFit qh cfg pool raw

theorem leaf_unitExponent (_unit : Unit) :
    Branch.unitExponent X G S b positive seedOne _unit=(leaf).debt cfg := rfl

include qFit in
theorem leaf_small (i : Fin (S.hostSize S.length)) (v : Fin ((ord).site i).nodes) : ((ord).site i).arity v ≤ q :=
  (Branch.final_slots X G S b positive ((ord).node i v)).trans qFit

include age in
theorem leaf_groups (v : (net).Site) (u : ((palette).recipe v).Node) : (∑j,((sh).sites v).groups u j) ≤ cap := by
  calc
    _ ≤ ∑j,∑g,(((sh).sites v).chunk u j g).count := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ = ∑_ : Fin (((sh).sites v).groups u j),(1:ℕ) := by simp
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro g _
          have bound:=(((sh).sites v).chunk u j g).fits ⟨0,positive⟩
          exact Nat.succ_le_of_lt (Nat.zero_lt_of_lt bound)
    _ ≤ _ := Branch.arguments_fit X G S b positive seedOne age branch v u

local notation "old" => DescentPrimitivePalette.codec (G:=G) («s»:=s) («Z»:=Z) rot
local notation "dict" => DescentPrimitivePalette.dictionary («s»:=s) («Z»:=Z) G rot reset.menu p
local notation "atomArity" => max 8 (2^S.capGain)

set_option maxHeartbeats 650000 in
theorem normalizedLeaf_factors {bitsW:ℕ} (machine : sliceWidth W q piece ≤ bitsW)
    (word : Nat.log 2 (NativeBranch.privateMax G S p)+1 ≤ bitsW)
    (pay : RowBit cfg.terminal.plane.rawRows (q*p)→Bool) (outer : Ports (fun _ : (Σ _:Fin S.copies,
        Fin (Fintype.card (Port P X.width)))=>s*1)) :
    (∏t:Unit,(2:F)^(Branch.unitExponent X G S b positive seedOne t))*
      (∏i,DescentTerminalChronologicalBooks.menu
        (fun j args=>bundleScalar p dict ((DescentBundleTagKeys.codec old atomArity cap p R).read j) args)
        (((leaf).keys cfg (arity:=atomArity) (groups:=cap) (stride:=R) old machine pay outer) i))=
      ∏v,(net).read (world).tables ((leaf).assignment cfg pay) outer v := by
  apply (leaf).factors cfg old machine
  · exact fun i v=>(Branch.final_slots X G S b positive ((ord).node i v)).trans qFit
  · exact Palette.correct X G S ordinary reset branch positive room shorten c
  · exact Palette.labels X G S ordinary reset branch positive room shorten c
  · exact Branch.node_arity X G S b positive
  · exact leaf_groups X G S ordinary reset branch positive room shorten c age
  · exact (sh).stride
  · rw [← leaf_unitExponent X G S ordinary reset branch positive room shorten c base width age wFit qFit qh cfg pool raw ()]
    exact Branch.unitExponent_lt X G S b positive seedOne word

/-- The calibrated scalar capacities can be used definitionally in a shape,
without a world-dependent choice of any row counter. -/
def purchasedLeaf (seed : DescentTerminalCompiledPrefix.Shape) :=
  normalizedLeaf X G S ordinary reset branch positive room shorten c base width age wFit qFit qh
    (buyLeafRows (W:=W) (q:=q) (piece:=piece) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) X G S seed)
    (Nat.le_refl _) (Nat.le_refl _)


end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
