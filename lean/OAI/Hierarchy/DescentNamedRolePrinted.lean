import OAI.Hierarchy.DescentNamedTerminalSliceLayout
import OAI.Hierarchy.DescentNamedTerminalLeaf
import OAI.Hierarchy.DescentTerminalSliceMachine
import OAI.Hierarchy.DescentTerminalPrintedNode
import OAI.Hierarchy.DescentTerminalRoleTables

namespace OAI
/-! # The six physical primitive fields of the reached named node -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open DescentTerminalGraphPositions DescentTerminalGraphVolume DescentTerminalCableOrder DescentKernelHistory
open DescentBundleHistory DescentPrimitivePalette DescentRotor DescentResetGates CorrectionBatch
open DescentTerminalBinReaddress DescentTerminalPorts Computability.BorderVNP.Crossing
open DescentTerminalEmitter DescentTerminalEmitter.Branch DescentTerminalChipRuntime
open DescentTerminalVertexFields DescentTerminalHeaderScatter DescentTerminalSiteShelves
open DescentTerminalScalarTransposes DescentTerminalDenseWindow DescentTerminalRecipeRows
open DescentTerminalScalarPadded DescentTerminalCompiledPrefix DescentEpochTagKeys
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open DescentTerminalSliceRuns DescentTerminalCombinedRole DescentSIMDLookup DescentPackedColony
open DescentTerminalPointerDigits DescentOperandStateBanks
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false

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
local notation "s" => S.firstWidth G.b p
local notation "Z" => S.grainAt G.b p 0
local notation "rot" => RotorSpec.ofRates reset
local notation "U" => Label G s Z rot
local notation "R" => max 1 (max reset.bitsR (C*reset.bitsR))
local notation "cap" => NativeBranch.privateSlotCapacity G S R
local notation "nodeCap" => S.epochPower^S.localTokenExponent
local notation "palette" => Palette.relabel X G S ordinary reset branch positive room shorten c
local notation "sh" => Palette.leafShape X G S ordinary reset branch positive room shorten c

variable {N groups blocks hosts M d bw : ℕ}
local notation "a₀" => max 8 (2^S.capGain)
local notation "colors_" => DescentPrimitivePalette.colors G s Z rot
local notation "dict" => DescentPrimitivePalette.codec (G:=G) («s»:=s) («Z»:=Z) rot
local notation "fieldBits" => DescentTerminalCombinedRole.width colors_ a₀ cap p R
local notation "widths" => fun f : Fin 6 => fieldBits f*N*groups
local notation "L" => Columns M
local notation "rows" => blocks*hosts

/-- Role fit at the original chosen node, including the number of scalar operands,
the count of grouped slices, and the greatest stride of each issued slice. -/
theorem normalized_role_fit (age : 0<S.height) (v : (world).graph.Site) (u : ((palette).recipe v).Node) :
    DescentBundleTagKeys.Fits dict a₀ cap p R
      ((((palette).recipe v).tag u),((sh).sites v).sliceFields u) := by
  apply (congrArg (DescentBundleTagKeys.Fits dict a₀ cap p R) (Shape.tag_fields positive ((sh).sites v) u)).mp
  apply DescentTerminalBundleMenu.tag_fits positive ((sh).sites v) dict u
  · exact DescentPrimitivePalette.all_fit rot _
  · exact Branch.node_arity X G S b positive v u
  · exact leaf_groups X G S ordinary reset branch positive room shorten c age v u
  · exact (sh).stride v u

variable (start advice : ℕ) (cfg : RawWidths) (chart : Fin (Columns M)→Fin blocks→Gather.Address)
    (original acquired : Memory bw)
local notation "rawBank" => fun f : Fin 6 => DescentTerminalSliceShelf.field start L d rows f.val
local notation "shelf" => DescentTerminalRoleTables.role widths rawBank advice
local notation "write_" => writePanel (d:=d) (M:=M) («s»:=s) («Z»:=Z) (N:=N) (groups:=groups) G rot a₀ cap p R cfg
local notation "before_" => DescentTerminalSliceShelf.memory start chart write_ hosts original
local notation "floor_" => DescentTerminalSliceShelf.fence start L d rows

variable (block : Fin blocks) (shop : Fin hosts) (group : Fin groups) (slot : Fin N)
local notation "row_" => finProdFinEquiv (block,shop)
local notation "inputs" => DescentTerminalSliceShelf.seen (d:=d) chart original block shop
local notation "raw_" => extract cfg inputs group slot
local notation "view_" => observed (n:=colors_) (A:=a₀) (G:=cap) («p»:=p) («R»:=R)
  (N:=N) (M:=groups) shelf acquired ((row_).val:Computability.VPVNP.BurstRAM.Word bw)
local notation "slices" v:arg u:arg => ((sh).sites v).sliceFields u
local notation "headers" v:arg u:arg => repeatFields (slices v u).flatten

set_option maxHeartbeats 400000 in
/-- The actual six-role program writes the six packed physical columns in block-major
order. Reading the reached chronological node after the protected prefix yields the
operand grouping selected on its original seed, ordinary, relay, or rotor date. -/
theorem normalized_role_printed (age : 0<S.height) (v : (world).graph.Site) (u : ((palette).recipe v).Node)
    (ok : ∀j x,(chart j x).Fits start hosts bw) (off : 2^d<2^bw) (room_ : floor_<2^bw)
    (fitsWord : ∀ f,widths f≤bw)
    (kept : ∀ j<floor_,acquired j=before_ j)
    (token : (raw_).token=((dict).store (((palette).recipe v).tag u)).val+1)
    (live : (raw_).live=(headers v u).length) (fits : (headers v u).length≤M)
    (spans : classify G p s (((palette).recipe v).tag u)=.rotor → ∀ j:Fin (headers v u).length,(raw_).header (j.castLE fits)=(headers v u).get j) :
    Printed dict (DescentTerminalCombinedRole.fields (n:=colors_) (A:=a₀) (G:=cap) («p»:=p) («R»:=R) (node (n:=colors_) (A:=a₀) (G:=cap) («p»:=p) («R»:=R) view_ group slot)) (((palette).recipe v).tag u) (slices v u) := by
  exact printed_at_node G rot a₀ cap p R start advice cfg chart original acquired block shop group slot
    positive ((sh).sites v) u (((palette).recipe v).tag u)
    (Palette.terminal_layout X G S ordinary reset branch positive room shorten c v u)
    (normalized_role_fit X G S ordinary reset branch positive room shorten c age v u)
    ok off room_ fitsWord kept token live fits spans

section Reached

variable {j rest : ℕ} (base : S.baseGroups=2^tail) (width : S.groupWidth k tail 0+k=j+(j+rest))
    (age : 0<S.height)
local notation "ord" => Branch.leafOrder X G S b positive base width
local notation "sites_" => S.hostSize S.length
local notation "cohorts_" => S.groupCount S.length
local notation "blocks_" => 2^k
local notation "rows_" => blocks_*sites_
local notation "A_" => (b).target.placement
variable (cables : Fin (Columns M)→Fin (2^k)→Gather.Address)
local notation "sizes_" => fun f : Fin 6 => fieldBits f*nodeCap*cohorts_
local notation "columns_" => fun f : Fin 6 => DescentTerminalSliceShelf.field start L d rows_ f.val
local notation "table_" => DescentTerminalRoleTables.role sizes_ columns_ advice
local notation "printer" => writePanel (d:=d) (M:=M) («s»:=s) («Z»:=Z) (N:=nodeCap) (groups:=cohorts_) G rot a₀ cap p R cfg
local notation "out_" => DescentTerminalSliceShelf.memory start cables printer sites_ original
local notation "end_" => DescentTerminalSliceShelf.fence start L d rows_
variable (i : Fin (S.hostSize S.length))
    (z : Fin ((Branch.leafOrder X G S (issued X G S ordinary reset branch positive room shorten c) positive base width).site i).nodes)
local notation "vertex_" => (ord).node i z
local notation "block_" => (A_).block vertex_
local notation "group_" => ((A_).pos vertex_).1
local notation "rawAt" => DescentTerminalSliceShelf.seen (d:=d) cables original block_ i
local notation "birth_" => (Branch.localNodes X G S b positive vertex_).toEmbedding.trans Fin.valEmbedding
local notation "slot_" u:arg => (DescentTerminalChronologicalBooks.ordinal birth_ u).castLE
  (Branch.site_nodes X G S b positive age vertex_)
local notation "input_" u:arg => extract cfg rawAt group_ (slot_ u)
local notation "fetched" => observed (n:=colors_) (A:=a₀) (G:=cap) («p»:=p) («R»:=R)
  (N:=nodeCap) (M:=cohorts_) table_ acquired ((finProdFinEquiv (block_,i)).val:Computability.VPVNP.BurstRAM.Word bw)

set_option maxHeartbeats 500000 in
/-- At a reached site all three coordinates come from its original placement.
This is the scalar-role premise of the earlier-operand readback at that site. -/
theorem normalized_previous_role (u : ((palette).recipe vertex_).Node)
    (ok : ∀ field block,(cables field block).Fits start sites_ bw) (off : 2^d<2^bw)
    (room_ : end_<2^bw) (fitsWord : ∀ f,sizes_ f≤bw)
    (kept : ∀ j<end_,acquired j=out_ j)
    (token : (input_ u).token=((dict).store (((palette).recipe vertex_).tag u)).val+1)
    (live : (input_ u).live=(headers vertex_ u).length) (fits : (headers vertex_ u).length≤M)
    (spans : classify G p s (((palette).recipe vertex_).tag u)=.rotor → ∀ j:Fin (headers vertex_ u).length,
      (input_ u).header (j.castLE fits)=(headers vertex_ u).get j) :
    Printed dict (DescentTerminalCombinedRole.fields (n:=colors_) (A:=a₀) (G:=cap) («p»:=p) («R»:=R) (node (n:=colors_) (A:=a₀) (G:=cap) («p»:=p) («R»:=R) fetched group_ (slot_ u))) (((palette).recipe vertex_).tag u) (slices vertex_ u) :=
  normalized_role_printed X G S ordinary reset branch positive room shorten c start advice cfg cables
    original acquired block_ i group_ (slot_ u) age vertex_ u ok off room_ fitsWord kept token live fits spans

end Reached

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
