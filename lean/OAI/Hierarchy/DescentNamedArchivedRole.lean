import OAI.Hierarchy.DescentNamedRoleDecoded
import OAI.Hierarchy.DescentTerminalArchivedSliceChart
import OAI.Hierarchy.DescentTerminalArchivedPrintedNode
import OAI.Hierarchy.DescentPrimitiveAtNode
import OAI.Hierarchy.DescentOriginalPaddedNodes

namespace OAI
/-! The selected terminal register directly supplies the raw role printed at every occupied venue. -/
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
set_option maxRecDepth 8192
set_option maxHeartbeats 450000
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin Branch.archive Branch.bundleShape

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
local notation "s" => S.firstWidth G.b p
local notation "Z" => S.grainAt G.b p 0
local notation "rot" => RotorSpec.ofRates reset
local notation "R" => max 1 (max reset.bitsR (C*reset.bitsR))
local notation "cap" => NativeBranch.privateSlotCapacity G S R
local notation "nodeCap" => S.epochPower^S.localTokenExponent
local notation "palette" => Palette.relabel X G S ordinary reset branch positive room shorten c
local notation "sh" => Palette.leafShape X G S ordinary reset branch positive room shorten c


open Chronology DescentDatedAddressBook DescentRetainedRangeDigits DescentTerminalSliceShelf
open DescentLocalArchiveOrder
variable {d bw : ℕ} (cpu : PhysicalReset) (dateFloor : ℕ) (incoming : cpu.DateInputs dateFloor bw)
local notation "ports" => DatePorts.reset cpu dateFloor incoming
local notation "out" => cpu.successor
local notation "M" => (out).argumentSlots
local notation "a₀" => max 8 (2^S.capGain)
local notation "colors_" => DescentPrimitivePalette.colors G s Z rot
local notation "dict" => DescentPrimitivePalette.codec (G:=G) («s»:=s) («Z»:=Z) rot
local notation "fieldBits" => DescentTerminalCombinedRole.width colors_ a₀ cap p R
local notation "A_" => (b).target.placement
local notation "L" => Columns M
local notation "B₀" => (Branch.archive X G S b positive).bit
local notation "ord₀" => Branch.localNodes X G S b positive
local notation "shape₀" => Branch.bundleShape X G S b positive (le_max_left 1 (max reset.bitsR (C*reset.bitsR)))
local notation "encoded" => Palette.atLeaf X G S ordinary reset branch positive room shorten c
local notation "cfg" => datedWidths out
variable (places : DatePorts.RangeRoom (DatePorts.reset cpu dateFloor incoming)
    (issued X G S ordinary reset branch positive room shorten c).target
    (Branch.archive X G S (issued X G S ordinary reset branch positive room shorten c) positive).bit)
    (axes : (DatePorts.reset cpu dateFloor incoming).rangeLayout=cpu.successor.rangeLayout)
    (chart : (DatePorts.reset cpu dateFloor incoming).metadataChart=cpu.successor.metadata.chart)
    (tok : cpu.successor.receiver.blocks=cpu.successor.primitive.chart.blocks)
    (argc : cpu.successor.receiver.blocks=cpu.successor.metadata.chart.blocks)
local notation "blockD" => (congrArg (2^·) places.radix).trans (congrArg DescentDatedPriorOperand.Layout.blocks axes)
local notation "published" => datedChart out (cpu.rebased dateFloor) tok argc
local notation "cables" => fun (j : Fin L) (x : DescentColonies.Block k)=>published j (x.cast blockD)
variable {j rest : ℕ} (base : S.baseGroups=2^tail) (width : S.groupWidth k tail 0+k=j+(j+rest))
    (age : 0<S.height) (start advice limit : ℕ) (lastMem original acquired : Memory bw)
local notation "ord" => Branch.leafOrder X G S b positive base width
local notation "sites_" => S.hostSize S.length
local notation "cohorts_" => S.groupCount S.length
local notation "rows_" => (2^k)*sites_
variable (i : Fin (S.hostSize S.length))
    (z : Fin ((Branch.leafOrder X G S (issued X G S ordinary reset branch positive room shorten c) positive base width).site i).nodes)
local notation "vertex_" => (ord).node i z
local notation "block_" => (A_).block vertex_
local notation "group_" => ((A_).pos vertex_).1
local notation "birth_" => (ord₀ vertex_).toEmbedding.trans Fin.valEmbedding
local notation "slot_" u:arg => (DescentTerminalChronologicalBooks.ordinal birth_ u).castLE
  (Branch.site_nodes X G S b positive age vertex_)
local notation "sizes_" => fun f : Fin 6 => fieldBits f*nodeCap*cohorts_
local notation "columns_" => fun f : Fin 6 => DescentTerminalSliceShelf.field start L d rows_ f.val
local notation "table_" => DescentTerminalRoleTables.role sizes_ columns_ advice
local notation "printer" => writePanel (d:=d) («M»:=M) («s»:=s) («Z»:=Z) (N:=nodeCap) (groups:=cohorts_) G rot a₀ cap p R cfg
local notation "output_" => DescentTerminalSliceShelf.memory start cables printer sites_ original
local notation "end_" => fence start L d rows_
local notation "fetched" => observed (n:=colors_) (A:=a₀) (G:=cap) («p»:=p) («R»:=R)
  (N:=nodeCap) («M»:=cohorts_) table_ acquired ((finProdFinEquiv (block_,i)).val:Computability.VPVNP.BurstRAM.Word bw)
local notation "rect" => physicalWidth (ports).venue.groups (out).nodes (printedBits G s Z rot) (out).nodeBits
local notation "slices" u:arg => ((sh).sites vertex_).sliceFields u
local notation "headers" u:arg => repeatFields (slices u).flatten

include chart in
/-- The last registered primitive table and three affine pages suffice for all six printed
fields of the chosen scalar. Only numeric layout, word widths and frame laws are needed. -/
theorem normalized_archived_role {ptr flags}
    (stored : DatePorts.ArchiveRead ports (b).target B₀ ord₀ places shape₀ rot
      (encoded).atNode ptr flags lastMem)
    (hostD : sites_=(ports).operandHosts) (nodeD : nodeCap=(out).nodes)
    (roleBits : printedBits G s Z rot=(out).primitive.chart.bits)
    (pitch : (ports).operandLanes=(ports).venue.groups) (rolePitch : (ports).roleLanes=(ports).venue.groups)
    (wide : rect≤bw) (covered : rect≤d) (argRoom : M<2^(out).nodeBits)
    (prior : ∀field block,(cables field block).Fits limit sites_ bw)
    (frame : ∀ a<limit,original a=lastMem a)
    (ok : ∀field block,(cables field block).Fits start sites_ bw) (off : 2^d<2^bw)
    (room_ : end_<2^bw) (fitsWord : ∀ f,sizes_ f≤bw)
    (kept : ∀ a<end_,acquired a=output_ a)
    (u : ((palette).recipe vertex_).Node) (fits : (headers u).length≤M) :
    Printed dict (DescentTerminalCombinedRole.fields (DescentTerminalCombinedRole.node fetched group_ (slot_ u))) (((palette).recipe vertex_).tag u) (slices u) :=by
  let x:=(block_).cast (congrArg (2^·) places.radix)
  let h:=i.cast hostD
  let g:=(group_).cast places.groups
  let n:Fin (out).nodes:=(slot_ u).cast nodeD
  have placed:=normalized_whereAt X G S ordinary reset branch positive room shorten c base width age i z u
  have at_ := (Reached.NodeCells.whereAt_some (b).target B₀ ord₀ block_ (slot_ u) i group_ vertex_ u).mp placed
  have hit : DatePorts.slotAt ports (b).target B₀ ord₀ places x n h g=some ⟨vertex_,u⟩:=by
    apply (Reached.NodeCells.atPhysical_some (b).target B₀ ord₀ _ _ _ _ vertex_ u).2
    exact ⟨congrArg (fun v=>v.1.val) at_.1,Fin.ext rfl,Fin.ext rfl,at_.2⟩
  have widthsEq : cfg = ⟨printedBits G s Z rot,(ports).operandBits,fun _ => (ports).operandBits⟩ := by
    change ⟨(out).primitive.chart.bits,(out).nodeBits,fun _ => (out).nodeBits⟩ = (⟨printedBits G s Z rot,(out).nodeBits,fun _ => (out).nodeBits⟩ : RawWidths)
    rw [roleBits]
  have addresses (j : Fin L) : DatePorts.archiveSliceChart ports j x = cables j block_ :=
    DatePorts.reset_slice_chart incoming axes chart tok argc j x
  exact DatePorts.ArchiveRead.printed_at_original (d:=d) ports (b).target B₀ ord₀ places
    shape₀ rot (encoded).atNode ptr flags lastMem original acquired stored cables cfg a₀ cap start advice
    x block_ i group_ (slot_ u) ⟨vertex_,u⟩ hostD nodeD places.groups widthsEq pitch rolePitch wide covered
    hit addresses (fun j => prior j block_) frame positive
    (Palette.terminal_layout X G S ordinary reset branch positive room shorten c vertex_ u)
    (normalized_role_fit X G S ordinary reset branch positive room shorten c age vertex_ u)
    argRoom fits ok off room_ fitsWord kept

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
