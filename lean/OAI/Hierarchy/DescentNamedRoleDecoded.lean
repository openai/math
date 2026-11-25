import OAI.Hierarchy.DescentNamedRolePrinted
import OAI.Hierarchy.DescentTerminalSliceSource
import OAI.Hierarchy.DescentRetainedRangeDigits
import OAI.Hierarchy.DescentReachedNodeCells
import Mathlib.Order.Interval.Finset.Fin

namespace OAI
/-! # Reached printed roles from the three archived operand range digits -/
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
set_option maxHeartbeats 1200000
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

variable {d bw : ℕ}
variable (out : DescentDatedAddressBook.ResetOutput)
local notation "M" => out.argumentSlots
local notation "a₀" => max 8 (2^S.capGain)
local notation "colors_" => DescentPrimitivePalette.colors G s Z rot
local notation "dict" => DescentPrimitivePalette.codec (G:=G) («s»:=s) («Z»:=Z) rot
local notation "fieldBits" => DescentTerminalCombinedRole.width colors_ a₀ cap p R
local notation "L" => Columns M
local notation "slices" v:arg u:arg => ((sh).sites v).sliceFields u
local notation "headers" v:arg u:arg => repeatFields (slices v u).flatten


private theorem slice_eq {left right : SliceCode} (h : left.start=right.start) (stride : left.stride=right.stride)
    (c : left.count=right.count) : left=right := by
  cases left
  cases right
  simp_all

variable (start advice : ℕ) (cfg : RawWidths) (original acquired : Memory bw)

section Reached

variable {j rest : ℕ} (base : S.baseGroups=2^tail) (width : S.groupWidth k tail 0+k=j+(j+rest))
    (age : 0<S.height)
local notation "ord" => Branch.leafOrder X G S b positive base width
local notation "sites_" => S.hostSize S.length
local notation "cohorts_" => S.groupCount S.length
local notation "blocks_" => 2^k
local notation "rows_" => blocks_*sites_
local notation "A_" => (b).target.placement
variable (cables : Fin (Columns out.argumentSlots)→Fin (2^k)→Gather.Address)
local notation "sizes_" => fun f : Fin 6 => fieldBits f*nodeCap*cohorts_
local notation "columns_" => fun f : Fin 6 => DescentTerminalSliceShelf.field start L d rows_ f.val
local notation "table_" => DescentTerminalRoleTables.role sizes_ columns_ advice
local notation "printer" => writePanel (d:=d) («M»:=M) («s»:=s) («Z»:=Z) (N:=nodeCap) (groups:=cohorts_) G rot a₀ cap p R cfg
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
  (N:=nodeCap) («M»:=cohorts_) table_ acquired ((finProdFinEquiv (block_,i)).val:Computability.VPVNP.BurstRAM.Word bw)

private theorem ordinal_equiv_value {Y : Type} [Fintype Y] (e:Y≃Fin (Fintype.card Y)) (u:Y) :
    (DescentTerminalChronologicalBooks.ordinal (e.toEmbedding.trans Fin.valEmbedding) u).val=(e u).val := by
  classical
  rw [DescentTerminalChronologicalBooks.ordinal_val]
  let xs := Finset.univ.filter (fun a:Y=>(e a).val<(e u).val)
  change xs.card=(e u).val
  have mapped : xs.map e.toEmbedding=Finset.Iio (e u) := by
    ext t
    constructor
    · intro ht
      obtain ⟨a,ha,eq_⟩:=Finset.mem_map.mp ht
      subst t
      exact Finset.mem_Iio.mpr (Finset.mem_filter.mp ha).2
    · intro ht
      refine Finset.mem_map.mpr ⟨e.symm t,?_,e.apply_symm_apply t⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,by simpa using Finset.mem_Iio.mp ht⟩
  calc
    xs.card=(xs.map e.toEmbedding).card := by rw [Finset.card_map]
    _=(e u).val := by rw [mapped,Fin.card_Iio]

/-- At a live terminal cell the physical inverse selects the same graph vertex
and primitive node which furnished the compressed role-table slot. -/
theorem normalized_whereAt (u : ((palette).recipe vertex_).Node) :
    Reached.NodeCells.whereAt (b).target (Branch.archive X G S b positive).bit
      (Branch.localNodes X G S b positive) block_ (slot_ u) i group_=some ⟨vertex_,u⟩ := by
  apply Reached.NodeCells.whereAt_at
  · change ((ord).home vertex_,group_,block_)=(i,group_,block_)
    exact congrArg (fun h=>(h,group_,block_)) (((ord).nodes i).symm z).property
  · exact ordinal_equiv_value (Branch.localNodes X G S b positive vertex_) u

theorem normalized_previous_decoded (u : ((palette).recipe vertex_).Node)
    (ok : ∀ field block,(cables field block).Fits start sites_ bw) (off : 2^d<2^bw)
    (room_ : end_<2^bw) (fitsWord : ∀ f,sizes_ f≤bw)
    (kept : ∀ j<end_,acquired j=out_ j)
    (fit : (headers vertex_ u).length≤M)
    (hostDim : sites_=out.receiver.hosts) (groupDim : cohorts_=out.receiver.groups)
    (nodeDim : nodeCap=out.nodes)
    (T : Fin out.receiver.hosts→Fin out.receiver.groups→Cell (out.primitive.chart.bits*out.nodes))
    (Q : Fin out.receiver.hosts→Fin out.receiver.groups→Cell (out.nodeBits*out.nodes))
    (sp : Fin 3→Fin M→Fin out.receiver.hosts→Fin out.receiver.groups→Cell (out.nodeBits*out.nodes))
    (decoded : Decoded out (i.cast hostDim) ((group_).cast groupDim) ((slot_ u).cast nodeDim) T Q sp (input_ u))
    (token : ((encode out.primitive.chart.bits out.nodes).symm
      (T (i.cast hostDim) ((group_).cast groupDim)) ((slot_ u).cast nodeDim)).val=
        ((dict).store (((palette).recipe vertex_).tag u)).val+1)
    (count : ((encode out.nodeBits out.nodes).symm
      (Q (i.cast hostDim) ((group_).cast groupDim)) ((slot_ u).cast nodeDim)).val=
        (((sh).sites vertex_).recipe positive).arity u)
    (digits : classify G p s (((palette).recipe vertex_).tag u)=.rotor →
      ∀(j:Fin (headers vertex_ u).length) (f:Fin 3),
        ((encode out.nodeBits out.nodes).symm (sp f (j.castLE fit) (i.cast hostDim)
          ((group_).cast groupDim)) ((slot_ u).cast nodeDim)).val=
          DescentRetainedRangeDigits.atSlot ((sh).sites vertex_) u j.val f) :
    Printed dict (DescentTerminalCombinedRole.fields (n:=colors_) (A:=a₀) (G:=cap) («p»:=p) («R»:=R)
      (node (n:=colors_) (A:=a₀) (G:=cap) («p»:=p) («R»:=R) fetched group_ (slot_ u))) (((palette).recipe vertex_).tag u) (slices vertex_ u) := by
  apply normalized_previous_role X G S ordinary reset branch positive room shorten c start advice cfg
    original acquired base width age cables i z u ok off room_ fitsWord kept
    (decoded.token.trans token) ((decoded.count.trans count).trans (emitted_length ((sh).sites vertex_) u positive).symm) fit
  intro rotor j
  have lane (f : Fin 3) := (digits rotor j f).trans
    (DescentRetainedRangeDigits.atSlot_lt ((sh).sites vertex_) u f j)
  apply slice_eq
  · exact (decoded.start (j.castLE fit)).trans (lane 0)
  · exact (decoded.stride (j.castLE fit)).trans (lane 1)
  · exact (decoded.words (j.castLE fit)).trans (lane 2)

end Reached

end
end Hierarchy.DescentSixParty.SeedNamed
end OAI

open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin Branch.archive Branch.bundleShape
