import OAI.Hierarchy.DescentMountedGoodRotor
import OAI.Hierarchy.DescentOriginalRotorCount

namespace OAI
/-! # Three physical range fields on a mounted good router -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu
open DescentKernelHistory DescentPhysicalSplit DescentResetGates DescentLaneGates DescentFallbackItemSelect
open DescentSIMDLookup DescentRetainedRangeDigits DescentBundleHistory DescentResetPublicOperandBook
open DescentResetOperandSetup DescentRotor DescentRouterSlots DescentBatchedNodeOrder
open DescentDenseHostOrder LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1400000
open private transportCircuit from OAI.Hierarchy.DescentInstalledNames
variable {a : PhysicalReset} {z : a.Atlas} {roots : a.RootInputs} (menu : OperandMenu z roots)
local notation "cfg" => publicOperands z roots menu.payload
local notation "C" => a.successor.setup
local notation "R" => (cfg).rotor
variable {U : ℕ} (name : Fin U→Fin a.successor.setup.placement.sparse)
    (Y : Fin (a.successor.setup.retained.outputs*a.successor.setup.placement.shapes)→Fin a.successor.setup.placement.oldHosts→
      Fin (a.successor.setup.placement.groups*a.successor.setup.placement.blocks)→Cell a.successor.setup.retained.bits)
    (j : Fin a.successor.setup.retained.outputs) (blk : Fin a.successor.setup.placement.blocks)
    (h : Fin a.successor.setup.placement.newHosts) (g : Fin a.successor.setup.placement.groups)
    (x : (publicOperands z roots menu.payload).Data a.successor.middle.rotorBits) (arg : Fin (publicOperands z roots menu.payload).args) (node : Fin (publicOperands z roots menu.payload).nodes)
    (blank : ((publicOperands z roots menu.payload).oldConfig.header ((publicOperands z roots menu.payload).basic x) 0).val=0 → ((publicOperands z roots menu.payload).reg x 1).val=0)
    (physical : ∀hv : h.val<U,((publicOperands z roots menu.payload).oldConfig.header ((publicOperands z roots menu.payload).basic x) 0).val≠0 →
      ((publicOperands z roots menu.payload).reg x 3).val=(a.successor.setup.placement.shape (name ⟨h.val,hv⟩)).val)
    (fresh : ∀hv : h.val<U,menu.keep (a.successor.setup.placement.shape (name ⟨h.val,hv⟩))=false)
local notation "mouth" => finProdFinEquiv (arg,node)
local notation "word" f:arg => menu.spanValue name Y j blk h g x mouth (page f) blank physical
local notation "prv" f:arg => (R).flatReg z.board (cfg).multiplicity (cfg).grain (cfg).split node.val arg.val
   (page f).succ ((cfg).reg x)
local notation "surface" f:arg => ((cfg).column z.board (C).fieldBits (some (page f)) mouth x).val

open DescentChosenRouter DescentMixedRouter DescentBatchedBank DescentBaseProfile
variable {V I H A K : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A] [Field K]
  {k unit N : ℕ} (placement : DescentChosenRouter.Placement V I H A k (2^a.successor.middle.rotorBits))
  (hw : 0<(publicOperands z roots menu.payload).rotor.packet) (pay : ℝ)
  (hardware : Hardware (K:=K) (C₀:=(publicOperands z roots menu.payload).multiplicity) (u:=unit) placement z.board hw pay)
  (key : I↪Fin N) (d : ℕ) (hp : 0<(publicOperands z roots menu.payload).grain) (fit : unit=(publicOperands z roots menu.payload).rotor.batches*(publicOperands z roots menu.payload).grain)
  (side : Bool) (rootId : placement.Good)
local notation "sel" => selected placement z.board hw pay hardware
local notation "bank" => DescentMixedRouter.network z.board hw unit placement.contact placement.input placement.site
  placement.owner placement.align sel d
local notation "site_" => (.inl rootId : placement.Site)
local notation "prg" => sizedProgram z.board hw unit (R).batches (cfg).grain hp fit placement.contact placement.input
  placement.site placement.owner placement.align key d sel
local notation "ord" => sizedOrder z.board hw (R).batches (cfg).grain hp placement.contact placement.input
  placement.site placement.owner placement.align key d unit fit sel
local notation "head_" => head placement side rootId
local notation "tail_" => tail placement side rootId
local notation "src" => DescentChosenRouter.source placement side rootId
local notation "dst" => DescentChosenRouter.target placement side rootId
local notation "E" => {i : I // placement.owner side (placement.contact i)=site_}
local notation "chron" => (Function.Embedding.subtype (fun i=>placement.owner side (placement.contact i)=site_)).trans key
local notation "fund" => (fit ▸ hardware : Hardware (K:=K) (C₀:=(cfg).multiplicity)
  (u:=(R).batches*(cfg).grain) placement z.board hw pay) side rootId
variable (actor : (DescentCommonPalette.rotor z.board).Site)
local notation "installed" => DescentCommonPalette.rotorSiteEquiv z.board d
  (selectedRotorLayers placement z.board hw pay hardware side rootId) (cfg).multiplicity (R).packet unit
local notation "sizedHardware" => (fit ▸ hardware : Hardware (K:=K) (C₀:=(cfg).multiplicity)
  (u:=(R).batches*(cfg).grain) placement z.board hw pay)
local notation "sized" => DescentCommonPalette.rotorSiteEquiv z.board d
  (selectedRotorLayers placement z.board hw pay sizedHardware side rootId) (cfg).multiplicity (R).packet ((R).batches*(cfg).grain)
local notation "itemEnum" => @Subtype.fintype I (fun e => placement.owner side (placement.contact e) = .inl rootId)
  (fun _ => Classical.propDecidable _) inferInstance
local notation "chip" => (transportCircuit (b:=itemEnum) (G:=z.board) (hw:=hw) (pay:=pay) (sizedHardware side rootId))
local notation "venue" => (⟨(side,site_),installed actor⟩ : (bank).Site)
local notation "shapeAt" mult:arg => ofProgram (fun e=>boundaryWidth bank venue e/(cfg).grain) mult hp (prg venue)

include fresh in
theorem mounted_rotor_span (multiple : ∀e,boundaryWidth bank venue e=boundaryWidth bank venue e/(cfg).grain*(cfg).grain)
    (gate : (prg venue).Node)
    (numbered : node.val=(ord venue gate).val)
    (actorShape : ↥(roster z.board (R).residual (R).depth)) (key₀ : DescentResetHostSize.Code (R).residual)
    (depth : ((cfg).reg x 1).val=key₀.val.1+1) (safe : ((cfg).reg x 2).val%2=0)
    (seen : ((cfg).reg x 3).val=(localRank z.board (R).residual (R).depth actorShape).val)
    (headSeen : ((cfg).oldConfig.header ((cfg).basic x) 2).val=(localRank z.board (R).residual (R).depth actorShape).val)
    (good : actorShape.val=.good side ((),key₀.val.2) actor)
    (measured : DescentRecordedRotorLayers.layers a.successor.middle.rotorBits (R).packet (R).gain ((cfg).reg x 0).val=(fund).layers)
    (seats : (fund).layers*(R).batches≤(R).addresses) (axis : Fin 3) (fitField : atSlot (shapeAt multiple) gate arg.val axis<2^(C).fieldBits)
    (slots : E↪Fin (cfg).oldConfig.count)
    (present : ∀e,(cfg).endpoints side key₀ x (slots e)=some (src e,dst e))
    (missing : ∀j,(¬∃e,slots e=j)→(cfg).endpoints side key₀ x j=none)
    (sorted : ∀e₁ e₂ : E,before ((cfg).oldItem x side) (slots e₁) (slots e₂) ↔ chron e₁<chron e₂)
    (traffic : (cfg).traffic x side key₀=DescentBaseProfile.matrixOfBundles src dst)
    (room : 2<2^(C).fieldBits) :
    (word axis).val=atSlot (shapeAt multiple) gate arg.val axis:=by
  let digit:=mountedGoodNode placement z.board hw pay hardware key d (R).batches (cfg).grain hp fit side rootId actor gate
  obtain ⟨localWidth,read⟩:=mountedGoodRange placement z.board hw pay hardware key d (R).batches (cfg).grain hp fit
    side rootId actor multiple gate
  have number:=mountedGoodIndex placement z.board hw pay hardware key d (R).batches (cfg).grain hp fit side rootId actor gate
  have atActor : (DescentCommonPalette.rotorSiteEquiv z.board d
      (selectedRotorLayers placement z.board hw pay sizedHardware side rootId) (cfg).multiplicity (R).packet ((R).batches*(cfg).grain)).symm (sized actor) = actor :=
    (sized).symm_apply_apply actor
  have placed : actorShape.val = .good side ((),key₀.val.2) ((sized).symm (sized actor)) := by
    rw [atActor]
    exact good
  have resized := selectedRotorLayers_eq placement z.board hw pay sizedHardware side rootId
  have seatsOnChip : selectedRotorLayers placement z.board hw pay sizedHardware side rootId *
      (R).batches ≤ (R).addresses :=
    (congrArg (fun layers => layers*(R).batches ≤ (R).addresses) resized).mpr seats
  have trafficOnChip : (cfg).traffic x side key₀ = @DescentBaseProfile.matrixOfBundles
      (Cells placement side rootId) itemEnum _ src dst :=
    traffic.trans (congrArg (fun en : Fintype (Cells placement side rootId) =>
      @DescentBaseProfile.matrixOfBundles (Cells placement side rootId) en _ src dst) (Subsingleton.elim _ _))
  rw [read]
  exact menu.physical_rotor_span name Y j blk h g x arg node blank physical fresh d hp placement.contact
    placement.input placement.site placement.owner placement.align side site_ head_ tail_ chip key (sized actor) digit
    localWidth (numbered.trans number) actorShape key₀ depth safe seen headSeen placed (measured.trans resized.symm) seatsOnChip axis
    ((read arg.val axis) ▸ fitField) slots present missing sorted trafficOnChip room

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI
