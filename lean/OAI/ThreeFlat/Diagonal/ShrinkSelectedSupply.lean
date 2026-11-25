import OAI.ThreeFlat.Diagonal.ShrinkSelectedGeometry
import OAI.ThreeFlat.Diagonal.ShrinkSupplyNativeWords
import OAI.ThreeFlat.Diagonal.ShrinkSupplyRequestFields

namespace OAI
/-! # The compiled supply lookup at the selected history's thirteen-register frame -/
namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalPinsExpr Computability.VPVNP.Compression CompressorPacking
open Native Native.ShrinkStage Native.ShrinkStage.Resident Native.Placement Native.Graph LinearAlgebra.SpectralBooks MotifKernel
open NavigationDirectory NavigationPass PhysicalShrink ShrinkStageNav
open scoped Classical Fin.NatCast
noncomputable section
@[instance_reducible] private noncomputable def selectedSiteDecidableEq {base tag lane : Type} :
    DecidableEq (Computability.VPVNP.Compression.Site base tag lane) := by
  classical
  infer_instance

attribute [local instance 2000] selectedSiteDecidableEq
open private rawConditions from OAI.ThreeFlat.Diagonal.PhysicalShrinkSuccessor
open private palette_two from OAI.ThreeFlat.Diagonal.PhysicalShrinkPrefix
set_option quotPrecheck false
variable {F : Type} [Field F] (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
variable (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024) (A : State (2^s) (shrinkCharge s+rem))
local notation "M" => shrinkBinary T s D rem hD small A
local notation "B" => shrinkRecordState s rem A
local notation "N" => Fintype.card (B).Base
local notation "P" => shrinkRecordPacking s rem A
local notation "d" => (2^s : ℕ)
local notation "k" => (2*d+1 : ℕ)
local notation "hc" => palette_two s
local notation "good" => rawConditions s rem B
local notation "S" => shrinkStage s D
local notation "t" => CompressorPacking.tagBits d
local notation "X" => dims S N t rem
local notation "pad" => PhysicalShrink.padding k d D
local notation "prior" => shrinkRecordWidth s rem A
local notation "supply" => shrinkIssuedWords T s D rem hD small A
local notation "order" => edgeOrder P (baseNat (B).order) (tagOrdinal t).toEmbedding (S).pieces (S).pieceRadix (shrinkPieceBound s D)
variable {W K : ℕ} {cur : Word W} {input out : Memory W} {c : Cursor}
local notation "p" => pointers K c X

include hD small in
private theorem copiesPositive (i : Fin 4) : 0<(S).pieces i :=
  (SlotEnergy.slotCount_mass (by positivity : 0<((2^k*d*d:ℕ):ℝ)/D) small i).1

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
/-- Scope 3 resolves the raw motif edge in the absorbed-bit prefix. Scope 2
resolves the corresponding endpoint of the actual output piece on its residual lane. -/
def supplyField (branch : Fin (M).rules.count) (G : LiftedSlots ((B).Base×BitWord t) (liveDegree S+pad) (BitWord rem))
    (m : (P).Motif) (u : Fin 6) (edge : Fin 8) (bit : Fin (supply branch m edge)) : Fin 4→ℕ :=
  SupplySend.fieldValues P binary_neg good (ShrinkMotif.chooseWidths (supply branch))
    (S).pieces (copiesPositive s D hD small) order hc pad (supply branch) G m u edge bit

local notation "layoutOf" => fun branch=>ShrinkMotif.chooseWidths (supply branch)
local notation "Vtx" => Computability.VPVNP.Compression.Site (B).Base (BitWord t) (BitWord rem)
local notation "chosen" => PhysicalShrink.widths T P prior (shrinkRecordCode s rem A) hc
local notation "many" => PhysicalShrink.r T P prior (shrinkRecordCode s rem A) hc
local notation "tiles" => PhysicalShrink.tile T P prior (shrinkRecordCode s rem A) hc
local notation "parallelism" => copiesPositive s D hD small
local notation "paddingAt" => fun (ht : 0<t) => tagPadding (V:=(B).Base) (L:=BitWord rem) (tagOne ht) (tagOne_ne ht) pad

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
/-- The query selected by the histogram for the actual outgoing callback. -/
abbrev supplyRequest (branch : Fin (M).rules.count) (ht : 0<t) (v : Vtx) (m : (P).Motif)
    (party : {u // partySite P (layoutOf branch) m u=v}) (q : supplyGraph.Port party.val)
    (cross : wireOwner supplyGraph.tail supplyGraph.head (partySite P (layoutOf branch) m) q.val.1=none)
    (j : Fin (supply branch m q.val.1)) :=
  SupplySend.request P chosen many tiles (shrinkIssuedBranch T s D rem hD small A branch)
    binary_neg good (layoutOf branch) (S).pieces parallelism order hc pad (paddingAt ht) v m
    (PrivateOrder.onSide party q cross) j

theorem supplyField_absorbed (branch : Fin (M).rules.count)
    (G : LiftedSlots ((B).Base×BitWord t) (liveDegree S+pad) (BitWord rem)) (v : Vtx) (m : (P).Motif)
    (party : {u // partySite P (layoutOf branch) m u=v}) (q : supplyGraph.Port party.val)
    (own : wireOwner supplyGraph.tail supplyGraph.head (partySite P (layoutOf branch) m) q.val.1=some v)
    (j : Fin (supply branch m q.val.1)) :
    supplyField T s D rem hD small A branch G m party.val q.val.1 j=![3,q.val.1.val,j.val,0] := by
  simp [supplyField,SupplySend.fieldValues,own]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
/-- The four fields returned by the selected history’s outgoing supply request. -/
abbrev supplyField_fresh (branch : Fin (M).rules.count) (ht : 0<t)
    (G : LiftedSlots ((B).Base×BitWord t) (liveDegree S+pad) (BitWord rem)) (v : Vtx) (m : (P).Motif)
    (party : {u // partySite P (layoutOf branch) m u=v}) (q : supplyGraph.Port party.val)
    (cross : wireOwner supplyGraph.tail supplyGraph.head (partySite P (layoutOf branch) m) q.val.1=none)
    (j : Fin (supply branch m q.val.1)) :=
  SupplySend.fieldValues_request P chosen many tiles (shrinkIssuedBranch T s D rem hD small A branch)
    binary_neg good (layoutOf branch) (S).pieces parallelism order hc pad (paddingAt ht) G v m party q cross j

private theorem selected_four_words {w : ℕ} (a b c₀ d₀ : ℕ) (i : Fin 4) :
    (![ (a : Word w), (b : Word w), (c₀ : Word w), (d₀ : Word w)] : Fin 4 → Word w) i =
    (((![a,b,c₀,d₀] : Fin 4 → ℕ) i : ℕ) : Word w) := by
  fin_cases i <;> rfl

private theorem selected_supply_mode {w : ℕ} (dimensions : Dimensions) (pointers : Pointers)
    (layout : Bool) :
    (Resident.value dimensions pointers layout 27 : Word w) = (if layout then 1 else 0) := by
  cases layout <;> simp [Resident.value,selected]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem ShrinkOutput.supplyBitAt (branch : Fin (M).rules.count) (z : ShrinkOutput (K:=K) T s D rem hD small A cur input c branch out)
    (space : CursorSpace cur input c K X) (caps : ShrinkOldCaps s rem W) (extra : ShrinkOutputCaps s D N W)
    (top : ℕ) (size : ∀m j,supply branch m j≤top) (cap : top<2^W)
    (later : Memory W) (frame : Resident.GeometryFrame X p out later) (regs : Fin 13→Word W)
    (kernel : (later (regs 0).val).val=(p).ownHeader)
    (m : (P).Motif) (u : Fin 6) (port : supplyGraph.Port u) (bit : Fin (supply branch m port.val.1))
    (field : Fin 4) (row : later (regs 2).val=(Demand.key P (baseNat (B).order) m.val:Word W))
    (rp : (regs 3).val=u.val) (re : (regs 4).val=port.val.1.val) (rb : regs 5=(bit.val:Word W)) :
    let G:=Resident.successor («pad»:=pad) S P (B).order (shrinkPieceBound s D)
      (ShrinkMotif.chooseWidths (supply branch)) hc good z.tagPos
    (((BitOrigins.lookup S true (.reg 0) (.reg 2) (.reg 3) (.reg 4) (.reg 5) (.lit field.val) : Formula 13).compile
      (fun _=>(0:Fin 1))).eval (fun _=>0) later regs)=
      (supplyField T s D rem hD small A branch G m u port.val.1 bit field:Word W) := by
  classical
  let ptr:=Formula.reg (0:Fin 13)
  let V:=Formula.value (fun _=>0) later regs
  let lay:=ShrinkMotif.chooseWidths (supply branch)
  let src:=BitOrigins.oldArc ptr S (.load (.reg 2))
  let old:=z.reopenAt later frame (regs 0) kernel
  let files:=ShrinkOutput.partyFilesAt T s D rem hD small A branch z space caps extra top size cap later frame regs kernel
  have h:=(shrink_output_bounds s D rem A hD caps extra (supply branch) top size cap lay hc good z.tagPos).1
  have h8 : 8≤2^W := by have:=caps.eight;omega
  have mode : V (atField (Demand.formulaOps 13) ptr selected)=(if lay then 1 else 0) := by
    have f:=old.hdr.viewField (data:=fun _ => (0 : Word W)) (vs:=regs) ptr rfl (27 : Fin 34)
    exact f.trans (selected_supply_mode X p lay)
  have enc:=old.viewOldArc (data:=fun _ => (0 : Word W)) (vs:=regs) ptr (shrinkOutputCodec s rem A caps) (show V ptr=regs 0 from rfl) h.code h.slotAdd h.slotSub m (.reg 2) row
    ⟨caps.slots,caps.tags,caps.residual⟩ caps.colors
  have atEdge : regs 4=(port.val.1.val:Word W) := Fin.ext (re.trans (Fin.val_cast_of_lt (port.val.1.isLt.trans_le h8)).symm)
  have atParty : regs 3=(u.val:Word W) := Fin.ext (rp.trans (Fin.val_cast_of_lt (u.isLt.trans_le ((by decide : 6≤8).trans h8))).symm)
  have used : u=ShrinkMotif.supplySrc port.val.1 ∨ u=ShrinkMotif.supplyDst port.val.1 := by
    rcases port with ⟨⟨edge,side⟩,placed⟩
    cases side
    · exact Or.inl placed.symm
    · exact Or.inr placed.symm
  dsimp only
  rw [BitOrigins.lookup_compiled S true lay field later regs (by omega) mode]
  by_cases active : wireOwner supplyGraph.tail supplyGraph.head (partySite P lay m) port.val.1=none
  · let wire : CrossEdge P lay:=⟨m,⟨port.val.1,active⟩⟩
    let kind:=typeIndex P binary_neg good lay wire
    have counted : (S).pieces kind<2^W:=(shrinkPieceBound s D kind).trans_lt extra.pieces
    have result:=SupplySend.native_fresh_words files good (copiesPositive s D hD small) wire src enc
      (.reg 3) (.reg 4) (.reg 5) u field h8 caps.colors counted ((size m port.val.1).trans_lt cap)
      bit atEdge atParty rb used
    let nextGraph := Resident.successor («pad»:=pad) S P (B).order (shrinkPieceBound s D) lay hc good z.tagPos
    have graphRead : files.graph = nextGraph := rfl
    dsimp only at result
    rw [graphRead] at result
    dsimp only [lay] at active
    unfold supplyField SupplySend.fieldValues
    dsimp only
    rw [dite_eq_left active]
    exact result.trans (selected_four_words 2 0 _ _ field)
  · have absent (kind : Fin 4) : ShrinkMotif.survivor lay kind≠port.val.1 := by
      intro same
      have cross:=(crossTypeEquiv P binary_neg good lay m kind).property
      change wireOwner supplyGraph.tail supplyGraph.head (partySite P lay m) (ShrinkMotif.survivor lay kind)=none at cross
      exact active (same ▸ cross)
    have result:=BitOrigins.supply_absorbed (fun _=>0) later regs ptr S lay src (.reg 3) (.reg 4) (.reg 5)
      port.val.1 u h8 atEdge atParty used absent field
    change _ = (![3,(port.val.1.val : Word W),regs 5,0] : Fin 4 → Word W) field at result
    rw [rb] at result
    dsimp only [lay] at active
    unfold supplyField SupplySend.fieldValues
    dsimp only
    rw [dite_eq_right active]
    exact result.trans (selected_four_words 3 port.val.1.val bit.val 0 field)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem ShrinkOutput.supplyBit (branch : Fin (M).rules.count) (z : ShrinkOutput (K:=K) T s D rem hD small A cur input c branch out)
    (space : CursorSpace cur input c K X) (caps : ShrinkOldCaps s rem W) (extra : ShrinkOutputCaps s D N W)
    (top : ℕ) (size : ∀m j,supply branch m j≤top) (cap : top<2^W)
    (regs : Fin 13→Word W) (kernel : (out (regs 0).val).val=(p).ownHeader)
    (m : (P).Motif) (u : Fin 6) (port : supplyGraph.Port u) (bit : Fin (supply branch m port.val.1))
    (field : Fin 4) (row : out (regs 2).val=(Demand.key P (baseNat (B).order) m.val:Word W))
    (rp : (regs 3).val=u.val) (re : (regs 4).val=port.val.1.val) (rb : regs 5=(bit.val:Word W)) :
    let G:=Resident.successor («pad»:=pad) S P (B).order (shrinkPieceBound s D)
      (ShrinkMotif.chooseWidths (supply branch)) hc good z.tagPos
    (((BitOrigins.lookup S true (.reg 0) (.reg 2) (.reg 3) (.reg 4) (.reg 5) (.lit field.val) : Formula 13).compile
      (fun _=>(0:Fin 1))).eval (fun _=>0) out regs)=
      (supplyField T s D rem hD small A branch G m u port.val.1 bit field:Word W) :=
  ShrinkOutput.supplyBitAt T s D rem hD small A branch z space caps extra top size cap
    out (fun _ _=>rfl) regs kernel m u port bit field row rp re rb



end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
