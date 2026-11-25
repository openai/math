import OAI.ThreeFlat.Diagonal.PhysicalShrinkPublished
import OAI.ThreeFlat.Diagonal.ShrinkDemandCD

namespace OAI
/-! # Reopening both physical graphs for a selected shrink party -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM NavigationDirectory

/-- Every persistent geometric read belongs to the old header, graph, widths,
or the newly allocated chronological interval. -/
theorem GeometryRead.in_intervals {w K : ℕ} {cur : Word w} {start : Memory w} {c : Cursor}
    {x : Dimensions} (z : CursorSpace cur start c K x) (safe : ℕ→Prop)
    (header : ∀ a,c.header≤a → a<c.header+34 → safe a)
    (oldGraph : ∀ a,c.graph≤a → a<c.graph+6*x.oldEdges → safe a)
    (oldWidths : ∀ a,c.width≤a → a<c.width+x.oldEdges*x.originalLanes → safe a)
    (heap : ∀ a,c.heap≤a → a<(allocate K c (.shrink x)).next.heap → safe a) :
    ∀ a,GeometryRead x (pointers K c x) a→safe a := by
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,a8,a9⟩ := z.allocated
  have endHeap : (pointers K c x).costs ≤ (allocate K c (.shrink x)).next.heap := by
    change _ ≤ extraEnd x ((pointers K c x).costs+2*(x.motifs+1))
    rw [extra_extent]
    omega
  intro a read
  cases read with
  | old persistent =>
    cases persistent (a+1) with
    | current e => omega
    | header h => exact header a h.1 h.2
    | graph h => exact oldGraph a h.1 h.2
    | widths h => exact oldWidths a h.1 h.2
    | sliced h | colors h | offsets h | issued h =>
      obtain ⟨lo,hi⟩ := h
      exact heap a (by omega) (by omega)
  | graph h | keys h | width h =>
    obtain ⟨lo,hi⟩ := h
    exact heap a (by omega) (by omega)

/-- An archived stage occupies four persistent intervals. Selected-node evaluation
can alter all scratch arenas outside these intervals. -/
theorem GeometryFrame.of_intervals {w K : ℕ} {cur : Word w} {start saved later : Memory w} {c : Cursor}
    {x : Dimensions} (z : CursorSpace cur start c K x)
    (header : ∀ a,c.header≤a → a<c.header+34 → later a=saved a)
    (oldGraph : ∀ a,c.graph≤a → a<c.graph+6*x.oldEdges → later a=saved a)
    (oldWidths : ∀ a,c.width≤a → a<c.width+x.oldEdges*x.originalLanes → later a=saved a)
    (heap : ∀ a,c.heap≤a → a<(allocate K c (.shrink x)).next.heap → later a=saved a) :
    GeometryFrame x (pointers K c x) saved later := by
  exact GeometryRead.in_intervals z (fun a=>later a=saved a) header oldGraph oldWidths heap



end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident

namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalPinsExpr Computability.VPVNP.Compression CompressorPacking
open Native Native.ShrinkStage Native.ShrinkStage.Resident Native.Placement Native.Graph
open NavigationDirectory NavigationPass PhysicalShrink ShrinkStageNav
open scoped Classical Fin.NatCast
noncomputable section
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
variable {W K : ℕ} {cur : Word W} {input out : Memory W} {c : Cursor}
local notation "p" => pointers K c X

private theorem selected_bundle_positive (s : ℕ) : 0<3*(2^(2*2^s+1)*2^s)/4 := by
  have two : 2≤2*2^s+1 := palette_two s
  have four : 4≤2^(2*2^s+1) := Nat.pow_le_pow_right (by decide : 0<2) two
  have product:=Nat.le_mul_of_pos_right (2^(2*2^s+1)) (Nat.two_pow_pos s)
  omega

variable {T s D rem hD small A} in
/-- Rebuild the stage view at an arbitrary scratch pointer after history preparation. -/
theorem ShrinkOutput.reopenAt {branch : Fin (shrinkBinary T s D rem hD small A).rules.count}
    (z : ShrinkOutput (K:=K) T s D rem hD small A cur input c branch out) (later : Memory W)
    (frame : GeometryFrame X p out later) (kernel : Word W) (header : (later kernel.val).val=(p).ownHeader) :
    Input S P (B).order hc (ShrinkMotif.chooseWidths (supply branch)) p kernel prior (supply branch) later :=
  z.graphInput.frameWith kernel header (fun a h=>(frame a (.old h)).trans (z.priorFrame a h))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
/-- Both old arcs and issued split supply ports are reopened directly from the
chronological write, including the per-slot identifiers used to locate the live edges. -/
def ShrinkOutput.partyFiles (branch : Fin (M).rules.count) (z : ShrinkOutput (K:=K) T s D rem hD small A cur input c branch out)
    (space : CursorSpace cur input c K X) (caps : ShrinkOldCaps s rem W) (extra : ShrinkOutputCaps s D N W)
    (top : ℕ) (size : ∀m j,supply branch m j≤top) (cap : top<2^W)
    (regs : Fin 13→Word W) (kernel : (out (regs 0).val).val=(p).ownHeader) :
    BitOrigins.SupplyFiles (n:=13) («N»:=N) («t»:=t) (l:=rem) (W:=W) S P (shrinkOutputCodec s rem A caps) (B).order (shrinkPieceBound s D)
      (ShrinkMotif.chooseWidths (supply branch)) hc (.reg (0:Fin 13)) (fun _=>0) out regs prior (supply branch) pad := by
  let lay:=ShrinkMotif.chooseWidths (supply branch)
  let E:=shrinkOutputCodec s rem A caps
  have h:= (shrink_output_bounds s D rem A hD caps extra (supply branch) top size cap lay hc good z.tagPos).1
  have old:=z.reopen (regs 0) kernel
  let nextGraph := Resident.successor («pad»:=pad) S P (B).order (shrinkPieceBound s D) lay hc good z.tagPos
  let nextWidth := Resident.newWidth («pad»:=pad) S P (B).order (shrinkPieceBound s D) lay hc good (supply branch)
  exact old.supplyFiles («pad»:=pad) (data:=fun _ => (0 : Word W)) (vs:=regs) (.reg (0:Fin 13)) E
    rfl h.code h.slotAdd h.slotSub (shrinkPieceBound s D) nextGraph nextWidth
    z.nativeGraph z.keysRead h.keys space.separation.keyEnd.le space.separation.graphEnd.le h.live h.degree

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
/-- Both old arcs and issued split supply ports are reopened directly from the
chronological write, including the per-slot identifiers used to locate the live edges. -/
def ShrinkOutput.partyFilesAt (branch : Fin (M).rules.count) (z : ShrinkOutput (K:=K) T s D rem hD small A cur input c branch out)
    (space : CursorSpace cur input c K X) (caps : ShrinkOldCaps s rem W) (extra : ShrinkOutputCaps s D N W)
    (top : ℕ) (size : ∀m j,supply branch m j≤top) (cap : top<2^W)
    (later : Memory W) (frame : GeometryFrame X p out later) (regs : Fin 13→Word W)
    (kernel : (later (regs 0).val).val=(p).ownHeader) :
    BitOrigins.SupplyFiles (n:=13) («N»:=N) («t»:=t) (l:=rem) (W:=W) S P (shrinkOutputCodec s rem A caps) (B).order (shrinkPieceBound s D)
      (ShrinkMotif.chooseWidths (supply branch)) hc (.reg (0:Fin 13)) (fun _=>0) later regs prior (supply branch) pad := by
  let lay:=ShrinkMotif.chooseWidths (supply branch)
  let E:=shrinkOutputCodec s rem A caps
  have h:= (shrink_output_bounds s D rem A hD caps extra (supply branch) top size cap lay hc good z.tagPos).1
  have old:=z.reopenAt later frame (regs 0) kernel
  have readGraph := z.nativeGraph.frame
    (fun a lo hi=>congrArg Fin.val (frame a (.graph ⟨lo,hi⟩)))
    (fun a lo hi=>congrArg Fin.val (frame a (.width ⟨lo,by
      change a<(p).newWidths+N*2^t*(liveDegree S+pad)*2^rem at hi
      change a<(p).newWidths+N*2^t*(S).outputDegree*2^rem
      exact hi.trans_eq (congrArg (fun degree => (p).newWidths+N*2^t*degree*2^rem) h.degree.symm)⟩)))
  have readKeys (u : ((B).Base × BitWord t) × Fin (liveDegree S+pad)) :
      later ((p).keys+SlotImage.ordinal (Template.tagNumber («t»:=t) (B).order) u)=
      (Template.sourceKey S P (B).order (shrinkPieceBound s D) lay hc u:Word W) := by
    rw [frame _ (.keys ⟨Nat.le_add_right ..,?_⟩),z.keysRead]
    apply Nat.add_lt_add_left
    have slot:=SlotImage.ordinal_lt (Template.tagNumber («t»:=t) (B).order) u
    change _<N*2^t*(S).outputDegree
    exact slot.trans_eq (congrArg (fun degree => N*2^t*degree) h.degree.symm)
  let nextGraph := Resident.successor («pad»:=pad) S P (B).order (shrinkPieceBound s D) lay hc good z.tagPos
  let nextWidth := Resident.newWidth («pad»:=pad) S P (B).order (shrinkPieceBound s D) lay hc good (supply branch)
  exact old.supplyFiles («pad»:=pad) (data:=fun _ => (0 : Word W)) (vs:=regs) (.reg (0:Fin 13)) E
    rfl h.code h.slotAdd h.slotSub (shrinkPieceBound s D) nextGraph nextWidth
    readGraph readKeys h.keys space.separation.keyEnd.le space.separation.graphEnd.le h.live h.degree

open private BitOrigins.requestWord from OAI.ThreeFlat.Diagonal.ShrinkDemandCD

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
/-- The field address of the selected party and local port is precisely the
word published by the chronological native shrink and the node's chosen history. -/
theorem ShrinkOutput.demandBit (branch : Fin (M).rules.count) (z : ShrinkOutput (K:=K) T s D rem hD small A cur input c branch out)
    (_space : CursorSpace cur input c K X) (caps : ShrinkOldCaps s rem W) (extra : ShrinkOutputCaps s D N W)
    (top : ℕ) (size : ∀m j,supply branch m j≤top) (cap : top<2^W)
    (regs : Fin 13→Word W) (kernel : (out (regs 0).val).val=(p).ownHeader)
    (m : (P).Motif) (party : Fin 6) (port : demandGraph.Port party)
    (bit : Fin (demandWidth P prior (motifNumbers P (Demand.key P (baseNat (B).order)) hc) m port.val.1))
    (field : Fin 4) (row : out (regs 2).val=(Demand.key P (baseNat (B).order) m.val:Word W))
    (rp : (regs 3).val=party.val) (re : (regs 4).val=port.val.1.val) (rb : regs 5=(bit.val:Word W))
    (maxWidth : A.maxWidth<2^W) (total : thickWidth P prior ((P).bundle m)<2^W) :
    let raw:=Demand.key P (baseNat (B).order)
    let num:=motifNumbers P raw hc
    let qPos:=selected_bundle_positive s
    let site:=partySite P (ShrinkMotif.chooseWidths (supply branch)) m party
    (((BitOrigins.lookup S false (.reg 0) (.reg 2) (.reg 3) (.reg 4) (.reg 5) (.lit field.val) : Formula 13).compile
      (fun _=>(0:Fin 1))).eval (fun _=>0) out regs)=
      (BitOrigins.requestWord (S₀:=S) («P»:=P) («prior»:=prior) (c:=2*d) raw qPos num
        m port.val.2 port.val.1 bit (motifNumbers_bundle P raw hc)
        (ShrinkMotif.chooseWidths (supply branch)) site
        (congrArg (partySite P (ShrinkMotif.chooseWidths (supply branch)) m) port.property) field : Word W) := by
  dsimp only
  let lay:=ShrinkMotif.chooseWidths (supply branch)
  have h:=(shrink_output_bounds s D rem A hD caps extra (supply branch) top size cap lay hc good z.tagPos).1
  have old:=z.reopen (regs 0) kernel
  apply BitOrigins.selected_demand (S₀:=S) (c:=2*d) («P»:=P) (E:=shrinkOutputCodec s rem A caps)
    (selected_bundle_positive s) p lay (supply branch) regs m party port bit field
    old h.code h.slotAdd h.slotSub old.aux.graphFits row
    ⟨caps.slots,caps.tags,caps.residual⟩ ((Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp caps.colors)
    (by have:=caps.eight;omega) rp re rb
  · exact fun a=>(prior_width_le s rem A a).trans_lt maxWidth
  · exact total
  · exact caps.bundle

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
/-- The field address of the selected party and local port is precisely the
word published by the chronological native shrink and the node's chosen history. -/
theorem ShrinkOutput.demandBitAt (branch : Fin (M).rules.count) (z : ShrinkOutput (K:=K) T s D rem hD small A cur input c branch out)
    (_space : CursorSpace cur input c K X) (caps : ShrinkOldCaps s rem W) (extra : ShrinkOutputCaps s D N W)
    (top : ℕ) (size : ∀m j,supply branch m j≤top) (cap : top<2^W)
    (later : Memory W) (frame : GeometryFrame X p out later) (regs : Fin 13→Word W)
    (kernel : (later (regs 0).val).val=(p).ownHeader)
    (m : (P).Motif) (party : Fin 6) (port : demandGraph.Port party)
    (bit : Fin (demandWidth P prior (motifNumbers P (Demand.key P (baseNat (B).order)) hc) m port.val.1))
    (field : Fin 4) (row : later (regs 2).val=(Demand.key P (baseNat (B).order) m.val:Word W))
    (rp : (regs 3).val=party.val) (re : (regs 4).val=port.val.1.val) (rb : regs 5=(bit.val:Word W))
    (maxWidth : A.maxWidth<2^W) (total : thickWidth P prior ((P).bundle m)<2^W) :
    let raw:=Demand.key P (baseNat (B).order)
    let num:=motifNumbers P raw hc
    let qPos:=selected_bundle_positive s
    let site:=partySite P (ShrinkMotif.chooseWidths (supply branch)) m party
    (((BitOrigins.lookup S false (.reg 0) (.reg 2) (.reg 3) (.reg 4) (.reg 5) (.lit field.val) : Formula 13).compile
      (fun _=>(0:Fin 1))).eval (fun _=>0) later regs)=
      (BitOrigins.requestWord (S₀:=S) («P»:=P) («prior»:=prior) (c:=2*d) raw qPos num
        m port.val.2 port.val.1 bit (motifNumbers_bundle P raw hc)
        (ShrinkMotif.chooseWidths (supply branch)) site
        (congrArg (partySite P (ShrinkMotif.chooseWidths (supply branch)) m) port.property) field : Word W) := by
  dsimp only
  let lay:=ShrinkMotif.chooseWidths (supply branch)
  have h:=(shrink_output_bounds s D rem A hD caps extra (supply branch) top size cap lay hc good z.tagPos).1
  have old:=z.reopenAt later frame (regs 0) kernel
  apply BitOrigins.selected_demand (S₀:=S) (c:=2*d) («P»:=P) (E:=shrinkOutputCodec s rem A caps)
    (selected_bundle_positive s) p lay (supply branch) regs m party port bit field
    old h.code h.slotAdd h.slotSub old.aux.graphFits row
    ⟨caps.slots,caps.tags,caps.residual⟩ ((Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp caps.colors)
    (by have:=caps.eight;omega) rp re rb
  · exact fun a=>(prior_width_le s rem A a).trans_lt maxWidth
  · exact total
  · exact caps.bundle



end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
