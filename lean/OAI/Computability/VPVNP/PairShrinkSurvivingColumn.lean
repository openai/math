import OAI.Computability.VPVNP.PairShrinkSurvivingAddress
import OAI.Computability.VPVNP.PairShrinkSurvivingPointers
import OAI.Computability.VPVNP.PairResidentFrameColumn

/-!
# Gathering a surviving endpoint into the six-party map buffer

The linked column computes three pointers per subdivision. The inverse sorted
table supplies the native field's port. The row table supplies the frame.
The full column reads one resident packet and writes one complete supply word.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkSurvivingColumn

open BurstRAM BurstRAM.PrivateRAM Compression Compression.PackingData
open CompressorRecords CompressorRecords.PhaseRecipe CompressorRecords.ShrinkSliceSweep
open NodeArguments ShrinkSurvivingPointers ShrinkSurvivingOperands ShrinkSurvivingFrames
open private descriptor head_fit from OAI.Computability.VPVNP.PairShrinkSurvivingFrames
open scoped Fin.CommRing

/-- Common runtime parameters of the column. The node and private destination
are supplied by the enclosing map job. -/
structure Inputs where
  /-- Runtime heads and dimensions used to recover the surviving endpoint's port and
  subdivision frame. -/
  tables : ShrinkSurvivingPointers.Inputs
  /-- Argument-arena geometry and incidence columns of the state containing the subdivided
  endpoint. -/
  half : ShrinkOldHalves.Physical.Header
  /-- DFS node expression selecting the private packet that contains this endpoint's
  subdivision. -/
  node : Expr
  /-- Private base expression of the unsplit supply word being reconstructed. -/
  destination : Expr

/-- Build the reverse-copy setup for one subdivision from its oriented port, resident packet
field, unsplit destination, and interval frame. -/
def Inputs.setup (H : Inputs) (degree : ℕ) (subdiv : Fin 4 → ℕ) (t : Fin 4) (dir : Bool)
    (j : Fin (subdiv t)) : ResidentColumn.Setup :=
  let endpoint := port degree (H.tables.rect subdiv t j dir)
  ⟨ShrinkSurvivingAddress.field degree H.half H.node dir endpoint, H.destination,
    H.tables.frame subdiv t j, true⟩

variable {a b g pad w : ℕ} (X : State a (packingLaneBits a g)) (layout : Bool)
variable (subdiv : Fin 4 → ℕ) (width : X.packingData.Motif → Fin 4 → ℕ)
variable {next : Equiv.Perm (X.Base × BitWord (packingTagBits (2 ^ a)))}
variable (I : X.packingData.ShrinkIndex layout subdiv next (2 ^ b) pad)
variable (m : X.packingData.Motif) (t : Fin 4) (dir : Bool)
local notation "Y" => X.shrinkOutputState layout subdiv width I
local notation "u" => site X layout m t dir
local notation "slt" => slot X layout subdiv width I m t dir
variable (z : (X.shrinkOutputState layout subdiv width I).network.Half (site X layout m t dir))
variable (A : Arena) (node dst : ℕ)
variable (bank : ShrinkSliceSweep.Row w)

/-- Logical rows carry the actual native fields, including zero-length subdivisions. -/
noncomputable def row (j : Fin (subdiv t)) : ResidentColumn.Row :=
  ⟨A.fieldAddress (Y) (u) node dir (slt j), dst, head bank (subdiv t) j, 0,
    start (width m t) (subdiv t) j, List.ofFn (fieldBits (Y) (u) z dir (slt j))⟩

local notation "rows" => row X layout subdiv width I m t dir z A node dst bank

theorem row_length (hpos : ∀ t, 0 < subdiv t) (j : Fin (subdiv t)) :
    (rows j).bits.length = splitWidth (width m t) (subdiv t) j := by
  have hs := slot_bits X layout subdiv width I hpos m t dir z j
  exact (congrArg List.length hs).trans List.length_ofFn

/-- The actual stored packet meets every frame's private source precondition. -/
theorem reads {endAddr : ℕ} (priv : Word w → Word w)
    (fit : (Packet.mk node (packed (Y) (u) z)).Fits A w endAddr)
    (stored : (Packet.mk node (packed (Y) (u) z)).Stored A (DFS.scratch endAddr priv))
    (j : Fin (subdiv t)) : (rows j).reads priv := by
  intro i
  let k : Fin ((Y).halfWidth (u) dir (slt j)) :=
    ⟨i.val, by simpa only [row, List.length_ofFn] using i.isLt⟩
  simpa only [row, Nat.add_zero, List.getElem_ofFn] using
    packet_field (Y) (u) z A node priv fit stored dir (slt j) k

/-- Each copy is from the packet below the workspace boundary into the
unsplit word above it, so earlier writes preserve all later source bits. -/
theorem fits (hpos : ∀ t, 0 < subdiv t) (pivot : ℕ)
    (packetEnd : A.base node + (packed (Y) (u) z).length ≤ pivot)
    (destStart : pivot ≤ dst) (destEnd : dst + width m t < 2 ^ w)
    (j : Fin (subdiv t)) : (rows j).Fits w pivot := by
  obtain ⟨pre, post, he, offset⟩ := packed_member (Y) (u) z dir (slt j)
  have len := row_length X layout subdiv width I m t dir z A node dst bank hpos j
  constructor
  · intro _
    change A.base node + NodeArguments.offset (Y) (u) dir (slt j) + 0 +
      (List.ofFn (fieldBits (Y) (u) z dir (slt j))).length ≤ pivot
    rw [← offset]
    rw [he, List.length_append, List.length_append] at packetEnd
    omega
  · exact destStart
  · intro _
    change dst + start (width m t) (subdiv t) j + (rows j).bits.length < _
    rw [len]
    have := end_le (width m t) (subdiv t) (hpos t) j
    omega

variable (H : Inputs) {pub : Fin 5 → Word w} {state : Word w} {mem : Memory w}
variable (hpos : ∀ t, 0 < subdiv t)

include hpos in
/-- Combine the actual port ordinal, packet directory and final three-word
interval image into the private worker's complete recorded row. -/
theorem recorded {n A₀ : ℕ} (T : Allocation w n A₀) (alloc : T.Fits) (idx : Fin n)
    (sameProfile : T.subdiv = subdiv) (atRow : T.row (idx, t) = bank)
    (inc : IncidenceDirectory w) (layer stride : ℕ)
    (half : H.half.Stored inc A layer stride pub state mem)
    (cols : inc.ActualColumns (Y) mem)
    (capacity : Fintype.card (Y).Base * 2 ^ g * 2 ^ b ≤ 2 ^ w) (degreeFit : 2 ^ b < 2 ^ w)
    (nodeAt : H.node.eval pub state mem = CursorRAM.encode w node)
    (destAt : H.destination.eval pub state mem = (dst : Word w))
    (dense : H.tables.dense.eval pub state mem = (idx.val : Word w))
    (interval : H.tables.intervalHead.eval pub state mem = (T.widthEnd : Word w))
    (image : ShrinkSliceSweep.Image bank (width m t) mem)
    (j : Fin (subdiv t))
    (portAt : (port (2 ^ b) (H.tables.rect subdiv t j dir)).eval pub state mem =
      IncidenceDirectory.actualPort (Y) ((u), slt j)) :
    (rows j).Recorded (H.setup (2 ^ b) subdiv t dir j) pub state mem := by
  subst subdiv
  subst bank
  let bank := T.row (idx, t)
  let q := T.subdiv t
  have count : bank.count.val = q := (T.row_vals alloc (idx, t)).2.2.2.2
  have room : SliceSchedule.Workspace bank.total bank.dst bank.bank 1 q :=
    count ▸ T.space alloc (idx, t)
  have src := ShrinkSurvivingAddress.field_eq X layout T.subdiv width I m t dir j
    H.half inc A half cols capacity degreeFit H.node _ node nodeAt portAt
  have len := row_length X layout T.subdiv width I m t dir z A node dst bank hpos j
  obtain ⟨hlen, hoff⟩ := descriptor image count j
  refine ⟨src, destAt, frame_eval H.tables T alloc idx t j dense interval,
    head_fit j room, hlen.trans len.symm, ?_⟩
  intro hp
  exact (hoff (len ▸ hp)).symm

/-- The concatenation of these precise native writes is one unsplit word. -/
theorem writes_operand (priv : Word w → Word w) :
    ResidentColumn.writes rows (List.finRange (subdiv t)) priv =
      PrivateFields.storeBits dst (List.ofFn (operand X layout subdiv width I hpos m t dir z))
        priv :=
  nativeFill_eq X layout subdiv width I hpos m t dir z dst priv


/-- Run the complete linked subdivision column from one resident packet.
Each iteration computes its pointers in the native register-setup machine. -/
theorem native {p r k endAddr : ℕ} (M : Machine w p r k)
    (vm : ∀ j, Fin (RegisterSetup.regCount ((H.setup (2 ^ b) subdiv t dir j).operands)) ↪ Fin r)
    (inputs : Fin 6 → Fin r) (loc : ResidentColumn.Label (H.setup (2 ^ b) subdiv t dir) → Fin p)
    (ret : Fin p)
    (code : ∀ l, M.code (loc l) = ResidentColumn.instruction (H.setup (2 ^ b) subdiv t dir)
      vm inputs loc ret l)
    (apart : ∀ i v j, vm i v ≠ inputs j)
    (recorded : ∀ j, (rows j).Recorded (H.setup (2 ^ b) subdiv t dir j) pub state mem)
    (cfg : Config w p r)
    (entry : cfg.pc = ResidentColumn.start (H.setup (2 ^ b) subdiv t dir) loc ret 0)
    (hp : ∀ j : Fin 5, cfg.reg (inputs j.castSucc) = pub j)
    (hs : cfg.reg (inputs (Fin.last 5)) = state)
    (packetFit : (Packet.mk node (packed (Y) (u) z)).Fits A w endAddr)
    (supplied : (Packet.mk node (packed (Y) (u) z)).Stored A (DFS.scratch endAddr cfg.privateMem))
    (pivot : ℕ) (below : A.base node + (packed (Y) (u) z).length ≤ pivot)
    (above : pivot ≤ dst) (room : dst + width m t < 2 ^ w) :
    ∃ events out, ResidentColumn.Result (H.setup (2 ^ b) subdiv t dir) vm M ret rows
      (List.finRange (subdiv t)) mem cfg out events ∧
      out.privateMem = PrivateFields.storeBits dst
        (List.ofFn (operand X layout subdiv width I hpos m t dir z)) cfg.privateMem := by
  have fit := fits X layout subdiv width I m t dir z A node dst bank hpos pivot below above room
  have read := reads X layout subdiv width I m t dir z A node dst bank cfg.privateMem
    packetFit supplied
  obtain ⟨events, out, result⟩ := ResidentColumn.native M loc ret code apart rows mem pub state
    recorded pivot fit cfg entry hp hs read
  exact ⟨events, out, result, result.memory.trans
    (writes_operand X layout subdiv width I m t dir z A node dst bank hpos cfg.privateMem)⟩

end PairSimulation.ShrinkSurvivingColumn

end VPVNP
end Computability
end OAI
