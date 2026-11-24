import OAI.Computability.VPVNP.PairPendingArguments
import OAI.Computability.VPVNP.PairShrinkSurvivingBuffer
import OAI.Computability.VPVNP.CompressorShrinkSelectedSlices
import OAI.Computability.VPVNP.ShrinkStateOutput
import OAI.Computability.VPVNP.ShrinkSupplyLocal

/-!
# Surviving supply operands in the shrinking kernel

Each surviving wire is gathered from the numbered half-wires of the output
state. At the target this uses the incoming slot of the translated actual
arc. The two endpoints may hold independent half-wire assignments.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkSurvivingOperands

open Compression Compression.PackingData Compression.SurvivingSlots Compression.ShrinkPayload
open LocalHistory NodeArguments

private theorem outgoing_list {a g : ℕ} (X : State a g) (u : X.network.Site)
    (z : X.network.Half u) (e : {e // u = X.network.src e}) :
    List.ofFn (fieldBits X u z false ((outgoingOrder X u).entries.symm e)) =
      List.ofFn (z.1 e.val e.property) := by
  obtain ⟨j, rfl⟩ := (outgoingOrder X u).entries.surjective e
  rw [Equiv.symm_apply_apply]
  rfl

private theorem incoming_list {a g : ℕ} (X : State a g) (u : X.network.Site)
    (z : X.network.Half u) (e : {e // u = X.network.dst e}) :
    List.ofFn (fieldBits X u z true ((incomingOrder X u).entries.symm e)) =
      List.ofFn (z.2 e.val e.property) := by
  obtain ⟨j, rfl⟩ := (incomingOrder X u).entries.surjective e
  rw [Equiv.symm_apply_apply]
  rfl

private theorem ofFn_cast {n m : ℕ} (h : n = m) (f : Fin n → Bool) :
    List.ofFn f = List.ofFn (cast (congrArg (fun n ↦ Fin n → Bool) h) f) := by
  subst m
  rfl

open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing

/-- Reading a resident packet's specified native slot gives the node's
actual half-field. The private memory may already contain other packets. -/
theorem packet_field {a g w endAddr : ℕ} (X : State a g) (u : X.network.Site)
    (z : X.network.Half u) (arena : Arena) (node : ℕ) (mem : Word w → Word w)
    (fits : (Packet.mk node (packed X u z)).Fits arena w endAddr)
    (stored : (Packet.mk node (packed X u z)).Stored arena (DFS.scratch endAddr mem))
    (dir : Bool) (port : Fin (2 ^ a)) (i : Fin (X.halfWidth u dir port)) :
    mem ((arena.fieldAddress X u node dir port + i.val : ℕ) : Word w) =
      PrivateFields.bitValue w (fieldBits X u z dir port i) := by
  obtain ⟨pre, post, pieces, addr⟩ := packed_member X u z dir port
  have len : pre.length + i.val < (packed X u z).length := by rw [pieces]; simp; omega
  let pos : Fin (packed X u z).length := ⟨pre.length + i.val, len⟩
  have value := stored pos
  let abs := arena.base node + pos.val
  have hfit : abs < 2 ^ w := (Nat.add_lt_add_left pos.isLt _).trans_le fits.2.2
  have above : endAddr ≤ (abs : Word w).val := by
    rw [Fin.val_natCast, Nat.mod_eq_of_lt hfit]
    exact fits.1.trans (Nat.le_add_right _ _)
  change rawScratch (DFS.scratch endAddr mem) (abs : Word w) = _ at value
  rw [rawScratch, dite_eq_left above] at value
  rw [Arena.fieldAddress, ← addr, Nat.add_assoc]
  refine value.trans ?_
  change PrivateFields.bitValue w ((packed X u z)[pre.length + i.val]) = _
  simp [pieces, i.isLt]

variable {a b g pad : ℕ} (X : State a (packingLaneBits a g))
variable (layout : Bool) (subdiv : Fin 4 → ℕ)
variable (width : X.packingData.Motif → Fin 4 → ℕ)
variable {next : Equiv.Perm (X.Base × BitWord (packingTagBits (2 ^ a)))}
variable (I : X.packingData.ShrinkIndex layout subdiv next (2 ^ b) pad)
local notation "Y" => X.shrinkOutputState layout subdiv width I
variable (hpos : ∀ t, 0 < subdiv t) (m : X.packingData.Motif) (t : Fin 4)

/-- Packed source or target site of the specified supply edge. -/
noncomputable def site : Bool → (X.Base × BitWord (packingTagBits (2 ^ a))) × BitWord g
  | false => packedSiteEquiv (X.packingData.survivingRole layout (sourceRole layout t) m)
  | true => packedSiteEquiv (X.packingData.survivingRole layout (targetRole layout t) m)

/-- The native slot at the chosen end of one actual subdivision. -/
noncomputable def slot (dir : Bool) (j : Fin (subdiv t)) : Fin (2 ^ b) :=
  let i : Id X.packingData.Motif subdiv := ⟨t, m, j⟩
  let e := X.packingData.shrinkArcEquiv layout subdiv I.outgoing (.inl i)
  let ends := X.packingData.shrinkArc_endpoints layout subdiv I i
  match dir with
  | false => (outgoingOrder (Y) (site X layout m t false)).entries.symm ⟨e, ends.1.symm⟩
  | true => (incomingOrder (Y) (site X layout m t true)).entries.symm ⟨e, ends.2.symm⟩

/-- Outgoing slots retain the genuine arc number, while the incoming
slot is the second component of the lifted slot permutation's image. -/
theorem slot_number (dir : Bool) (j : Fin (subdiv t)) :
    let e := X.packingData.shrinkArcEquiv layout subdiv I.outgoing (.inl ⟨t, m, j⟩)
    slot X layout subdiv width I m t dir j =
      if dir then (I.graph.actualGraph.target e).2 else e.2 := by
  cases dir <;> rfl

/-- Word read by the supply map from an arbitrary half-assignment at this endpoint. -/
noncomputable def operand : (dir : Bool) → (Y).network.Half (site X layout m t dir) →
    Fin (width m t) → Bool
  | false => X.packingData.localSurvivingSource layout subdiv width I hpos m t
  | true => X.packingData.localSurvivingTarget layout subdiv width I hpos m t

/-- The physical node field is exactly the corresponding interval of the
local supply operand, at either of its endpoints. -/
theorem slot_bits (dir : Bool) (z : (Y).network.Half (site X layout m t dir)) (j : Fin (subdiv t)) :
    List.ofFn (fieldBits (Y) _ z dir (slot X layout subdiv width I m t dir j)) =
      List.ofFn (sliceWords (width m t) (subdiv t) (hpos t)
        (operand X layout subdiv width I hpos m t dir z) j) := by
  let i : Id X.packingData.Motif subdiv := ⟨t, m, j⟩
  let e := X.packingData.shrinkArcEquiv layout subdiv I.outgoing (.inl i)
  have he := X.packingData.shrinkArc_endpoints layout subdiv I i
  have hw := X.packingData.shrinkSlotWidth_genuine layout subdiv width I.outgoing i
  cases dir with
  | false =>
    change List.ofFn (fieldBits (Y) _ z false
      ((outgoingOrder (Y) _).entries.symm ⟨e, he.1.symm⟩)) = _
    refine (outgoing_list (Y) (site X layout m t false) z ⟨e, he.1.symm⟩).trans ?_
    simp only [operand, localSurvivingSource, Equiv.apply_symm_apply]
    exact ofFn_cast hw (z.1 e he.1.symm)
  | true =>
    change List.ofFn (fieldBits (Y) _ z true
      ((incomingOrder (Y) _).entries.symm ⟨e, he.2.symm⟩)) = _
    refine (incoming_list (Y) (site X layout m t true) z ⟨e, he.2.symm⟩).trans ?_
    simp only [operand, localSurvivingTarget, Equiv.apply_symm_apply]
    exact ofFn_cast hw (z.2 e he.2.symm)

open CompressorRecords CompressorRecords.SliceSchedule ShrinkSurvivingFrames
open scoped Fin.CommRing

/-- Copy one native output slot into the operand buffer from a supplied
parent packet, using the physical surviving row in level memory. -/
theorem execute_slot {w p r k endAddr : ℕ} {M : Machine w p r k} {pc : Fin 11 → Fin p}
    {reg : Fin 6 ↪ Fin r} {arcPC : Fin 7 → Fin p} {done : Fin p}
    (linked : ReverseSlices.Linked M pc reg (arcPC 0) done)
    (copy : PrivateFields.Linked M .copy arcPC (PrivateSlices.copyRegs reg) done)
    (c : Config w p r) (entry : c.pc = pc 0) (one : c.reg (reg 3) = 1)
    (dir : Bool) (z : (Y).network.Half (site X layout m t dir)) (j : Fin (subdiv t))
    (arena : Arena) (node dst : ℕ)
    (fits : (Packet.mk node (packed (Y) _ z)).Fits arena w endAddr)
    (stored : (Packet.mk node (packed (Y) _ z)).Stored arena (DFS.scratch endAddr c.privateMem))
    {row : ShrinkSliceSweep.Row w} {mem : Memory w}
    (image : ShrinkSliceSweep.Image row (width m t) mem) (count : row.count.val = subdiv t)
    (space : Workspace row.total row.dst row.bank 1 (subdiv t))
    (frame : c.reg (reg 5) = (head row (subdiv t) j : Word w))
    (dest : c.reg (reg 2) = (dst : Word w)) :
    let src := arena.fieldAddress (Y) (site X layout m t dir) node dir
      (slot X layout subdiv width I m t dir j)
    let bits := sliceWords (width m t) (subdiv t) (hpos t)
      (operand X layout subdiv width I hpos m t dir z) j
    c.reg (reg 0) = (src : Word w) →
      dst + width m t < 2 ^ w →
      (dst + width m t ≤ arena.base node ∨ arena.base node + (packed (Y) _ z).length ≤ dst) →
      ReverseSlices.FrameResult M reg done c mem (head row (subdiv t) j : Word w)
        (dst + start (width m t) (subdiv t) j) (List.ofFn bits) := by
  intro src bits source destFit apart
  let u := site X layout m t dir
  let port := slot X layout subdiv width I m t dir j
  have same : List.ofFn (fieldBits (Y) u z dir port) = List.ofFn bits :=
    slot_bits X layout subdiv width I hpos m t dir z j
  have widthEq : (Y).halfWidth u dir port = splitWidth (width m t) (subdiv t) j := by
    simpa only [List.length_ofFn] using congrArg List.length same
  obtain ⟨pre, post, packEq, addr⟩ := packed_member (Y) u z dir port
  have srcEq : src = arena.base node + pre.length := by
    change arena.base node + offset (Y) u dir port = _
    rw [addr]
  have srcBound : src + splitWidth (width m t) (subdiv t) j ≤
      arena.base node + (packed (Y) u z).length := by
    rw [packEq, srcEq, ← widthEq]
    simp only [List.length_append, List.length_ofFn]
    omega
  have endBound := ShrinkSurvivingFrames.end_le (width m t) (subdiv t) (hpos t) j
  apply execute_piece linked copy c entry one j image count space src dst frame source dest bits
  · intro _
    exact ⟨srcBound.trans fits.2.2, by omega⟩
  · intro _
    change dst + width m t ≤ arena.base node ∨
      arena.base node + (packed (Y) u z).length ≤ dst at apart
    rcases apart with left | right
    · exact Or.inl (le_trans (by omega) (left.trans (by rw [srcEq]; omega)))
    · exact Or.inr (srcBound.trans (right.trans (Nat.le_add_right _ _)))
  · intro i
    let k : Fin ((Y).halfWidth u dir port) := ⟨i.val, widthEq.symm ▸ i.isLt⟩
    have resident := packet_field (Y) u z arena node c.privateMem fits stored dir port k
    refine resident.trans (congrArg (PrivateFields.bitValue w) ?_)
    have e := congrArg (fun xs : List Bool ↦ xs[i.val]?) same
    simpa [k, i.isLt, show i.val < (Y).halfWidth u dir port from widthEq.symm ▸ i.isLt] using e

/-- Memory updates from visiting each actual output slot at this endpoint. -/
noncomputable def nativeFill {w : ℕ} (dir : Bool) (z : (Y).network.Half (site X layout m t dir))
    (dst : ℕ) (mem : Word w → Word w) : Word w → Word w :=
  (List.finRange (subdiv t)).foldl (fun prev j ↦
    PrivateFields.storeBits (dst + start (width m t) (subdiv t) j)
      (List.ofFn (fieldBits (Y) _ z dir (slot X layout subdiv width I m t dir j))) prev) mem

/-- Executing the memory updates from the full row stores exactly the
surviving supply word, including its selector bits. -/
theorem nativeFill_eq {w : ℕ} (dir : Bool) (z : (Y).network.Half (site X layout m t dir))
    (dst : ℕ) (mem : Word w → Word w) :
    nativeFill X layout subdiv width I m t dir z dst mem =
      PrivateFields.storeBits dst (List.ofFn (operand X layout subdiv width I hpos m t dir z))
        mem := by
  unfold nativeFill
  simp only [slot_bits X layout subdiv width I hpos m t dir z]
  exact ShrinkSurvivingBuffer.fill_eq (width m t) (subdiv t) (hpos t) _ dst mem

section Map

open NetworkKernel ShrinkMotif
open private readSupplyEnd from OAI.Computability.VPVNP.ShrinkSupplyLocal
open private layoutCases layoutCases_active from OAI.Computability.VPVNP.ShrinkSupplyLocal

variable (allWidths : X.packingData.Motif → Bool × Fin 4 → ℕ)
local notation "W" => fun m t ↦ allWidths m (layout, t)
local notation "S" => X.shrinkOutputState layout subdiv (W) I

/-- Vertex of the six-party map which owns this end of the surviving wire. -/
def party (layout : Bool) (t : Fin 4) : Bool → Fin 6
  | false => supply.src (layout, t)
  | true => supply.dst (layout, t)

theorem party_site (dir : Bool) :
    X.packingData.shrinkPartySite layout m (party layout t dir) = site X layout m t dir := by
  cases dir <;> simp only [shrinkPartySite, party, role_src_survives, role_dst_survives, site]

/-- Select the incoming or outgoing column of the actual local supply map
at the active edge. Its opposite layout fields use the internal assignment. -/
noncomputable def mapColumn (dir : Bool)
    (h : Placed (X.packingData.shrinkInternalOwner layout) (internalLabel allWidths layout)
      (X.packingData.shrinkPartySite layout m (party layout t dir)))
    (z : (S).network.Half (X.packingData.shrinkPartySite layout m (party layout t dir))) :
    Fin (2 ^ allWidths m (layout, t)) :=
  match dir with
  | false =>
    (X.packingData.shrinkLocalSupplyArg layout subdiv allWidths I hpos m _ h z).1 (layout, t) rfl
  | true =>
    (X.packingData.shrinkLocalSupplyArg layout subdiv allWidths I hpos m _ h z).2 (layout, t) rfl

/-- The reconstructed operand is precisely the bit representation of the
surviving column on independent local half-wires. -/
theorem mapColumn_bits (dir : Bool)
    (h : Placed (X.packingData.shrinkInternalOwner layout) (internalLabel allWidths layout)
      (X.packingData.shrinkPartySite layout m (party layout t dir)))
    (z : (S).network.Half (X.packingData.shrinkPartySite layout m (party layout t dir))) :
    RAMSerialization.wordBits _ (mapColumn X layout subdiv I hpos m t allWidths dir h z) =
      operand X layout subdiv (W) I hpos m t dir
        ⟨fun e he ↦ z.1 e ((party_site X layout m t dir).trans he),
         fun e he ↦ z.2 e ((party_site X layout m t dir).trans he)⟩ := by
  cases dir <;> simp only [mapColumn, shrinkLocalSupplyArg, readSupplyEnd, layoutCases_active,
    Equiv.apply_symm_apply, operand] <;> rfl

/-- Reading a gathered bit gives that coordinate of the local six-party
map's actual supply basis index. -/
theorem nativeFill_mapColumn {w : ℕ} (dir : Bool)
    (h : Placed (X.packingData.shrinkInternalOwner layout) (internalLabel allWidths layout)
      (X.packingData.shrinkPartySite layout m (party layout t dir)))
    (z : (S).network.Half (X.packingData.shrinkPartySite layout m (party layout t dir)))
    (dst : ℕ) (mem : Word w → Word w) (fit : dst + allWidths m (layout, t) ≤ 2 ^ w)
    (i : Fin (allWidths m (layout, t))) :
    let halves : (S).network.Half (site X layout m t dir) :=
      ⟨fun e he ↦ z.1 e ((party_site X layout m t dir).trans he),
       fun e he ↦ z.2 e ((party_site X layout m t dir).trans he)⟩
    nativeFill X layout subdiv (W) I m t dir halves dst mem ((dst + i.val : ℕ) : Word w) =
      PrivateFields.bitValue w (RAMSerialization.wordBits _
        (mapColumn X layout subdiv I hpos m t allWidths dir h z) i) := by
  intro halves
  rw [nativeFill_eq X layout subdiv (W) I hpos m t dir halves dst mem, mapColumn_bits]
  exact (PrivateFields.storeBits_read dst _ mem (by simpa using fit)
    ⟨i.val, by simp⟩).trans (by simp only [List.getElem_ofFn]; rfl)

end Map

section Selection

open MotifBlocks MotifGrid MotifConversion ShrinkMotif
open CompressorRecords.ShrinkSliceSweep

variable {K : Type*} [_root_.Field K] {factor : ℝ}
variable (F : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable {w : ℕ}

open Classical in
/-- Extract exactly the three preconditions of the reverse reader from the
selected global row sweep at the physical dense ordinal of a motif and role. -/
theorem selected_inputs (s : X.ShrinkSelection F) (term : Word w) (stride widthBase : ℕ)
    (mem : Memory w) :
    let T := selectedAllocation F X s term stride widthBase subdiv
    let sites := Shrink.packedIndex (a := a) (g := g) X.baseIndex
    let id := (ShrinkMotifOrder.stateNumber X m, t)
    let row := T.row id
    T.Fits → (∀ i, Image (T.row i)
      (selected X.packingData X.shrinkNumber sites T F X.packingWidth s i) mem) →
      Image row (X.packingData.termWidths F X.shrinkNumber X.packingWidth s m T.layout t) mem ∧
      row.count.val = subdiv t ∧ Workspace row.total row.dst row.bank 1 (subdiv t) := by
  intro T sites id row fit images
  have count : row.count.val = subdiv t := (T.row_vals fit id).2.2.2.2
  refine ⟨?_, count, count ▸ T.space fit id⟩
  simpa only [selected, id, ShrinkMotifOrder.stateNumber, Equiv.symm_apply_apply, sites]
    using images id

end Selection

end PairSimulation.ShrinkSurvivingOperands

end VPVNP
end Computability
end OAI
