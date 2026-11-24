import OAI.Computability.VPVNP.CompressorShrinkResidentScan
import OAI.Computability.VPVNP.CompressorShrinkResidentFormula
import OAI.Computability.VPVNP.CompressorShrinkMotifAbsolute

/-!
# Native owner columns for hidden and map residents of a shrinking node

The dense CD array comes from the classified old-port scatter. The selected
layout supplies the absolute role rows. A scan over the motif-major order
uses exactly these two inputs to materialize each resident's packed owner.
-/

namespace OAI
namespace Computability
namespace VPVNP

set_option maxHeartbeats 1500000

namespace CompressorRecords.ShrinkResidentDirectory

open Compression Compression.SurvivingSlots BurstRAM BurstRAM.PrivateRAM
open PrimedStackRAM PairSimulation.LocalHistory ShrinkHistoryRows ResidentOwners
open scoped Fin.CommRing

variable {a g w : ℕ} (X : State a (packingLaneBits a g))

/-- Motif-major scan order for resident occurrences, with four internal fields or six party
maps per motif according to `maps`. -/
noncomputable abbrev oldOrder (maps : Bool) := (shrinkMotifOrder X).prod (Order.fin (arity maps))

/-- Select the packed role of an internal field or a party map from its local index and the
chosen shrink layout. -/
def role : (maps : Bool) → Bool → Fin (arity maps) → PackedRole
  | false => ShrinkMotif.internalRole
  | true => ShrinkMotif.partyRole

/-- Packed site owning a given motif's field or map occurrence, found from its surviving role
under the selected layout. -/
noncomputable abbrev place (maps layout : Bool) (x : X.packingData.Motif × Fin (arity maps)) :=
  packedSiteEquiv (X.packingData.survivingRole layout (role maps layout x.2) x.1)

/-- Encode the owner placement as RAM words using the motif-major occurrence order and the
numerical packed-site order. -/
noncomputable abbrev physical (maps layout : Bool) :=
  encodedPlacement (w := w) (oldOrder X maps).entries.symm (packedOrder X).entries.symm (place X maps layout)

/-- The dense CD directory in memory maps each motif index to its old arc's absolute role-table
index. -/
abbrev Absolute (head : Word w) (mem : Memory w) :=
  MotifAbsolute.Directory X.slots X.baseIndex X.shrinkNumber head mem

/-- The sorted scatter uses exactly the motif coordinate of the history cursor. -/
theorem absolute_input {head : Word w} {mem : Memory w} (dir : Absolute X head mem) (m : X.packingData.Motif) :
    (mem (head.val + (ShrinkMotifOrder.stateNumber X m).val)).val = (DemandRAM.absoluteIndex X m.val).val := by
  let E := MotifAbsolute.denseIndex X.packingData (Shrink.packedIndex X.baseIndex) X.shrinkNumber
  have read := dir (E m)
  change (mem (head.val + (E m).val)).val = (DemandRAM.absoluteIndex X (E.symm (E m)).val).val at read
  rw [E.symm_apply_apply] at read
  exact read

variable (maps : Bool) (p : Fin 4 → Word w)

/-- The input rectangles may lie on either side of the fresh owner column. -/
structure Areas : Prop where
  absoluteRoom : (p 0).val + (shrinkMotifOrder X).length ≤ 2^w
  roleRoom : (p 1).val + 4 * DemandRAM.absoluteCount X ≤ 2^w
  ownerRoom : (p 3).val + (oldOrder X maps).length ≤ 2^w
  absoluteApart : (p 0).val + (shrinkMotifOrder X).length ≤ (p 3).val ∨
    (p 3).val + (oldOrder X maps).length ≤ (p 0).val
  roleApart : (p 1).val + 4 * DemandRAM.absoluteCount X ≤ (p 3).val ∨
    (p 3).val + (oldOrder X maps).length ≤ (p 1).val
  radixFits : 6 < 2^w

private theorem motif_lt (m : X.packingData.Motif) : (ShrinkMotifOrder.stateNumber X m).val < (shrinkMotifOrder X).length :=
  ((shrinkMotifOrder X).entries.symm m).isLt

set_option maxHeartbeats 1300000 in
private theorem digits (j : Fin (oldOrder X maps).length) :
    j.val / arity maps = (ShrinkMotifOrder.stateNumber X ((oldOrder X maps).entries j).1).val ∧
    j.val % arity maps = ((oldOrder X maps).entries j).2.val := by
  cases maps with
  | false => exact ShrinkResidentFormula.hiddenDigits X j
  | true => exact ShrinkResidentFormula.mapDigits X j

open private div_cast remainder_cast from OAI.Computability.VPVNP.CompressorShrinkResidentOwners

private theorem cast_val (x : Word w) : (x.val : Word w) = x := Fin.ext (Nat.mod_eq_of_lt x.isLt)

/-- The quotient in the running program reads the sorted absolute-ID cell. -/
theorem absolute_address (areas : Areas X maps p) (j : Fin (oldOrder X maps).length) :
    (absoluteAddr maps p (j.val : Word w)).val =
      (p 0).val + (ShrinkMotifOrder.stateNumber X ((oldOrder X maps).entries j).1).val := by
  let m := ((oldOrder X maps).entries j).1
  have hj : j.val < 2^w := j.isLt.trans_le ((Nat.le_add_left ..).trans areas.ownerRoom)
  have hrad : arity maps < 2^w := (by cases maps <;> decide : arity maps ≤ 6).trans_lt areas.radixFits
  let k := (ShrinkMotifOrder.stateNumber X m).val
  have eqw : p 0+(k : Word w) = (((p 0).val+k : ℕ) : Word w) := by rw [Nat.cast_add,cast_val]
  rw [absoluteAddr_eq,div_cast hj hrad,(digits X maps j).1,eqw]
  exact Nat.mod_eq_of_lt ((Nat.add_lt_add_left (motif_lt X m) _).trans_le areas.absoluteRoom)

private theorem tag_offset {layout : Bool} (side : p 2 = (layout.toNat : Word w))
    (areas : Areas X maps p) (j : Fin (oldOrder X maps).length) :
    offset maps (p 2) (BinaryOp.mod.eval (j.val : Word w) (arity maps : Word w)) =
      (SlotOwners.roleOffset (role maps layout ((oldOrder X maps).entries j).2) : Word w) := by
  have hj : j.val < 2^w := j.isLt.trans_le ((Nat.le_add_left ..).trans areas.ownerRoom)
  have hrad : arity maps < 2^w := (by cases maps <;> decide : arity maps ≤ 6).trans_lt areas.radixFits
  rw [side,remainder_cast hj hrad,(digits X maps j).2]
  cases maps with
  | false => exact offset_hidden layout _ areas.radixFits
  | true => exact offset_party layout _ areas.radixFits

private theorem offset_lt (r : PackedRole) : SlotOwners.roleOffset r < 4 := by cases r <;> decide

private theorem role_lt_end (m : X.packingData.Motif) (r : PackedRole) :
    (p 1).val + 4*(DemandRAM.absoluteIndex X m.val).val + SlotOwners.roleOffset r < (p 1).val + 4 * DemandRAM.absoluteCount X := by
  have bound {i n k : ℕ} (hi : i < n) (hk : k < 4) : 4*i+k < 4*n := by omega
  rw [Nat.add_assoc]
  exact Nat.add_lt_add_left (bound (DemandRAM.absoluteIndex X m.val).isLt (offset_lt r)) _

/-- Combining the scatter read and role digit identifies the actual role-word address. -/
theorem role_address {layout : Bool} {mem : Memory w} (side : p 2 = (layout.toNat : Word w))
    (areas : Areas X maps p) (dir : Absolute X (p 0) mem) (j : Fin (oldOrder X maps).length) :
    let x := (oldOrder X maps).entries j
    (roleAddr maps p mem (j.val : Word w)).val =
      (p 1).val + 4*(DemandRAM.absoluteIndex X x.1.val).val + SlotOwners.roleOffset (role maps layout x.2) := by
  let x := (oldOrder X maps).entries j
  let r := role maps layout x.2
  let abs := (DemandRAM.absoluteIndex X x.1.val).val
  let addr := (absoluteAddr maps p (j.val : Word w)).val
  have hv : (mem addr).val = abs := by
    change (mem (absoluteAddr maps p (j.val : Word w)).val).val = _
    rw [absolute_address X maps p areas j]
    exact absolute_input X dir x.1
  have value : mem addr = (abs : Word w) := by rw [← hv,cast_val]
  rw [roleAddr_eq,tag_offset X maps p side areas j,show mem (absoluteAddr maps p (j.val : Word w)).val = (abs : Word w) from value]
  have eqw : p 1 + 4*(abs : Word w) + (SlotOwners.roleOffset r : Word w) =
      (((p 1).val + 4*abs + SlotOwners.roleOffset r : ℕ) : Word w) := by
    rw [Nat.cast_add,Nat.cast_add,Nat.cast_mul,cast_val]
    rfl
  rw [eqw]
  exact Nat.mod_eq_of_lt ((role_lt_end X p x.1 r).trans_le areas.roleRoom)

private theorem role_read {layout : Bool} {mem : Memory w} (areas : Areas X maps p)
    (newFit : (packedOrder X).length ≤ 2^w) (roles : DemandRAM.RoleColumns X layout (p 1).val mem)
    (j : Fin (oldOrder X maps).length) :
    let x := (oldOrder X maps).entries j
    mem ((p 1).val + 4*(DemandRAM.absoluteIndex X x.1.val).val + SlotOwners.roleOffset (role maps layout x.2)) =
      physical (w := w) X maps layout (j.val : Word w) := by
  have oldFit : (oldOrder X maps).length ≤ 2^w := (Nat.le_add_left ..).trans areas.ownerRoom
  cases maps with
  | false => exact ShrinkResidentFormula.hidden_readback_at X roles oldFit newFit j
  | true => exact ShrinkResidentFormula.map_readback_at X roles oldFit newFit j

/-- Complete physical owner column and the native trace which generated it. -/
structure Written (layout : Bool) (mem : Memory w) (rs : List (Report w)) : Prop where
  native : runSegment ((worker maps).table.instantiate w p).program (1+(code maps).length)
    (some 0) mem (List.replicate (oldOrder X maps).length []) = some rs
  owner (j : Fin (oldOrder X maps).length) :
    after mem (eventLog rs) ((p 3).val+j.val) = physical X maps layout (j.val : Word w)
  frame (addr : ℕ) (outside : addr < (p 3).val ∨ (p 3).val+(oldOrder X maps).length ≤ addr) :
    after mem (eventLog rs) addr = mem addr
  cursor : endState (some 0) rs = some ((oldOrder X maps).length : Word w)
  count : rs.length = (oldOrder X maps).length
  work : ∀ r ∈ rs, r.events.length = (code maps).length ∧ countProbes r.events = 3 ∧ choiceBits r.events = []
  charge : RAMBuckets.cost Report.probes rs = 4*(oldOrder X maps).length

/-- Each native owner word supplies the exact input read of the preimage collector. -/
theorem Written.ownerAt {layout : Bool} {mem : Memory w} {rs : List (Report w)}
    (written : Written X maps p layout mem rs) (areas : Areas X maps p)
    (q : Fin 6 → Word w) (head : q 1 = p 3) (length : (q 0).val = (oldOrder X maps).length)
    (i : Word w) (hi : i < q 0) :
    CompressorRecords.ownerAt q (after mem (eventLog rs)) i = physical X maps layout i := by
  let j : Fin (oldOrder X maps).length := ⟨i.val,(show i.val < (q 0).val from hi).trans_eq length⟩
  have fit : (p 3).val+i.val < 2^w := (Nat.add_lt_add_left j.isLt _).trans_le areas.ownerRoom
  have word : (j.val : Word w) = i := cast_val i
  change after mem (eventLog rs) (q 1+i).val = _
  rw [head,Fin.val_add,Nat.mod_eq_of_lt fit]
  exact (written.owner j).trans (congrArg (physical X maps layout) word)

/-- Scan the sorted absolute-CD input and selected role rows to form the
four-way hidden or six-way map owner column, preserving all other words. -/
theorem run {layout : Bool} {mem : Memory w} (side : p 2 = (layout.toNat : Word w))
    (areas : Areas X maps p) (newFit : (packedOrder X).length ≤ 2^w)
    (dir : Absolute X (p 0) mem) (roles : DemandRAM.RoleColumns X layout (p 1).val mem) :
    ∃ rs, Written X maps p layout mem rs := by
  let n := (oldOrder X maps).length
  have input (i : Word w) (hi : i.val < n) :
      ((absoluteAddr maps p i).val < (p 3).val ∨ (p 3).val+n ≤ (absoluteAddr maps p i).val) ∧
      ((roleAddr maps p mem i).val < (p 3).val ∨ (p 3).val+n ≤ (roleAddr maps p mem i).val) := by
    let j : Fin n := ⟨i.val,hi⟩
    let x := (oldOrder X maps).entries j
    have word : (j.val : Word w) = i := cast_val i
    have absAddr := absolute_address X maps p areas j
    have roleAddr := role_address X maps p side areas dir j
    rw [word] at absAddr roleAddr
    rw [absAddr,roleAddr]
    constructor
    · exact areas.absoluteApart.imp (fun h => (Nat.add_lt_add_left (motif_lt X x.1) _).trans_le h)
        (fun h => h.trans (Nat.le_add_right ..))
    · exact areas.roleApart.imp (fun h => (role_lt_end X p x.1 (role maps layout x.2)).trans_le h)
        (fun h => (h.trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..))
  obtain ⟨rs,exec,read,frame,count,work,charge⟩ :=
    scan_separate maps p mem n areas.ownerRoom input
  have cursor := endState_of_run maps p 0 mem n rs exec
  refine ⟨rs,exec,fun j => ?_,frame,by simpa only [zero_add] using cursor,count,work,charge⟩
  rw [read j,role_address X maps p side areas dir j]
  exact role_read X maps p areas newFit roles j

end CompressorRecords.ShrinkResidentDirectory

end VPVNP
end Computability
end OAI
