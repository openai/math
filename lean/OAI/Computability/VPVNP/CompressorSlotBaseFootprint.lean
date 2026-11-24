import OAI.Computability.VPVNP.CompressorSlotLevelRun
import OAI.Computability.VPVNP.CompressorRefreshStageFrame

/-!
# External addresses of the lane-zero base matching scan

Each base arc uses the real outgoing row to locate the adjacent incoming
field in the inverse table. Both lookups precede the output columns, so
the same sorted endpoint tables remain valid on every visit. The native
reports read within the row and inverse tables and write within the target
and displacement columns.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SlotLevel

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM SourceTransport
open Compression Compression.PackingData Compression.SurvivingSlots Slots SlotSchedule
open scoped Fin.CommRing

variable {w : ℕ}

/-- The sorted endpoint rows and inverse field directory. -/
def BaseReadRegion (s : Shape) (h : Heads) (x : ℕ) : Prop :=
  rowsHead s h ≤ x ∧ x < targetsHead s h

/-- The target and displacement columns written by the base matching scan. -/
def BaseWriteRegion (s : Shape) (h : Heads) (x : ℕ) : Prop :=
  targetsHead s h ≤ x ∧ x < stopAddress s h

private theorem write_row (s : Shape) (h : Heads) (fit : stopAddress s h < 2^w)
    (m : Memory w) {j : ℕ} (hj : j < baseArcs s) :
    Writes (BaseWriteRegion s h) (SlotBaseScan.events (bank s h w .baseMatching) m (j : Word w)) := by
  let q := bank s h w .baseMatching
  have htgt : targetsHead s h + baseArcs s = shiftsHead s h := rfl
  have hsh : shiftsHead s h + baseArcs s = stopAddress s h := rfl
  have q4 : (q 4).val = targetsHead s h := Nat.mod_eq_of_lt (by omega : targetsHead s h < 2^w)
  have q5 : (q 5).val = shiftsHead s h := Nat.mod_eq_of_lt (by omega : shiftsHead s h < 2^w)
  have hj' : (j : Word w).val = j := Nat.mod_eq_of_lt (by omega)
  intro a v ha
  change Event.write a v ∈ SlotBaseScan.events q m (j : Word w) at ha
  simp [SlotBaseScan.events] at ha
  rcases ha with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> unfold BaseWriteRegion
  · rw [Fin.val_add,q4,hj',Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Fin.val_add,q5,hj',Nat.mod_eq_of_lt (by omega)]
    omega

/-- Lift read bounds on a single visit to its full segment. All earlier
writes are above the two input tables. -/
private theorem scan_regions (s : Shape) (h : Heads) (m : Memory w) (rs : List (Report w))
    (fit : stopAddress s h < 2^w) (readable : ℕ → Prop)
    (rd : ∀ j < baseArcs s, ∀ curr : Memory w, Agree (BaseReadRegion s h) m curr →
      Reads readable (SlotBaseScan.events (bank s h w .baseMatching) curr (j : Word w)))
    (run : runSegment ((template SlotBaseScan.code 0).instantiate w (bank s h w .baseMatching)).program
      33 (some 0) m (List.replicate (baseArcs s) []) = some rs) :
    StageFrame.Scanned 0 (baseArcs s) rs ∧ Reads readable (eventLog rs) ∧
      Writes (BaseWriteRegion s h) (eventLog rs) := by
  let q := bank s h w .baseMatching
  let P := ((template SlotBaseScan.code 0).instantiate w q).program
  have step (j : ℕ) (_ : 0 ≤ j) (hj : j < baseArcs s) (curr : Memory w)
      (agree : Agree (BaseReadRegion s h) m curr) :
      Agree (BaseReadRegion s h) m (after curr (SlotBaseScan.events q curr (j : Word w))) ∧
      Reads readable (SlotBaseScan.events q curr (j : Word w)) ∧
      Writes (BaseWriteRegion s h) (SlotBaseScan.events q curr (j : Word w)) := by
    have wr := write_row s h fit curr hj
    refine ⟨fun x hx ↦ (agree x hx).trans (after_outside curr wr ?_).symm, rd j hj curr agree, wr⟩
    exact fun hw ↦ hx.2.not_ge hw.1
  have hs := StageFrame.scan P 33 0 (baseArcs s) (fun _ ↦ Agree (BaseReadRegion s h) m)
    (SlotBaseScan.events q) readable (BaseWriteRegion s h) (fun j _ _ curr ↦ SlotBaseScan.native q curr _)
    step (Nat.zero_le _) m rs (fun _ _ ↦ rfl) (by simpa using run)
  exact ⟨hs.1, hs.2.2⟩

variable {V H Tag L : Type*} {d c N J nL degree : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L] [Module (ZMod 2) Tag]
variable (P : PackingData V H Tag L d c) (subdiv : Fin 4 → ℕ)
variable (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (lanes : L ≃ Fin nL)

/-- In the memory left by scatter, the sorted source row contains the field of
the lane-zero outgoing end. Its successor is the incoming field of the same
arc. These two fitting addresses account for every external read of the pass. -/
theorem base_footprint (layout : Bool) (h : Heads) (hc : 2 ≤ c)
    (hφ : P.slots.ValidTagOffsets P.tagShift P.offset) (hd : survivingDegree d c subdiv ≤ degree)
    (hJ : 1 < J) (hlane : (lanes 0).val = 0) (hw : 2 < 2^w)
    (hdw : degree < 2^w) (hlw : nL < 2^w) (m : Memory w) (rs : List (Report w)) :
    let s : Shape := ⟨N,J,nL,d,c,subdiv,degree⟩
    let D := slotDirectory P subdiv vertices tags lanes layout (pad := pad s)
    let hD := fun b ↦ (slotDirectory_degree P subdiv vertices tags lanes hc layout b).trans (Nat.add_sub_of_le hd)
    let q := bank s h w .baseMatching
    stopAddress s h < 2^w → Tables D degree (rowsHead s h) (inverseHead s h) hD m →
    runSegment ((template SlotBaseScan.code 0).instantiate w q).program 33
      (some 0) m (List.replicate (baseArcs s) []) = some rs →
    StageFrame.Scanned 0 (baseArcs s) rs ∧ Reads (BaseReadRegion s h) (eventLog rs) ∧
      Writes (BaseWriteRegion s h) (eventLog rs) := by
  intro s D hD q fit tab run
  apply scan_regions s h m rs fit _ _ run
  intro j hj curr agree
  have rowCap : rowsHead s h + owners s * degree ≤ inverseHead s h :=
    Nat.add_le_add_left (Nat.mul_le_mul_right degree (Nat.le_add_right (owners s) (fields s))) _
  have hf : inverseHead s h + fields s = targetsHead s h := rfl
  have ht : targetsHead s h + baseArcs s = shiftsHead s h := rfl
  have hs : shiftsHead s h + baseArcs s = stopAddress s h := rfl
  let e := (baseIndex vertices tags (degree := degree)).symm ⟨j,hj⟩
  have he : (baseIndex vertices tags e).val = j :=
    congrArg Fin.val ((baseIndex vertices tags).apply_symm_apply ⟨j,hj⟩)
  have hb := base_lookup P subdiv vertices tags lanes hc hφ layout hd hJ hlane m e
    (by change fields s ≤ 2^w; omega) (by change owners s * degree ≤ 2^w; omega) tab
  rw [he] at hb
  let source := laneZeroRow degree nL j
  have hsource : source < owners s * degree := hb.1
  have hread : BaseReadRegion s h (rowsHead s h + source) := by
    unfold BaseReadRegion; omega
  have hfield : (curr (rowsHead s h + source)).val + 1 < fields s := by
    rw [← agree _ hread]
    exact hb.2.1
  have q0 : (q 0).val = degree := Nat.mod_eq_of_lt hdw
  have q1 : (q 1).val = nL := Nat.mod_eq_of_lt hlw
  have q2 : (q 2).val = rowsHead s h := Nat.mod_eq_of_lt (by omega : rowsHead s h < 2^w)
  have q3 : (q 3).val = inverseHead s h := Nat.mod_eq_of_lt (by omega : inverseHead s h < 2^w)
  have ji : (j : Word w).val = j := Nat.mod_eq_of_lt (by omega)
  have addrs := SlotBaseScan.read_addresses q curr (j : Word w) hw
    (by rw [q0,q1,q2,ji]; change rowsHead s h + source < 2^w; omega)
    (by dsimp only; rw [q0,q1,q2,q3,ji]; change inverseHead s h + ((curr (rowsHead s h + source)).val+1) < 2^w; omega)
  dsimp only at addrs
  rw [q0,q1,q2,q3,ji] at addrs
  change (SlotBaseScan.rowAddr q (j : Word w)).val = rowsHead s h + source ∧
    (SlotBaseScan.invAddr q curr (j : Word w)).val =
      inverseHead s h + ((curr (rowsHead s h + source)).val+1) at addrs
  intro a v ha
  change Event.read a v ∈ SlotBaseScan.events q curr (j : Word w) at ha
  simp [SlotBaseScan.events] at ha
  rcases ha with ⟨rfl,_⟩ | ⟨rfl,_⟩
  · rwa [addrs.1]
  · rw [addrs.2]
    unfold BaseReadRegion
    omega

/-- The native reports and final tables supplied by `run_selected` suffice:
the base pass writes only above the scatter tables, so the final table
readback also holds at entry to this pass. -/
theorem selected_base_footprint (layout : Bool) (h : Heads) (hc : 2 ≤ c)
    (hφ : P.slots.ValidTagOffsets P.tagShift P.offset) (hd : survivingDegree d c subdiv ≤ degree)
    (hJ : 1 < J) (hlane : (lanes 0).val = 0) (hw : 2 < 2^w)
    (hdw : degree < 2^w) (hlw : nL < 2^w) (mem : Memory w) (r : Reports w) :
    let s : Shape := ⟨N,J,nL,d,c,subdiv,degree⟩
    let D := slotDirectory P subdiv vertices tags lanes layout (pad := pad s)
    let hD := fun b ↦ (slotDirectory_degree P subdiv vertices tags lanes hc layout b).trans (Nat.add_sub_of_le hd)
    stopAddress s h < 2^w → r.Native s h mem →
    Tables D degree (rowsHead s h) (inverseHead s h) hD (r.final mem) →
    StageFrame.Scanned 0 (baseArcs s) r.bases ∧ Reads (BaseReadRegion s h) (eventLog r.bases) ∧
      Writes (BaseWriteRegion s h) (eventLog r.bases) := by
  intro s D hD fit native tab
  let m := after (after (after (after mem (eventLog r.genuine)) (eventLog r.dummy)) (eventLog r.append))
    (eventLog r.scatter)
  have run := native.2.2.2.2
  have wr := (scan_regions s h m r.bases fit (fun _ ↦ True) (fun _ _ _ _ _ _ _ ↦ trivial) run).2.2
  have same (x : ℕ) (hx : x < targetsHead s h) : r.final mem x = m x :=
    after_outside m wr (fun hw ↦ hx.not_ge hw.1)
  apply base_footprint P subdiv vertices tags lanes layout h hc hφ hd hJ hlane hw hdw hlw m r.bases fit _ run
  have rowCap : rowsHead s h + owners s * degree ≤ inverseHead s h :=
    Nat.add_le_add_left (Nat.mul_le_mul_right degree (Nat.le_add_right (owners s) (fields s))) _
  have hf : inverseHead s h + fields s = targetsHead s h := rfl
  constructor
  · intro e
    have he : (sortedFields D degree hD e).val < owners s * degree := (sortedFields D degree hD e).isLt
    exact (same (rowsHead s h + (sortedFields D degree hD e).val) (by omega)).symm.trans (tab.bySlot e)
  · intro e
    have he : (D.address e).val < fields s := (D.address e).isLt
    exact (same (inverseHead s h + (D.address e).val) (by omega)).symm.trans (tab.byField e)

end CompressorRecords.SlotLevel

end VPVNP
end Computability
end OAI
