import OAI.Computability.VPVNP.CompressorSlotWidth
import OAI.Computability.VPVNP.CompressorSlotOutputLayout
import OAI.Computability.VPVNP.CompressorSlotState

/-!
# The selected shrinking state's canonical width column

The graph and slot order read by the width writer are those used in the
selected compression branch. The old-arc-indexed split words are mapped to
the outgoing ports of the next state in its stored base order.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSlots

open Compression Compression.State Compression.PackingData Compression.ShrinkMotif Compression.ShrinkEnergy
open MotifBlocks MotifGrid MotifConversion Slots SlotLevel SlotOwners SlotSchedule
open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {a b g w : ℕ} {δ factor : ℝ} {k : Type*} [Field k]
variable (X : State a (packingLaneBits a g))
variable (B : FixedBlock k demandSource demandTarget supply (realWidths demandMass) (realWidths supplyMass) (31/16) factor)
variable (ready : Ready (2^a) (2*2^a+1) (2^b) δ) (sel : X.ShrinkSelection B)
private noncomputable local instance : DecidableEq X.Base := Classical.decEq _

/-- Width of the specified motif role edge in the selected term and layout before division into
surviving slots. -/
noncomputable abbrev branchWidth (m : X.packingData.Motif) (t : Fin 4) :=
  X.packingData.termWidths B X.shrinkNumber X.packingWidth sel m (selectedLayout X B sel) t

/-- The shared port lengths agree with the branch's own base and lane cardinals. -/
theorem next_counts :
    let s := levelShape (b := b) X
    let Y := X.shrinkNext B ready sel
    Fintype.card Y.Base*2^b=baseArcs s ∧ Fintype.card Y.Base*2^g*2^b=actualCount s := by
  intro s Y
  change Fintype.card (X.Base×BitWord (packingTagBits (2^a))) * 2^b = _ ∧
    Fintype.card (X.Base×BitWord (packingTagBits (2^a))) * 2^g * 2^b = _
  rw [Fintype.card_prod]
  have card := (Fintype.card_congr (bitWordFinEquiv (packingTagBits (2^a)))).trans (Fintype.card_fin _)
  rw [card]
  exact ⟨rfl,by change _ = (Fintype.card X.Base * (2^packingTagBits (2^a)*2^g))*2^b; ring⟩

/-- Re-association of base, tag and remaining lane in the two mixed-radix
implementations produces the same canonical port number. -/
theorem portIndex_next (e : ((X.shrinkNext B ready sel).Base × BitWord g) × Fin (2^b)) :
    (SlotWidthScan.portIndex X.baseIndex (bitWordFinEquiv (packingTagBits (2^a))) (bitWordFinEquiv g) e).val =
      (IncidenceDirectory.actualOrder (X.shrinkNext B ready sel) e).val := by
  let v := (X.baseIndex e.1.1.1).val
  let t := (bitWordFinEquiv (packingTagBits (2^a)) e.1.1.2).val
  let l := (bitWordFinEquiv g e.1.2).val
  let J := 2^packingTagBits (2^a)
  change e.2.val+2^b*(l+2^g*t+(J*2^g)*v) = e.2.val+2^b*(l+2^g*(t+J*v))
  ring

/-- Actual native width scan in state coordinates. Its input split rows can
be the simultaneously established rows of `ShrinkSliceSweep.graph_run`. -/
theorem width_run (h : Heads) (splitHead : ℕ) (m : Memory w) :
    let s := levelShape (b := b) X
    let l := selectedLayout X B sel
    let P := X.packingData
    let tags := bitWordFinEquiv (packingTagBits (2^a))
    let lanes := bitWordFinEquiv g
    let D := slotDirectory P s.subdivisions X.baseIndex tags lanes l (pad := pad s)
    let hD := fun v ↦ (slotDirectory_degree P s.subdivisions X.baseIndex tags lanes (two_le_packingColors a) l v).trans
      (Nat.add_sub_of_le ready.degree_budget)
    let p := widthBank s h splitHead w
    let M := (template SlotWidthScan.visit 0).instantiate w p
    let Y := X.shrinkNext B ready sel
    2 < 2^w → 2^b < 2^w → 2^g < 2^w → (∑t,s.subdivisions t) < 2^w →
    oldBaseArcCount s.bases s.tags s.oldDegree s.colors < 2^w →
    splitHead+(oldBaseArcCount s.bases s.tags s.oldDegree s.colors*s.lanes)*4*(∑ t,s.subdivisions t) ≤ h.scratch →
    finish s h < 2^w → SlotWidthScan.SplitRows P s.subdivisions X.baseIndex tags lanes (branchWidth X B sel) splitHead m →
    (∀ x, m (rowsHead s h+(sortedFields D (2^b) hD x).val) = Fin.ofNat _ (D.address x).val) →
    ∃ rs, runSegment M.program 43 (some 0) m (List.replicate (actualCount s) []) = some rs ∧
      endState (some 0) rs = some (Fin.ofNat _ (actualCount s)) ∧
      (∀ e, after m (eventLog rs) (widthHead s h+(IncidenceDirectory.actualOrder Y e).val) =
        Fin.ofNat _ (Y.width ((e.1.1,e.2),e.1.2))) ∧
      (∀ addr, addr < widthHead s h ∨ finish s h ≤ addr → after m (eventLog rs) addr=m addr) ∧
      RAMBuckets.cost Report.probes rs = 4*actualCount s := by
  intro s l P tags lanes D hD p M Y hw hdw hlw hsw hbw room fit split rows
  have hrow : rowsHead s h+owners s*s.newDegree ≤ inverseHead s h :=
    Nat.add_le_add_left (Nat.mul_le_mul_right s.newDegree (Nat.le_add_right (owners s) (fields s))) _
  have hheads : h.scratch ≤ rowsHead s h ∧ inverseHead s h+fields s ≤ widthHead s h ∧ widthHead s h+actualCount s=finish s h := by
    refine ⟨(Nat.le_add_right h.scratch (fields s)).trans (Nat.le_add_right _ _), ?_, rfl⟩
    change targetsHead s h ≤ widthHead s h
    calc
      targetsHead s h ≤ shiftsHead s h := Nat.le_add_right _ _
      _ ≤ inverseBaseHead s h := Nat.le_add_right _ _
      _ ≤ outHead s h := Nat.le_add_right _ _
      _ ≤ inHead s h := Nat.le_add_right _ _
      _ ≤ widthHead s h := Nat.le_add_right _ _
  have hgen : keyCount s.bases s.tags s.oldDegree s.colors s.subdivisions*s.lanes ≤ fields s := by
    unfold fields RecordCount; omega
  have hP0 : (p 0).val=2^b := Nat.mod_eq_of_lt hdw
  have hP1 : (p 1).val=2^g := Nat.mod_eq_of_lt hlw
  have hP2 : (p 2).val=∑t,s.subdivisions t := Nat.mod_eq_of_lt hsw
  have hP3 : (p 3).val=oldBaseArcCount s.bases s.tags s.oldDegree s.colors := Nat.mod_eq_of_lt hbw
  have hP4 : (p 4).val=keyCount s.bases s.tags s.oldDegree s.colors s.subdivisions*s.lanes :=
    Nat.mod_eq_of_lt (by omega : keyCount s.bases s.tags s.oldDegree s.colors s.subdivisions*s.lanes < 2^w)
  have hP5 : (p 5).val=rowsHead s h := Nat.mod_eq_of_lt (by omega : rowsHead s h < 2^w)
  have hP6 : (p 6).val=splitHead := Nat.mod_eq_of_lt (by omega : splitHead < 2^w)
  have hP7 : (p 7).val=widthHead s h := Nat.mod_eq_of_lt (by omega : widthHead s h < 2^w)
  have hpos : 0 < actualCount s := by
    rw [← (next_counts X B ready sel).2]; positivity
  have hbase : h.scratch < widthHead s h := by
    simp only [widthHead,inHead,outHead,inverseBaseHead,stopAddress,shiftsHead,targetsHead,inverseHead,rowsHead]; omega
  obtain ⟨rs,hr,hc,output,frame,cost⟩ := SlotWidthScan.write_all P s.subdivisions X.baseIndex tags lanes l
    (branchWidth X B sel) (two_le_packingColors a) (orderedDyadicPacking_validTags X.slots X.baseIndex)
    ready.degree_budget (Nat.one_lt_two_pow (Nat.succ_pos _).ne') p m hP0 hP1 hP2 hP3 hP4 hw
    (by rw [hP5,hP7]; change rowsHead s h+owners s*s.newDegree ≤ widthHead s h; omega)
    (by rw [hP6,hP7]; exact room.trans hbase.le) (by rw [hP6,hP7]; omega) (hP6 ▸ split)
    (by rw [hP7]; change widthHead s h+actualCount s ≤ 2^w; omega)
    (fun x ↦ hP5 ▸ rows x) (by change fields s ≤ 2^w; omega)
  refine ⟨rs,hr,hc,?_,?_,cost⟩
  · intro e
    have he := output e
    rw [hP7,portIndex_next X B ready sel] at he
    exact he
  · intro addr ha; exact frame addr (by rw [hP7]; change addr < widthHead s h ∨ widthHead s h+actualCount s ≤ addr; omega)

end CompressorRecords.ShrinkSlots

end VPVNP
end Computability
end OAI
