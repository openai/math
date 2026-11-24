import OAI.Computability.VPVNP.CompressorSlotBuildInputs
import OAI.Computability.VPVNP.CompressorSlotFinish

/-!
# Complete shrinking slot and incidence construction from the selected rows

The demand-role scan supplies the CD indicator and three packed role sites
on each old arc. The term/slice scan supplies each genuine subdivision width.
Beginning with those rows, native preparation, ordering, inversion and width
scans construct all six incidence columns for the very next compressor state.
The scratch and output counters may initially contain arbitrary words.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSlots.Build

open Compression Compression.State Compression.PackingData Compression.ShrinkMotif Compression.ShrinkEnergy
open MotifBlocks MotifGrid MotifConversion Slots SlotLevel SlotOwners SlotSchedule
open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

/-- Reports for a complete shrinking slot construction, from preparing the selected input
tables to writing the next state's incidence columns. -/
structure Construction (w : ℕ) where
  /-- Reports for publishing subdivisions, building the role and successor tables, and clearing
  the append counters. -/
  prepare : Preparation.Reports w
  /-- Reports for constructing the slot and mate directories and gathering their widths from
  the prepared inputs. -/
  passes : Passes w

/-- All preparation and construction reports in execution order. -/
def Construction.all {w : ℕ} (r : Construction w) := r.prepare.all++r.passes.all

/-- Memory after replaying the preparation reports and then the slot, mate, and width passes. -/
def Construction.final {w : ℕ} (r : Construction w) (m : Memory w) := r.passes.final (r.prepare.final m)

/-- The memory consumed by the next level is the replay of this construction's chronological log. -/
theorem Construction.final_eq {w : ℕ} (r : Construction w) (m : Memory w) :
    r.final m = after m (eventLog r.all) := by
  simp only [Construction.all, Construction.final, Preparation.Reports.final, Passes.all, Passes.final,
    SlotLevel.Reports.all, SlotLevel.Reports.final, MateReports.all, MateReports.final, eventLog,
    List.flatMap_append, after, List.foldl_append]

/-- The preparation and construction reports are produced by their respective native workers,
with construction starting from the prepared memory. -/
def Construction.Native {w : ℕ} (r : Construction w) (s : Shape) (h : Heads) (splitHead : ℕ) (layout : Bool) (m : Memory w) :=
  r.prepare.Native s h layout m ∧ r.passes.Native s h splitHead (r.prepare.final m)

/-- All preparation and construction passes return their prescribed ending cursors for this
level. -/
def Construction.Cursors {w : ℕ} (r : Construction w) (s : Shape) := r.prepare.Cursors s ∧ r.passes.Cursors s

variable {a b g w : ℕ} {δ factor : ℝ} {k : Type*} [_root_.Field k]
variable (X : State a (packingLaneBits a g))
variable (B : FixedBlock k demandSource demandTarget supply (realWidths demandMass) (realWidths supplyMass) (31/16) factor)
variable (ready : Ready (2^a) (2*2^a+1) (2^b) δ) (sel : X.ShrinkSelection B)
private noncomputable local instance : DecidableEq X.Base := Classical.decEq _

/-- Convert the simultaneous natural-number width readback of the selected
slice sweep to the word representation used by the ordered incidence passes. -/
theorem splitRows_of_values (subdiv : Fin 4 → ℕ) (base : ℕ) (mem : Memory w)
    (width : X.packingData.Motif → Fin 4 → ℕ)
    (values : ∀ m t (j : Fin (subdiv t)),
      (mem (base + (((oldArcIndex X.packingData X.baseIndex (bitWordFinEquiv (packingTagBits (2^a)))
        (bitWordFinEquiv g) m.val).val * 4 + t.val) * (∑ e, subdiv e) + j.val))).val =
        splitWidth (width m t) (subdiv t) j) :
    SlotWidthScan.SplitRows X.packingData subdiv X.baseIndex (bitWordFinEquiv (packingTagBits (2^a)))
      (bitWordFinEquiv g) width base mem := by
  intro i
  apply Fin.ext
  rw [Fin.val_ofNat, ← values i.2.1 i.1 i.2.2, Nat.mod_eq_of_lt (mem _).isLt]

/-- Construct the complete shared incidence directory in arbitrary initial
scratch memory. Source word bounds are the live radices of the level.
The frame covers every earlier input and every later reserved address. -/
theorem build (h : Heads) (splitHead : ℕ) (mem : Memory w) :
    let s := levelShape (b := b) X
    let layout := selectedLayout X B sel
    let tags := bitWordFinEquiv (packingTagBits (2^a))
    let lanes := bitWordFinEquiv g
    let splits := SlotWidthScan.SplitRows X.packingData s.subdivisions X.baseIndex tags lanes (branchWidth X B sel) splitHead
    DemandRAM.RoleColumns X layout h.oldArc mem → splits mem →
    h.oldArc+4*DemandRAM.absoluteCount X ≤ h.role →
    splitHead+(oldBaseArcCount s.bases s.tags s.oldDegree s.colors*s.lanes)*4*(∑ t,s.subdivisions t) ≤ h.role →
    h.role+8 ≤ h.nextSite → h.nextSite+sites s ≤ h.subdivisions → h.subdivisions+4 ≤ h.scratch →
    finish s h < 2^w → s.lanes < 2^w → s.tags < 2^w → (∑t,s.subdivisions t)<2^w → s.newDegree<2^w →
    ∃ r : Construction w, r.Native s h splitHead layout mem ∧ r.Cursors s ∧
      (directory s h w).Represents (X.shrinkNext B ready sel) (r.final mem) ∧
      DemandRAM.RoleColumns X layout h.oldArc (r.final mem) ∧ splits (r.final mem) ∧
      (∀ addr, addr < h.role ∨ finish s h ≤ addr → r.final mem addr=mem addr) ∧
      RAMBuckets.cost Report.probes r.all = (24+2*sites s+2*(owners s+fields s))+
        (6*genuineCount s+3*dummyCount s+5*fields s+3*(owners s*2^b)+8*baseArcs s+12*actualCount s) := by
  intro s layout tags lanes splits roles split oldRoom splitRoom roleRoom nextRoom subRoom fit lw tw sw dw
  have hr : h.scratch ≤ rowsHead s h := by unfold rowsHead; omega
  have hs : rowsHead s h ≤ finish s h := by
    calc
      _ ≤ inverseHead s h := Nat.le_add_right _ _
      _ ≤ targetsHead s h := Nat.le_add_right _ _
      _ ≤ shiftsHead s h := Nat.le_add_right _ _
      _ ≤ inverseBaseHead s h := Nat.le_add_right _ _
      _ ≤ outHead s h := Nat.le_add_right _ _
      _ ≤ inHead s h := Nat.le_add_right _ _
      _ ≤ widthHead s h := Nat.le_add_right _ _
      _ ≤ finish s h := Nat.le_add_right _ _
  obtain ⟨prep,hp,cursor,gTable,dTable,zero,fp,prepCost⟩ := Preparation.run (b := b) X h layout mem roles
    oldRoom roleRoom nextRoom subRoom (hs.trans_lt fit) lw tw sw dw
  let mp := prep.final mem
  have split' : splits mp := SlotWidthScan.SplitRows.congr_below _ _ _ _ _ split splitRoom (fun addr ha ↦ fp addr (Or.inl ha))
  have oldRoom' : h.oldArc+4*(oldBaseArcCount s.bases s.tags s.oldDegree s.colors*s.lanes) ≤ h.scratch := by
    change h.oldArc+4*DemandRAM.absoluteCount X ≤ h.scratch; omega
  obtain ⟨result,native,cursors,rep,fr,cost⟩ := from_prepared X B ready sel h splitHead mp dw gTable dTable
    split' oldRoom' (by omega) subRoom (nextRoom.trans (by omega)) (splitRoom.trans (by omega)) fit zero
  let r : Construction w := ⟨prep,result⟩
  have frame (addr : ℕ) (ha : addr < h.role ∨ finish s h ≤ addr) : r.final mem addr=mem addr :=
    (fr addr (by change addr<h.scratch ∨ finish s h≤addr; omega)).trans
      (fp addr (by change addr<h.role ∨ rowsHead s h ≤ addr; omega))
  obtain ⟨oldCols,oldWidths⟩ := Preparation.preserve_rows (b := b) X h layout splitHead (branchWidth X B sel)
    mem (r.final mem) oldRoom splitRoom (fun addr ha ↦ frame addr (Or.inl ha)) roles split
  refine ⟨r,⟨hp,native⟩,⟨cursor,cursors⟩,rep,oldCols,oldWidths,frame,?_⟩
  exact (RAMBuckets.cost_append Report.probes prep.all result.all).trans (congrArg₂ (·+·) prepCost cost)

end CompressorRecords.ShrinkSlots.Build

end VPVNP
end Computability
end OAI
