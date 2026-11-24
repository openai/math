import OAI.Computability.VPVNP.CompressorSlotOwnerFootprint
import OAI.Computability.VPVNP.CompressorSlotFillFootprint
import OAI.Computability.VPVNP.CompressorSlotBaseFootprint
import OAI.Computability.VPVNP.CompressorSlotRunUnique
import OAI.Computability.VPVNP.CompressorShrinkSlotFootprint

/-!
# Access bounds of the five sorted-slot workers on the selected branch

Recover the owner records, zero counters and sorted fields at their actual
phase boundaries. This gives the addresses of every emitted probe, including
the indirect row and inverse-field lookups.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSlots.Build

open Compression Compression.State Compression.PackingData Compression.ShrinkMotif Compression.ShrinkEnergy
open MotifBlocks MotifGrid MotifConversion Slots SlotLevel SlotOwners SlotSchedule
open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

/-- The physical inputs used by the branch and all intermediate slot arrays. -/
def readRegion (s : Shape) (h : Heads) (splitHead x : ℕ) :=
  min h.oldArc splitHead ≤ x ∧ x < finish s h

/-- Slot outputs including the small preparation tables. -/
def writeRegion (s : Shape) (h : Heads) (x : ℕ) := h.role ≤ x ∧ x < finish s h

/-- Bounds used to allocate and instantiate the native shrinking workers. -/
structure Space (s : Shape) (h : Heads) (splitHead w : ℕ) : Prop where
  old : h.oldArc + SlotOwnerFootprint.oldWords s ≤ h.role
  split : splitHead+(oldBaseArcCount s.bases s.tags s.oldDegree s.colors*s.lanes)*4*(∑t,s.subdivisions t) ≤ h.role
  roles : h.role+8 ≤ h.nextSite
  next : h.nextSite+sites s ≤ h.subdivisions
  subdiv : h.subdivisions+4 ≤ h.scratch
  fit : finish s h < 2^w
  lanes : s.lanes < 2^w
  tags : s.tags < 2^w
  profile : (∑t,s.subdivisions t) < 2^w
  degree : s.newDegree < 2^w

variable {a b g w : ℕ} {δ factor : ℝ} {k : Type*} [_root_.Field k]
variable (X : State a (packingLaneBits a g))
variable (B : FixedBlock k demandSource demandTarget supply (realWidths demandMass) (realWidths supplyMass) (31/16) factor)
variable (ready : Ready (2^a) (2*2^a+1) (2^b) δ) (sel : X.ShrinkSelection B)
private noncomputable local instance : DecidableEq X.Base := Classical.decEq _

/-- The two-way rectangular slot order on this actual selected network. -/
noncomputable abbrev OrderedTables (side : Bool) (h : Heads) (mem : Memory w) :=
  let s := levelShape (b := b) X
  let tags := bitWordFinEquiv (packingTagBits (2^a))
  let D := slotDirectory X.packingData s.subdivisions X.baseIndex tags (bitWordFinEquiv g) side (pad := pad s)
  let degree := fun v ↦ (slotDirectory_degree X.packingData s.subdivisions X.baseIndex tags (bitWordFinEquiv g)
    (two_le_packingColors a) side v).trans (Nat.add_sub_of_le ready.degree_budget)
  Tables D (2^b) (rowsHead s h) (inverseHead s h) degree mem

set_option maxHeartbeats 1000000 in
/-- All five sorted-slot phases access the allocated data, and the exact
post-memory supplies the typed base matching for the subsequent mate scans. -/
theorem core_access (h : Heads) (splitHead : ℕ) (mem : Memory w) (r : Construction w) :
    let s := levelShape (b := b) X
    let side := selectedLayout X B sel
    Space s h splitHead w → DemandRAM.RoleColumns X side h.oldArc mem →
    r.Native s h splitHead side mem →
      LogAccess (readRegion s h splitHead) (writeRegion s h) r.passes.slots.all ∧
      BaseForward (X.shrinkNext B ready sel) (targetsHead s h) (shiftsHead s h)
        (r.passes.slots.final (r.prepare.final mem)) ∧
      2 < 2^w ∧ oldBaseArcCount s.bases s.tags s.oldDegree s.colors < 2^w ∧
      OrderedTables X ready side h (r.passes.slots.final (r.prepare.final mem)) := by
  intro s side sp roles native
  let P := X.packingData
  let tags := bitWordFinEquiv (packingTagBits (2^a))
  let lanes := bitWordFinEquiv g
  let D := slotDirectory P s.subdivisions X.baseIndex tags lanes side (pad := pad s)
  let degree := fun v ↦ (slotDirectory_degree P s.subdivisions X.baseIndex tags lanes (two_le_packingColors a) side v).trans
    (Nat.add_sub_of_le ready.degree_budget)
  have h0 := sp.old
  have h1 := sp.roles
  have h2 := sp.next
  have h3 := sp.subdiv
  have f0 : h.scratch+fields s ≤ rowsHead s h := Nat.le_add_right _ _
  have f1 : rowsHead s h+owners s*s.newDegree ≤ inverseHead s h :=
    Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)) _
  have f2 : inverseHead s h ≤ targetsHead s h := Nat.le_add_right _ _
  have f3 : targetsHead s h ≤ stopAddress s h := (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  have f4 : stopAddress s h ≤ finish s h := by unfold finish widthHead inHead outHead inverseBaseHead; omega
  have fit := sp.fit
  have oldBound : h.oldArc + SlotOwnerFootprint.oldWords s ≤ h.scratch := by omega
  have roleBound : h.role+8 ≤ h.scratch := by omega
  have nextBound : h.nextSite+sites s ≤ h.scratch := by omega
  have cap : stopAddress s h < 2^w := f4.trans_lt fit
  have capRows : rowsHead s h < 2^w := by omega
  obtain ⟨prep,pn,_,genuine,dummy,zero,_,_⟩ := Preparation.run (b := b) X h side mem roles h0 h1 h2 h3
    capRows sp.lanes sp.tags sp.profile sp.degree
  obtain rfl := pn.unique native.1
  let mp := r.prepare.final mem
  let rs := r.passes.slots
  have rn : rs.Native s h mp := native.2.1
  obtain ⟨rs',rn',_,tables,forward,_,_⟩ := next_run X B ready sel h mp sp.degree genuine dummy
    oldBound roleBound h3 nextBound cap zero
  obtain rfl := rn'.unique rn
  obtain ⟨gr,dr⟩ := SlotOwnerFootprint.of_tables (degree := s.newDegree) P s.subdivisions X.baseIndex tags lanes
    side h mp rs genuine dummy oldBound roleBound h3 nextBound cap rn
  have input := input_of_tables (degree := s.newDegree) P s.subdivisions X.baseIndex tags lanes
    side mp h genuine dummy oldBound roleBound h3 nextBound cap
  obtain ⟨ar,ir⟩ := SlotFillFootprint.selected s h D input (Nat.two_pow_pos b) sp.degree degree cap zero rn
  have hJ : 1 < 2^packingTagBits (2^a) := Nat.one_lt_two_pow (Nat.succ_pos _).ne'
  have zeroLane : (lanes 0).val = 0 := by simpa using bitWordFinEquiv_add_val (0 : BitWord g) 0
  obtain ⟨_,br⟩ := selected_base_footprint P s.subdivisions X.baseIndex tags lanes side h (two_le_packingColors a)
    (orderedDyadicPacking_validTags X.slots X.baseIndex) ready.degree_budget hJ zeroLane dummy.twoFits
    sp.degree sp.lanes mp rs cap rn tables
  have lower := min_le_left h.oldArc splitHead
  have sizes := counts_add s
  let rd := readRegion s h splitHead
  let wr := writeRegion s h
  have g' : LogAccess rd wr rs.genuine := LogAccess.mono gr (fun x hx ↦ by
    change SlotOwnerFootprint.interval h.oldArc (SlotOwnerFootprint.oldWords s) x ∨
      SlotOwnerFootprint.interval h.role 8 x ∨ SlotOwnerFootprint.interval h.subdivisions 4 x at hx
    unfold SlotOwnerFootprint.interval at hx
    change min h.oldArc splitHead ≤ x ∧ x < finish s h; rcases hx with hx|hx|hx <;> omega)
    (fun x hx ↦ by change h.scratch≤x ∧ x<h.scratch+genuineCount s at hx; change h.role≤x ∧ x<finish s h; omega)
  have d' : LogAccess rd wr rs.dummy := LogAccess.mono dr
    (fun x hx ↦ by change h.nextSite≤x ∧ x<h.nextSite+sites s at hx; change min h.oldArc splitHead≤x ∧ x<finish s h; omega)
    (fun x hx ↦ by change h.scratch+genuineCount s≤x ∧ x<h.scratch+genuineCount s+dummyCount s at hx
                   change h.role≤x ∧ x<finish s h; omega)
  have a' : LogAccess rd wr rs.append := LogAccess.mono ar (fun x hx ↦ by change min h.oldArc splitHead≤x ∧ x<finish s h; omega)
    (fun x hx ↦ by change h.role≤x ∧ x<finish s h; omega)
  have i' : LogAccess rd wr rs.scatter := LogAccess.mono ir (fun x hx ↦ by change min h.oldArc splitHead≤x ∧ x<finish s h; omega)
    (fun x hx ↦ by change h.role≤x ∧ x<finish s h; omega)
  have b' : LogAccess rd wr rs.bases := LogAccess.mono br
    (fun x hx ↦ by change rowsHead s h≤x ∧ x<targetsHead s h at hx; change min h.oldArc splitHead≤x ∧ x<finish s h; omega)
    (fun x hx ↦ by change targetsHead s h≤x ∧ x<stopAddress s h at hx; change h.role≤x ∧ x<finish s h; omega)
  exact ⟨((((g'.append d').append a').append i').append b'),forward,dummy.twoFits,
    genuine.baseCount ▸ (bank s h w .genuineOwners 2).isLt,tables⟩

end CompressorRecords.ShrinkSlots.Build

end VPVNP
end Computability
end OAI
