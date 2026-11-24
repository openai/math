import OAI.Computability.VPVNP.CompressorSlotCoreAccess
import OAI.Computability.VPVNP.CompressorSlotMateFootprint
import OAI.Computability.VPVNP.CompressorSlotWidthFootprint

/-! # Retained endpoint identifiers after all shrinking output scans

The native mate and width passes write beyond the rectangular row and inverse
field arrays. Both lookup directions remain available to the selector after
the completed incidence directory has been produced.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSlots.Build

open Compression Compression.State Compression.PackingData Compression.ShrinkMotif Compression.ShrinkEnergy
open MotifBlocks MotifGrid MotifConversion Slots SlotLevel ShrinkSlots BurstRAM

variable {a b g w : ℕ} {δ factor : ℝ} {k : Type*} [_root_.Field k]
variable (X : State a (packingLaneBits a g))
variable (B : FixedBlock k demandSource demandTarget supply (realWidths demandMass) (realWidths supplyMass) (31/16) factor)
variable (ready : Ready (2^a) (2*2^a+1) (2^b) δ) (sel : X.ShrinkSelection B)

private noncomputable local instance : DecidableEq X.Base := Classical.decEq _

set_option maxHeartbeats 1000000 in
theorem post_access (h : Heads) (splitHead : ℕ) (m : Memory w) (r : Construction w) :
    let s := levelShape (b := b) X
    let side := selectedLayout X B sel
    Space s h splitHead w → DemandRAM.RoleColumns X side h.oldArc m → r.Native s h splitHead side m →
      LogAccess (readRegion s h splitHead) (writeRegion s h) r.passes.slots.all ∧
      LogAccess (readRegion s h splitHead) (writeRegion s h) (r.passes.mates.all++r.passes.widths) ∧
      OrderedTables X ready side h (r.final m) := by
  intro s side sp roles native
  let Y := X.shrinkNext B ready sel
  obtain ⟨core,forward,twoFits,oldFits,tables⟩ := Build.core_access X B ready sel h splitHead m r sp roles native
  have counts := next_counts X B ready sel
  change Fintype.card Y.Base*2^b=baseArcs s ∧ Fintype.card Y.Base*2^g*2^b=actualCount s at counts
  let m₁ := r.passes.slots.final (r.prepare.final m)
  let m₂ := r.passes.mates.final m₁
  have mate := mate_footprint Y s h m₁ r.passes.mates forward counts.1 counts.2 rfl rfl
    sp.degree sp.lanes sp.fit native.2.2.1
  have h0 := sp.old
  have h1 := sp.roles
  have h2 := sp.next
  have h3 := sp.subdiv
  have h4 := sp.split
  have hs : h.scratch ≤ rowsHead s h := by unfold rowsHead; omega
  have hr : rowsHead s h ≤ targetsHead s h := by unfold targetsHead inverseHead; omega
  have ht : targetsHead s h ≤ inverseBaseHead s h := by unfold inverseBaseHead stopAddress shiftsHead; omega
  have hb : inverseBaseHead s h ≤ widthHead s h := by unfold widthHead inHead outHead; omega
  have hw : widthHead s h ≤ finish s h := Nat.le_add_right _ _
  have ws := SlotWidthScan.run_footprint s h splitHead m₂ r.passes.widths twoFits sp.degree sp.lanes sp.profile
    oldFits (h4.trans (by omega)) (by omega) sp.fit native.2.2.2
  let rd := readRegion s h splitHead
  let wr := writeRegion s h
  have lower := min_le_left h.oldArc splitHead
  have other := min_le_right h.oldArc splitHead
  have mate' : LogAccess rd wr r.passes.mates.all := LogAccess.mono mate
    (fun x hx ↦ by change min h.oldArc splitHead ≤ x ∧ x < finish s h; omega)
    (fun x hx ↦ by change h.role ≤ x ∧ x < finish s h; omega)
  have width' : LogAccess rd wr r.passes.widths := LogAccess.mono ws
    (fun x hx ↦ by change min h.oldArc splitHead ≤ x ∧ x < finish s h; omega)
    (fun x hx ↦ by change h.role ≤ x ∧ x < finish s h; omega)
  have keep (x : ℕ) (hx : x < targetsHead s h) : r.final m x = m₁ x := by
    have cm : m₂ = after m₁ (eventLog r.passes.mates.all) := by
      simp only [m₂,MateReports.final,MateReports.all,eventLog,List.flatMap_append,after,List.foldl_append]
    have hw := SourceTransport.after_outside m₂ ws.2 (show ¬ (widthHead s h ≤ x ∧ x < finish s h) by omega)
    have hm := SourceTransport.after_outside m₁ mate.2 (show ¬ (inverseBaseHead s h ≤ x ∧ x < widthHead s h) by omega)
    change after m₂ (eventLog r.passes.widths) x = m₁ x
    exact hw.trans (by rw [cm]; exact hm)
  have rect : rowsHead s h+owners s*s.newDegree ≤ inverseHead s h :=
    Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)) _
  have extent : inverseHead s h+fields s=targetsHead s h := rfl
  let tags := bitWordFinEquiv (packingTagBits (2^a))
  let lanes := bitWordFinEquiv g
  let D := SlotSchedule.slotDirectory X.packingData s.subdivisions X.baseIndex tags lanes side (pad := pad s)
  let hD := fun v ↦ (SlotSchedule.slotDirectory_degree X.packingData s.subdivisions X.baseIndex tags lanes
    (two_le_packingColors a) side v).trans (Nat.add_sub_of_le ready.degree_budget)
  refine ⟨core,mate'.append width',⟨?_,?_⟩⟩
  · intro e
    apply (keep _ ?_).trans (tables.bySlot e)
    change rowsHead s h+(SlotSchedule.sortedFields D (2^b) hD e).val < targetsHead s h
    have index : (SlotSchedule.sortedFields D (2^b) hD e).val < owners s*s.newDegree :=
      (SlotSchedule.sortedFields D (2^b) hD e).isLt
    omega
  · intro e
    apply (keep _ ?_).trans (tables.byField e)
    change inverseHead s h+(D.address e).val < targetsHead s h
    have hi : (D.address e).val < fields s := (D.address e).isLt
    omega

/-- The canonical sorted-field and inverse-field arrays after all sixteen construction phases. -/
theorem retained_tables (h : Heads) (splitHead : ℕ) (m : Memory w) (r : Construction w) :
    let s := levelShape (b := b) X
    let side := selectedLayout X B sel
    Space s h splitHead w → DemandRAM.RoleColumns X side h.oldArc m → r.Native s h splitHead side m →
      OrderedTables X ready side h (r.final m) := by
  intro s side sp roles native
  exact (post_access X B ready sel h splitHead m r sp roles native).2.2

end CompressorRecords.ShrinkSlots.Build

end VPVNP
end Computability
end OAI
