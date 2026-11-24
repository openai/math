import OAI.Computability.VPVNP.CompressorRecordRefreshDirectory
import OAI.Computability.VPVNP.CompressorRecordRefreshNewSlots

/-!
# Native external descriptor construction from an old compressor state

The old outgoing slots index the width column directly. The old base table supplies a target
and a binary lane displacement per arc. Three scans with shared external memory gather the
actual widths, translate the base table into a bundle directory and write the two endpoint
segment tables. The resulting totals and segment rows refer to the same old state and the
same kernel intervals. The resource count includes all three scans.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh

open Compression Compression.Refresh Compression.DegreeRefresh BurstRAM PrimedStackRAM RefreshRAM

variable {a g n bits : ℕ} (X : State a (a+g)) (base : X.Base × Fin (2^a) ≃ Fin n)

/-- The gather and directory tables use the array bases of the ensuing external pass. -/
def gatherWords (p : Fin 8 → BurstRAM.Word bits) (lanes oldWidth : BurstRAM.Word bits) : Fin 4 → BurstRAM.Word bits :=
  ![p 0, lanes, oldWidth, p 1]

/-- Assemble the bundle-directory operands from the residual lane count, old base columns, and
three scratch destinations. -/
def directoryWords (p : Fin 8 → BurstRAM.Word bits) (lanes target shift : BurstRAM.Word bits) :
    Fin 8 → BurstRAM.Word bits := ![lanes,target,p 2,p 3,p 4,shift,0,0]

variable (p : Fin 8 → BurstRAM.Word bits) (lanes oldWidth target shift : BurstRAM.Word bits)

/-- The old base columns also remain live through the gather's width writes. -/
def baseOutsideGather : Prop :=
  ∀ e (j : BurstRAM.Word bits), j.val < n * 2^g * 2^a →
    (target + Fin.ofNat (2^bits) (base e).val).val ≠ (p 1 + j).val ∧
    (shift + Fin.ofNat (2^bits) (base e).val).val ≠ (p 1 + j).val

private theorem gather_cost {rs : List (Report bits)} (h : ∀ r ∈ rs, countProbes r.events = 2) :
    RAMBuckets.cost Report.probes rs = 3 * rs.length := by
  induction rs with
  | nil => simp [RAMBuckets.cost]
  | cons r rs ih =>
    rw [RAMBuckets.cost, Report.probes, h r (List.mem_cons_self ..), ih (fun q hq => h q (List.mem_cons_of_mem _ hq)),
      List.length_cons, Nat.mul_succ]
    omega

/-- A physical address outside all seven arrays at this level. -/
def outsideLevel (p : Fin 8 → BurstRAM.Word bits) (S addr : ℕ) : Prop :=
  ∀ t : Fin 8, t ≠ 0 → ∀ i : BurstRAM.Word bits, i.val < S → addr ≠ (p t + i).val

include base in
/-- The source-bundle count is the physical position count of the input state. -/
theorem bundleCount_positions : n * 2^g = X.positions := by
  have hbase := Fintype.card_congr base
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at hbase
  rw [State.positions, Fintype.card_prod, Fintype.card_congr (bitWordFinEquiv (a+g)), Fintype.card_fin, ← hbase, pow_add]
  exact Nat.mul_assoc ..

/-- Native reports, memory and geometric rows produced by the three external passes. -/
def ExternalReports (m : Memory bits) (fit : n * 2^g * 2^a ≤ 2^bits)
    (rg rd re : List (Report bits)) : Prop :=
    let B := n * 2^g
    let S := B * 2^a
    let ord := bundleOrder g base
    let gM := (template RefreshGather.gather 0).instantiate bits (gatherWords p lanes oldWidth)
    let dM := (template BundleDirectory.visit 0).instantiate bits (directoryWords p lanes target shift)
    let eM := (template RefreshRAM.visit 0).instantiate bits p
    let m₁ := after m (eventLog rg)
    let m₂ := after m₁ (eventLog rd)
    let m₃ := after m₂ (eventLog re)
    runSegment gM.program 24 (some 0) m (List.replicate S []) = some rg ∧
    runSegment dM.program 28 (some 0) m₁ (List.replicate B []) = some rd ∧
    runSegment eM.program 33 (some 0) m₂ (List.replicate S []) = some re ∧
    RAMBuckets.cost Report.probes (rg ++ rd ++ re) = 6 * B + 12 * S ∧
    AtCursor p S (graphInput (splitSlots X) ord (splitWidths X)) m₃ S ∧
    (∀ addr, outsideLevel p S addr → m₃ addr = m addr) ∧
    (∀ b, (cell p m₃ 4 (bundleWord ord fit b)).val =
      ∑ j, bundleWidths (bitWordFinEquiv a) (splitWidths X) b j) ∧
    ∀ e : DyadicArc X.Base (BitWord g) a,
      let i := idWord ord fit e
      let j := idWord ord fit (oldPortMatching (splitSlots X) (bitWordFinEquiv a) e)
      let r := outgoingRecord (splitSlots X) (bitWordFinEquiv a) (splitWidths X) e
      (cell p m₃ 5 i).val = r.offset ∧ (cell p m₃ 6 j).val = r.offset ∧ (cell p m₃ 7 j).val = r.width

/-- Existence of a complete deterministic external construction. -/
def ExternalExecution (m : Memory bits) (fit : n * 2^g * 2^a ≤ 2^bits) : Prop :=
  ∃ rg rd re, ExternalReports X base p lanes oldWidth target shift m fit rg rd re

/-- Execute the three native phase tables in succession from the old physical slot records.
For `B` bundles and `S` segments the exact cost is `6B + 12S` calls plus external probes. -/
theorem external_phases_stages (degree : (p 0).val = 2^a) (residual : lanes.val = 2^g)
    (regions : Regions p (n*2^g*2^a))
    (dirLayout : BundleDirectory.Layout (directoryWords p lanes target shift) n (2^g))
    (m : Memory bits)
    (widths : RefreshGather.HasOldWidths X base (gatherWords p lanes oldWidth) m)
    (baseTable : BundleDirectory.BaseTables (splitSlots X) base (directoryWords p lanes target shift) m)
    (wireApart : RefreshGather.SourcesDisjoint (gatherWords p lanes oldWidth) (n*2^g*2^a))
    (baseApart : baseOutsideGather (g := g) X base p target shift)
    (room : ∀ b, (∑ j, bundleWidths (bitWordFinEquiv a) (splitWidths X) b j) < 2^bits) :
    ∃ rg rd re, ExternalReports X base p lanes oldWidth target shift m regions.fits rg rd re ∧
      BundleDirectory.BaseTables (splitSlots X) base (directoryWords p lanes target shift) (after m (eventLog rg)) ∧
      AtCursor p (n*2^g*2^a) (graphInput (splitSlots X) (bundleOrder g base) (splitWidths X))
        (after (after m (eventLog rg)) (eventLog rd)) 0 := by
  let B := n * 2^g
  let S := B * 2^a
  let q := gatherWords p lanes oldWidth
  let d := directoryWords p lanes target shift
  let ord := bundleOrder g base
  let data : Input bits := graphInput (splitSlots X) ord (splitWidths X)
  have T : Directory (splitSlots X) ord (splitWidths X) p data regions.fits :=
    graphInput_directory (splitSlots X) ord (splitWidths X) p degree room
  have start : RefreshGather.Gathered q m m 0 :=
    ⟨fun _ hi => (Nat.not_lt_zero _ hi).elim, fun _ _ => rfl⟩
  obtain ⟨rg,hg,done,ng,wg⟩ := RefreshGather.gather_run regions.fits wireApart start S (by simp [S,B])
  let m₁ := after m (eventLog rg)
  have old : BundleDirectory.BaseTables (splitSlots X) base d m₁ := by
    refine ⟨baseTable.lanes, fun e => ?_, fun e => ?_⟩
    · have h := done.frame (target + Fin.ofNat (2^bits) (base e).val).val
        (fun j hj => (baseApart e j (by simpa only [Nat.zero_add] using hj)).1)
      exact (congrArg Fin.val h).trans (baseTable.target e)
    · have h := done.frame (shift + Fin.ofNat (2^bits) (base e).val).val
        (fun j hj => (baseApart e j (by simpa only [Nat.zero_add] using hj)).2)
      exact (congrArg Fin.val h).trans (baseTable.displacement e)
  obtain ⟨rd,hd,ready,frame,cd,_,_⟩ := BundleDirectory.directory_pass (splitSlots X) base d dirLayout m₁ old
  let m₂ := after m₁ (eventLog rd)
  have init := BundleDirectory.Prefix.external_start (splitSlots X) base d p m₂ (splitWidths X) ready degree rfl rfl rfl (by
    intro i hi
    let e := (numbered ord).symm ⟨i.val,hi⟩
    have he : idWord ord regions.fits e = i := by
      apply Fin.ext
      change (numbered ord e).val = i.val
      simp [e]
    have hframe := frame (p 1+i).val (by
      intro j hj
      have hs : j.val < S := hj.trans_le (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos a))
      exact ⟨fun h => (by decide : (1 : Fin 8) ≠ 2) ((regions.apart 1 2 (by decide) (by decide) i j hi hs).mp h).1,
        fun h => (by decide : (1 : Fin 8) ≠ 3) ((regions.apart 1 3 (by decide) (by decide) i j hi hs).mp h).1,
        fun h => (by decide : (1 : Fin 8) ≠ 4) ((regions.apart 1 4 (by decide) (by decide) i j hi hs).mp h).1⟩)
    change after m₁ (eventLog rd) (p 1+i).val = data.width i
    rw [hframe]
    have copy := done.rows i (by simpa only [Nat.zero_add] using hi)
    change m₁ (p 1+i).val = _ at copy
    rw [copy, ← he]
    apply Fin.ext
    exact (RefreshGather.read_state_width X base ord (bundleOrder_val g base) q m widths degree residual regions.fits e).trans
      (T.old e).symm)
  obtain ⟨re,he,ce,atEnd,frameEnd,total,rows⟩ := external_pass (splitSlots X) ord (splitWidths X) p data T regions room m₂ init
  have finalFrame (addr : ℕ) (outside : outsideLevel p S addr) :
      after m₂ (eventLog re) addr = m addr := by
    have he' := frameEnd addr (fun t ht => outside t (by rintro rfl; simp at ht))
    have hd' := frame addr (fun i hi =>
      let hs := hi.trans_le (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos a))
      ⟨outside 2 (by decide) i hs, outside 3 (by decide) i hs, outside 4 (by decide) i hs⟩)
    have hg' := done.frame addr (fun i hi => outside 1 (by decide) i (by simpa only [Nat.zero_add] using hi))
    exact he'.trans (hd'.trans hg')
  refine ⟨rg,rd,re,⟨hg,hd,he,?_,atEnd,finalFrame,total,rows⟩,old,init⟩
  have cg := gather_cost (fun r h => (wg r h).2)
  rw [ng] at cg
  change RAMBuckets.cost Report.probes re = 9 * S at ce
  change RAMBuckets.cost Report.probes rd = 6 * B at cd
  simp only [RAMBuckets.cost_append, cg, cd, ce, S, B]
  ring

/-- A complete execution of the three native refresh prepasses. -/
theorem external_phases (degree : (p 0).val = 2^a) (residual : lanes.val = 2^g)
    (regions : Regions p (n*2^g*2^a))
    (dirLayout : BundleDirectory.Layout (directoryWords p lanes target shift) n (2^g))
    (m : Memory bits)
    (widths : RefreshGather.HasOldWidths X base (gatherWords p lanes oldWidth) m)
    (baseTable : BundleDirectory.BaseTables (splitSlots X) base (directoryWords p lanes target shift) m)
    (wireApart : RefreshGather.SourcesDisjoint (gatherWords p lanes oldWidth) (n*2^g*2^a))
    (baseApart : baseOutsideGather (g := g) X base p target shift)
    (room : ∀ b, (∑ j, bundleWidths (bitWordFinEquiv a) (splitWidths X) b j) < 2^bits) :
    ExternalExecution X base p lanes oldWidth target shift m regions.fits := by
  obtain ⟨rg,rd,re,h,_,_⟩ := external_phases_stages X base p lanes oldWidth target shift degree residual
    regions dirLayout m widths baseTable wireApart baseApart room
  exact ⟨rg,rd,re,h⟩

end CompressorRecords.PortRefresh

end VPVNP
end Computability
end OAI
