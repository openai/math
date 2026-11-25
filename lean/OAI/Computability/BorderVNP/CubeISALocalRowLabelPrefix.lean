import OAI.Computability.BorderVNP.CubeDirectedIntervalNative

/-! # Memory below the public label and interval tables

The label chooser reads the sparse rows of the incoming frame. The interval
pass then uses the chosen labels and updates the two higher scratch arrays.
Their joint tick bound and untouched prefix apply without choosing a physical
enumeration of the sparse rows.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open BorderVNP.Cube VPVNP.BurstRAM

/-- Bounds on the input frame, compressed endpoints and allocated scratch for
the public label and directed-interval passes. -/
structure LabelPrefixFits (base w : ℕ) (before : ℕ → ℕ) : Prop where
  /-- All sparse endpoint names lie in the public cell range. -/
  endpoints : LabelIndex.Endpoints (LabelIndex.layout base before) before
  /-- The chooser tables occupy their required disjoint spans. -/
  allocated : LabelIndex.Allocated (LabelIndex.layout base before)
  /-- There is at least one possible label. -/
  positive : 0 < (LabelIndex.layout base before).labels
  /-- Compressed cables are below the chooser's output. -/
  cables : let t := LabelIndex.layout base before
    t.cables+t.cableCount*3 ≤ before (base+48)
  /-- All frame fields read by either pass precede the chooser's output. -/
  frame : base+58 < before (base+48)
  /-- The output label vector precedes the chooser's incidence heads. -/
  heads : let t := LabelIndex.layout base before
    before (base+48)+t.cells ≤ t.heads
  /-- The last chooser subtotal fits shared memory. -/
  means : let t := LabelIndex.layout base before
    t.dataMean+t.labels ≤ 2^w
  /-- All chooser arithmetic on the incoming row widths fits a word. -/
  envelope : let t := LabelIndex.layout base before
    LabelIndex.wordEnvelope t.labels (LabelIndex.inputWidth t before) < 2^w
  /-- The directed width table is above the chooser's output. -/
  widths : before (base+48)+(LabelIndex.layout base before).cells ≤ before (base+57)
  /-- Every ordered-pair width precedes the cable prefix array. -/
  ordinals : before (base+57)+(LabelIndex.layout base before).labels^2 ≤ before (base+58)
  /-- Every cable prefix fits shared memory. -/
  space : before (base+58)+(LabelIndex.layout base before).cableCount ≤ 2^w

/-- Combined tick bound on the original sparse frame. -/
def labelPrefixCost (base : ℕ) (before : ℕ → ℕ) : ℕ :=
  let t := LabelIndex.layout base before
  LabelIndex.directoryTicks t (t.labels-1) before +
    (NativeIntervals.setup.slots + (4*t.labels^2+2) + (2+t.cableCount*(NativeIntervals.cableStep.slots+1)))

/-- Run both public passes on the incoming frame. Every memory word below the
actual label pointer has its original reading in the returned state. -/
theorem labelPrefix_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (fit : LabelPrefixFits (pub 0).val w (readings m)) :
    BoundedRun pub mac (.seq LabelIndex.directoryProgram NativeIntervals.prepare) s m
      (labelPrefixCost (pub 0).val (readings m))
      (fun st => ∀ a < readings m ((pub 0).val+48), st.mem a = readings m a) := by
  let base := (pub 0).val
  let before := readings m
  let t := LabelIndex.layout base before
  let lab := before (base+48)
  let l := NativeIntervals.chooserLayout t base lab (before (base+57)) (before (base+58))
  have positive : 0 < t.labels := fit.positive
  have frame : base+58 < lab := fit.frame
  have heads : lab+t.cells ≤ t.heads := fit.heads
  have hz : t.labels = (t.labels-1)+1 := by omega
  obtain ⟨tr,u,mid,run,clock,_,codes,off⟩ := LabelIndex.native_table_codes pub mac (t.labels-1) s m
    fit.endpoints fit.allocated hz heads (show base+56 < t.heads by omega) fit.means fit.envelope
  have keep (a : ℕ) (ha : a < lab) : readings mid a = before a := congrArg Fin.val (off a ha)
  have bound (i : Fin t.cells) : readings mid (lab+i.val) < t.labels := by
    change (mid (lab+i.val)).val < t.labels
    rw [codes i]
    exact (Physical.tableCodes t before fit.endpoints (t.labels-1) i).isLt.trans_le (by omega)
  have room := NativeIntervals.chooser_interval_fits t before (readings mid) base lab l.widths l.ordinals w
    fit.endpoints keep bound positive fit.cables frame fit.widths fit.ordinals fit.space fit.envelope
  have field (j : ℕ) (hj : j ≤ 58) := keep (base+j) (by omega)
  have fields : l.Fields (readings mid) :=
    ⟨field 6 (by decide),field 7 (by decide),field 48 (by decide),field 56 (by decide),
      field 57 (by decide),field 58 le_rfl⟩
  obtain ⟨fs,v,last,run',clock',_,img⟩ := NativeIntervals.run_prepare pub mac l u mid room rfl fields
  have finalImage : l.Image (readings mid) l.count (readings last) := img
  refine ⟨_,v,last,run.seq run',(VPVNP.RAMBuckets.cost_append ..).trans_le (Nat.add_le_add clock clock'),?_⟩
  intro a ha
  have h : a < lab := ha
  have widths : lab+t.cells ≤ l.widths := fit.widths
  have ordinals : l.widths+t.labels^2 ≤ l.ordinals := fit.ordinals
  exact (finalImage.outside a (by omega) (by omega)).trans (keep a h)

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
