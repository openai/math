import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOwnedOpen
import OAI.Computability.BorderVNP.FiniteEvaluatorPrepareReportsAllocation

/-! # The finite report seed on the actual opening image

The host writes inside the receiving-cell banks. The bundle writer and the
cell-control writer place their tables above the banks, and the latter stores
the owned count in frame word 90. This identifies the report setup words,
the receiving-team and bank columns, and the earlier canonical input widths.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open Packing FiniteEvaluator BorderVNP.Cube VPVNP.BurstRAM

variable (t : Layout) {team frame offsets control live ports bundles b w : ℕ}
variable (owner : Fin bundles → Fin t.cube.cells) (header : Fin bundles → BottomReports.BundleHeader)
local notation "H" => t.openInputs team frame offsets control live ports bundles b owner header

/-- Physical layout of the finite report preparation on the signed arena. -/
noncomputable def Layout.allocatedReports (frame control : ℕ) : Reports.Layout :=
  Reports.allocatedLayout t.before frame control t.p.report.gadgets t.p.report.countWidth

variable {m : ℕ → ℕ}
variable (place : OpenSuffix.Placement (t.openInputs team frame offsets control live ports bundles b owner header)
  t.cube t.before frame m)
include place

/-- The host's true destinations and both compact bundle tables leave every
word below the cell banks intact at the input of the control writer. -/
theorem Layout.open_bundle_low (a : ℕ) (low : a<t.cube.cellBank) :
    (H).bundleImage frame m a=m a := by
  have dest := CubeAllocation.host_dest t.cube frame m place.pointer place.bank place.ends
  have clear := OpenSuffix.afterDeck_of_allocation (H) t.before t.open_table_order.2.2
    place.ranges place.bundles place.four place.six
  apply ((H).bundles.image_outside _ _ _ _ (.inl (low.trans_le clear.ranges))
    (.inl (low.trans_le clear.bundles))).trans
  exact HostScatter.Layout.prefix_outside _ _ _ _ (fun i hi side own => .inl (low.trans_le (dest i hi side own).1))

/-- The complete opening additionally writes the populated count in frame word
90. Every other address below the cell banks still has its original word. -/
theorem Layout.open_image_low (a : ℕ) (low : a<t.cube.cellBank) (count : a≠frame+90) :
    (H).image frame m a=m a := by
  have clear := OpenSuffix.afterDeck_of_allocation (H) t.before t.open_table_order.2.2
    place.ranges place.bundles place.four place.six
  have four := low.trans_le clear.four
  have six := low.trans_le clear.six
  have ne : a≠(H).control.frame+90 := count
  have outside : ¬(H).control.outputs a :=
    fun h => h.elim (fun v => four.not_ge v.1) (fun v => v.elim (fun z => six.not_ge z.1) ne)
  rw [OpenSuffix.Inputs.image,CellControlRows.Layout.published,Function.update_of_ne ne,
    CellControlRows.image_outside _ _ le_rfl outside]
  exact t.open_bundle_low owner header place a low

variable (room : t.OpenRoom frame offsets control live ports bundles (2^b) w)
include room

/-- All seven setup words for the finite preparer come from the actual control
vector and the freshly published count of the preceding owned-cell scan. -/
theorem Layout.allocatedReport_seed (ready : OpenSuffix.Ready (H) frame m w)
    (controls : ∀ i : Fin 37, m (control+i.val)=t.controls i.val) (first : frame+112 ≤ control) :
    (t.allocatedReports frame control).Seed ((H).control.before ((H).bundleImage frame m) (H).control.cells)
      ((H).image frame m) := by
  have hctl := room.controlEnd.trans t.open_table_order.1
  have atControl (i : Fin 37) : (H).image frame m (control+i.val)=t.controls i.val :=
    (t.open_image_low owner header place _ (by have := i.isLt; omega) (by omega)).trans (controls i)
  have kept (a : ℕ) (low : a<t.cube.cellBank) (ne : a≠frame+90) :
      (H).image frame m a=(H).bundleImage frame m a :=
    (t.open_image_low owner header place a low ne).trans (t.open_bundle_low owner header place a low).symm
  have fw : (H).bundleImage frame m (frame+92)=control := ready.fields.frame.2.2.2.2.2.2.2
  refine ⟨(kept (frame+92) (by omega) (by omega)).trans fw,?_,atControl 17,atControl 27,atControl 22,atControl 14,atControl 7⟩
  exact Function.update_self _ _ _

/-- The signed arena's finite seed at the exact output of any native execution
of all four opening stages. -/
theorem Layout.report_seed_after_return {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {s z : Bank w} {input output : Memory w} {events : List (TeamRAM.Event w)}
    (base : (pub 0).val=frame) (initial : readings input=m)
    (ready : OpenSuffix.Ready (H) frame m w)
    (controls : ∀ i : Fin 37, m (control+i.val)=t.controls i.val) (first : frame+112 ≤ control)
    (run : Runs pub mac OpenSuffix.code s input events z output) :
    (t.allocatedReports frame control).Seed ((H).control.before ((H).bundleImage frame m) (H).control.cells)
      (readings output) := by
  have native : OpenSuffix.Ready (H) (pub 0).val (readings input) w := by rwa [base,initial]
  have image : readings output=(H).image (pub 0).val (readings input) := ((OpenSuffix.run (H) native).sound run).2
  rw [image,base,initial]
  exact t.allocatedReport_seed owner header place room ready controls first

/-- A genuine native directory entry supplies the owner and bank address of each
physical cell. The canonical width comes from the earlier routing geometry,
preserved through both native writers and the first three opening stages. -/
theorem Layout.open_report_sources {input original written : ℕ → ℕ} {R : ℕ}
    (axis : Fin (t.cube.n+1))
    (entry : Evaluator.NativeEntry t.cube frame control axis R input original written)
    (keep : CubeAllocation.HostRetention t.cube frame original written m)
    (widthEnd : offsets+2*t.cube.cables+t.cube.cells ≤ t.cube.header.header)
    (c : ℕ) (hc : c<t.cube.cells) :
    (H).bundleImage frame m (t.cube.hostDirectory+2*c)=(t.cube.receivingOwner frame axis R input c).val ∧
    (H).bundleImage frame m (t.cube.hostDirectory+2*c+1)=t.cube.cellBank+c*t.cube.cellStride ∧
    (H).bundleImage frame m (offsets+2*t.cube.cables+c)=original (offsets+2*t.cube.cables+c) := by
  have high := t.open_table_order.2.1
  have lower := room.offsetsLow
  have upper := room.offsetsEnd
  obtain ⟨_,labels,weights,owners,pair,host,_,_⟩ := t.cube.writer_order
  obtain ⟨_,_,dir⟩ := entry.image
  have own := (dir.hostRows c hc).1
  rw [Nat.mul_comm c 2] at own
  refine ⟨(t.open_bundle_low owner header place _ (by omega)).trans ((keep.tables _ (by omega) (by omega)).trans own),
    (t.open_bundle_low owner header place _ (by omega)).trans (place.bank c hc),?_⟩
  exact (t.open_bundle_low owner header place _ (by omega)).trans (keep.geometry lower _ (by omega) (by omega))

omit place room

/-- The physical routing allocator places the whole canonical-width column
before the signed control vector. This supplies the header bound for every
owned cell's canonical-width readback. -/
theorem Layout.OpenRoom.routing_width_end {t : Layout} {frame origin control live ports bundles width w : ℕ}
    (room : t.OpenRoom frame (RoutingOutputs.bases origin t.cube.cables t.cube.cells bundles).ends control
      live ports bundles width w)
    (address : control=RoutingOutputs.controlsBase origin t.cube.cables t.cube.cells bundles ports) :
    (RoutingOutputs.bases origin t.cube.cables t.cube.cells bundles).ends+2*t.cube.cables+t.cube.cells ≤
      t.cube.header.header := by
  have hi := room.controlEnd
  rw [address] at hi
  dsimp only [RoutingOutputs.bases,RoutingOutputs.controlsBase] at hi ⊢
  omega

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
