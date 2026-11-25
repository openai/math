import OAI.Computability.BorderVNP.DiagonalOwnedControlReportSetup
import OAI.Computability.BorderVNP.FiniteEvaluatorOwnedReportSeed
import OAI.Computability.BorderVNP.DiagonalTallySignedHeaderSeed
import OAI.Computability.BorderVNP.DiagonalTallyGadgetReadback

/-! # Seeding the genuine signed cell-report directory on the native control return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM Packing FiniteEvaluator BorderVNP.Cube DiagonalTallyAllocation DiagonalTallyCellReports
open ReportDirectory TeamContraction.JointHeader

variable (t : Layout) {w team frame offsets control live ports bundles b : ℕ}
variable (owner : Fin bundles → Fin t.cube.cells) (source : Fin bundles → ReportBundle)

local notation "r" => reportLayout t.before t.after frame control t.p.parameters t.p.siteWidth t.p.bodyCap t.cube.stop
local notation "d" => t.bundleLayout frame control bundles
local notation "rows" => t.controlRows team frame offsets control live ports

/-- The actual directory layout identifies all row and bundle pointers. The
physical cell count can be strictly smaller than its padded table capacity. -/
theorem Layout.signedReportBindings (room : t.OpenRoom frame offsets control live ports bundles (2^b) w) :
    Bindings t.before d rows r :=
  ⟨rfl,room.cells,room.bundles,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Recover the descriptor, true zero address and parameter dimension from the
parsed tally frame and the same installed lookup deck used by the signed suffix. -/
theorem Layout.signedReportWords {n b' h K s reserve axes groups cap width : ℕ} {pub : Arg → Word w}
    {mem : Memory w} {P : CubePacket.Inputs n b' h K s ℕ} {id : TableEntry n b' h K s → ℕ}
    {p : PositiveFields reserve axes groups cap t.cube.teams t.dim width} {raw : ℕ}
    (ptr : (pub 0).val=frame) (seed : HeaderSeed t p pub raw team mem)
    (deck : CubePacket.WordPrepared P id pub mem) (zeroAddr : P.frame.zeroAddr=t.cube.stop) :
    readings mem (frame+44)=t.after.descriptors ∧ readings mem (frame+81)=t.cube.stop ∧
      readings mem (frame+95)=t.p.parameters := by
  rw [←ptr]
  exact ⟨seed.seed.words.1,deck.frame.2.2.2.2.2.1.trans zeroAddr,seed.parameters⟩

variable {m : ℕ → ℕ}
variable (place : OpenSuffix.Placement (t.openInputs team frame offsets control live ports bundles b owner
    (fun j => (source j).header)) t.cube t.before frame m)
variable (room : t.OpenRoom frame offsets control live ports bundles (2^b) w)

include place in
/-- Genuine host cable writes target the receiver banks. The reference frame,
geometry counters, and low control table retain their original values. -/
theorem Layout.signedHostWord (x : ℕ) (low : x<t.cube.cellBank) : OpenSuffix.hostImage frame m x=m x := by
  have destination := CubeAllocation.host_dest t.cube frame m place.pointer place.bank place.ends
  exact HostScatter.Layout.prefix_outside _ _ _ _ (fun i hi side own => .inl (low.trans_le (destination i hi side own).1))

include room place in
/-- Read all thirteen report seed words and four scanner controls on the actual
post-host image. The value of count word 90 is then supplied by the real cell
control publisher. -/
theorem Layout.signedReportSeed (base : m (frame+92)=control)
    (inputs : m (frame+44)=t.after.descriptors ∧ m (frame+81)=t.cube.stop ∧ m (frame+95)=t.p.parameters)
    (ctl : ∀ i : Fin 37, m (control+i.val)=t.controls i.val) :
    let host := OpenSuffix.hostImage frame m
    (r).seed t.after.reportCursor (host (frame+90)) host ∧ (r).ScannerControls host := by
  intro host
  have bank := t.open_table_order.2.1
  have primary := room.primary
  have upper := room.controlEnd.trans t.open_table_order.1
  have field (i : ℕ) (hi : i<112) : host (frame+i)=m (frame+i) :=
    t.signedHostWord owner source place _ (by omega)
  have word (i : Fin 37) : host (control+i.val)=t.controls i.val :=
    (t.signedHostWord owner source place _ (by have := i.isLt; omega)).trans (ctl i)
  refine ⟨⟨(field 92 (by decide)).trans base,rfl,(field 95 (by decide)).trans inputs.2.2,
    (field 81 (by decide)).trans inputs.2.1,(field 44 (by decide)).trans inputs.1,
    word 17,word 19,word 22,word 23,word 24,word 25,word 26,word 27⟩,
    ⟨word 12,word 13,word 14,word 7⟩⟩

include room place in
/-- Allocate the report cells that the genuine sorted directory actually owns,
using the physical receiver extent and the true global one-copy source bounds. -/
theorem Layout.signedDirectoryAllocation (axis : Fin (t.cube.n+1))
    (counts : ℕ → Fin t.p.report.gadgets → Fin t.p.report.countWidth → Bool)
    (receive : ∀ c : Fin t.cube.cells, m (offsets+2*t.cube.cables+c.val)+
      (t.p.report.gadgets*t.p.report.countWidth+weightedCopies ((BundleDirectory.sourceRows owner c.val).map source))
        ≤ t.cube.cellStride)
    (supp : ∀ c : Fin t.cube.cells, supplementWords ((BundleDirectory.sourceRows owner c.val).map source) ≤ t.p.report.supplementStride)
    (marks : ∀ j,(source j).positions.length ≤ t.p.report.marked)
    (expanded : (∑ j,(source j).useCount) ≤ t.p.report.uses) :
    let host := OpenSuffix.hostImage frame m
    let cs := directoryCells d rows r owner source (grouped d owner source host) counts
    ReportAllocation t.before t.after (t.cube.cellWriter frame control axis) r cs t.after.reportCursor := by
  intro host cs
  have order := t.open_table_order
  have primary := room.primary
  have offsetTop := room.offsetsEnd
  have after : t.before.limit ≤ t.after.start := by
    change t.before.limit ≤ t.before.limit+3*t.cube.cells+7*t.cube.cells+
      t.p.scratchStride*t.cube.cells+t.p.burstStride*t.cube.cells
    omega
  have past : t.cube.stop ≤ t.before.start := by
    apply LE.le.trans _ t.constants_le_before
    unfold CubeConstants.arenaEnd CubeConstants.idBase; omega
  apply allocation_le t.before t.after (t.cube.cellWriter frame control axis) d rows frame control t.p.parameters
    t.p.siteWidth t.p.bodyCap t.cube.stop (t.signedReportBindings room) owner source host counts le_rfl room.cells rfl
    (by change frame+96 ≤ t.cube.cellBank; omega) past after (order.2.1.trans order.2.2)
    (offsetTop.trans order.2.2) _ _ supp room.bundles marks expanded
  · intro c
    change host (t.cube.hostDirectory+2*c.val+1)=t.cube.cellBank+c.val*t.cube.cellStride
    have hc : c.val < t.cube.cells := c.isLt
    have hd := order.2.1
    exact (t.signedHostWord owner source place _ (by omega)).trans (place.bank c.val hc)
  · intro c
    change OpenSuffix.hostImage frame m (offsets+2*t.cube.cables+c.val)+_ ≤ t.cube.cellStride
    have hc : c.val < t.cube.cells := c.isLt
    rw [t.signedHostWord owner source place (offsets+2*t.cube.cables+c.val) (by omega)]
    exact receive c

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
