import OAI.Computability.VPVNP.CompressorShrinkBlockInputs
import OAI.Computability.VPVNP.CompressorShrinkInputTerms
import OAI.Computability.VPVNP.CompressorShrinkGatherDispatch
import OAI.Computability.VPVNP.CompressorTermWorkerFootprint
import OAI.Computability.VPVNP.CompressorSourceWalk

/-!
# The two term-selection packets in the shrinking block calendar

The ordered packets correspond to the actual gather and selection visits
of the block planner. Each packet records the source program, complete
branch tapes, successor ordinals, and external read and write bounds.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkTermPackets

open BurstRAM BlockPlanner Compression ShrinkBlockInputs ShrinkInput PhaseRecipe SourceTransport
open scoped Classical Fin.CommRing

/-- The two native stages of term preparation, gathering AB/CD demand widths and selecting a
term for each motif. -/
inductive Stage where
  | gather | select
  deriving DecidableEq

/-- Run the demand gather before the term selector so the selector sees the completed dense
pairs. -/
def order : List Stage := [.gather,.select]

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps) (origin : Expr)

/-- The planned gather or selector visit at its position in the shrinking substep's term
window. -/
noncomputable def visit : Stage → Visit
  | .gather => (termVisits B i origin)[0]'(by rw [termVisits_length]; decide)
  | .select => (termVisits B i origin)[1]'(by rw [termVisits_length]; decide)

theorem order_visits : order.map (visit B i origin) = termVisits B i origin := rfl

variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g)) (T : IncidenceDirectory w) (start : ℕ)
variable (s : X.ShrinkSelection B.shrink)
local notation "N" => ShrinkTermInputs.motifCount X
local notation "H" => ShrinkTermSelection.bundles X
local notation "Q" => ShrinkTermSelection.ranks (a i)
local notation "src" => demandHead (w := w) X start
local notation "dst" => termHead (w := w) X start

/-- The public operands of the demand gather or motif selector, using the actual pair bank or
the dense demand and term-table heads. -/
noncomputable def bank : (j : Stage) → Fin (visit B i origin j).worker.params → Word w
  | .gather => pairBank X T start
  | .select => TermWorker.motifData B.shrink finTwoEquiv SelectedScore.supplyOrder.entries w
      (ShrinkTermSelection.addr src dst 10)

/-- An empty tape per gather row, or the encoded selected term's tape per dense motif for the
selector. -/
noncomputable def choices : Stage → List (List Bool)
  | .gather => List.replicate (H*Q) []
  | .select => List.ofFn (ShrinkTermSelection.tapes B.shrink X s w)

/-- Running the selected worker with its physical bank from cursor zero on the given tapes
yields the indicated reports. -/
noncomputable def source (cap : ℕ) (j : Stage) (mem : Memory w) (bs : List (List Bool)) (rs : List (Report w)) : Prop :=
  let P := ((visit B i origin j).worker.table.instantiate w (bank B i origin X T start j)).program
  runSegment P cap (some 0) mem bs = some rs

/-- The allowed external read region for gathering demands or reading the dense demands and
selected term records. -/
def readable : Stage → ℕ → Prop
  | .gather => ShrinkDemandGather.ReadRegion H (pairBank X T start)
  | .select => fun x => (src).val ≤ x ∧ x < (dst).val+N*10

/-- The gather's output pair region or the selector's ten-word term rows, according to the
phase. -/
def writable : Stage → ℕ → Prop
  | .gather => ShrinkDemandGather.WriteRegion H Q (pairBank X T start)
  | .select => fun x => (dst).val ≤ x ∧ x < (dst).val+N*10

/-- The per-motif probe bound for a term packet, four for gathering or the term-reader bound
for two demands and eight supplies. -/
noncomputable def probeRate : Stage → ℕ
  | .gather => 4
  | .select => TermRecordScan.probesPerRow B.shrink 2 8

/-- The physical gather or selection run with its tapes, cursor sequence, motif report count,
memory footprint and probe bound. -/
structure PacketRun (cap : ℕ) (j : Stage) (mem : Memory w) (rs : List (Report w)) : Prop where
  run : source B i origin X T start cap j mem (choices (w := w) B i X s j) rs
  reads : Reads (readable i X T start j) (eventLog rs)
  writes : Writes (writable i X T start j) (eventLog rs)
  cursors : rs.map Report.result = (List.range' 1 N).map (fun k : ℕ => some (k : Word w))
  branches : branchPaths rs = choices (w := w) B i X s j
  count : rs.length = N
  probes : countProbes (eventLog rs) ≤ N * probeRate B j

theorem gathered_packet (cap : ℕ) (hcap : ShrinkDemandGather.cost < cap) (room : termEnd X start 10 < 2^w)
    (mem : Memory w) (rs : List (Report w)) (hg : ShrinkDemandGather.Gathered H Q (pairBank X T start) cap mem rs) :
    PacketRun B i origin X T start s cap .gather mem rs := by
  have layout := (termLayout X T start 10 room).1
  let P := ShrinkDemandGather.program (pairBank X T start)
  let cursor (j : ℕ) : Word w := j
  have inc (j : ℕ) (_ : j < H*Q) (m : Memory w) (bits : List Bool) (r : Report w)
      (h : execute P cap (P.start (cursor j)) m bits = some r) : r.result = some (cursor (j+1)) := by
    have he := (execute_prefix_unique (suffix := bits) (ShrinkDemandGather.visit_run (pairBank X T start) (cursor j) m hcap) h).2
    rw [← he,ShrinkDemandGather.visits_result]; simp [cursor]
  have ord := OrdinalRun.successors P cap cursor (H*Q) inc 0 (List.replicate (H*Q) []) mem rs (by simp) hg.run
  obtain ⟨rd,wr⟩ := ShrinkDemandGather.footprints _ layout hcap mem rs hg.run
  exact ⟨hg.run,rd,wr,by simpa only [List.length_replicate,ShrinkTermSelection.motifCount_eq] using ord,
    ((runSegment_iff ..).mp hg.run).2.2,hg.count.trans (ShrinkTermSelection.motifCount_eq X).symm,
    by rw [hg.probes,ShrinkTermSelection.motifCount_eq]; change 4*(H*Q) ≤ (H*Q)*4; omega⟩

set_option maxHeartbeats 1200000 in
theorem selected_packet (cap : ℕ) (room : termEnd X start 10 < 2^w)
    (mem : Memory w) (rs : List (Report w))
    (h : ShrinkTermSelection.Written B.shrink X src dst 10 cap s mem rs) :
    PacketRun B i origin X T start s cap .select mem rs := by
  obtain ⟨_,_,sep,fit⟩ := termLayout X T start 10 room
  let L := ShrinkTermInputs.termRows X src dst 10 le_rfl sep fit
  let addr := ShrinkTermSelection.addr src dst 10
  let P := ShrinkTermSelection.termProgram B.shrink src dst 10
  let cursor (j : ℕ) : Word w := j
  let bits := List.ofFn (ShrinkTermSelection.tapes B.shrink X s w)
  have hw : TermWorker.Addresses L addr := TermWorker.addresses_strided (n := 8) _ _ _ _ le_rfl le_rfl sep fit
  have inc (j : ℕ) (hj : j<N) (m : Memory w) (bs : List Bool) (r : Report w)
      (hr : execute P cap (P.start (cursor j)) m bs = some r) : r.result = some (cursor (j+1)) := by
    let l : Fin N := ⟨j,hj⟩
    have hs := (hw l).1.symm ▸ L.sourceFits l
    have hd := (hw l).2.symm ▸ L.termFits l
    have hh := (TermWorker.Footprint.call B.shrink finTwoEquiv SelectedScore.supplyOrder.entries addr
      (cursor j) m cap bs r hs hd hr).1
    simpa only [cursor,Nat.cast_add,Nat.cast_one] using hh
  have len : bits.length = N := List.length_ofFn
  have ord := OrdinalRun.successors P cap cursor N inc 0 bits mem rs (by omega) h.run
  obtain ⟨rd,wr⟩ := TermWorker.Footprint.strided_segment B.shrink finTwoEquiv SelectedScore.supplyOrder.entries
    (src).val (dst).val 2 10 le_rfl le_rfl sep fit 0 cap mem bits rs (by omega) h.run
  exact ⟨h.run,rd,wr,by simpa only [len] using ord,h.branches,h.count,h.probes⟩

/-- The calendar's actual visits form one chronological two-packet
execution. The final snapshot retains the graph input, all six sorted
columns, and the selected descriptor of every motif. -/
theorem packets (cap : ℕ) (room : termEnd X start 10 < 2^w)
    (fit : ShrinkTermSelection.fitConstant B.shrink +4*Nat.clog 2 (X.maxWireWidth+1) ≤ w)
    (gatherCap : ShrinkDemandGather.cost < cap) (termCap : TermWorker.budget B.shrink 2 8 w X.maxWireWidth ≤ cap)
    (before : Memory w) (stored : ShrinkTermSelection.oldRows X (thickBank X T start) (cdBank X T start)
      (piecesBank X T start) before) :
    ∃ gs ts, let mid := after before (eventLog gs)
      let out := after mid (eventLog ts)
      let ps : List (SourceWalk.Packet Stage w) := [⟨.gather,before,gs⟩,⟨.select,mid,ts⟩]
      (ps.map (fun p => visit B i origin p.stage)) = termVisits B i origin ∧
      SourceWalk.Chronological (PacketRun B i origin X T start s cap) before ps ∧
      ShrinkTermSelection.Written B.shrink X src dst 10 cap s mid ts ∧
      ShrinkTermSelection.oldRows X (thickBank X T start) (cdBank X T start) (piecesBank X T start) out ∧
      ∀ x < ShrinkInput.stop X start, out x = before x := by
  obtain ⟨gs,hg,_,full⟩ := ShrinkInput.gather_select_from X T start B.shrink before stored 10 le_rfl room fit cap
    gatherCap termCap
  obtain ⟨ts,ht,cols,frame⟩ := full s
  exact ⟨gs,ts,rfl,⟨rfl,gathered_packet B i origin X T start s cap gatherCap room before gs hg,
    rfl,selected_packet B i origin X T start s cap room _ ts ht,trivial⟩,ht,cols,frame⟩

end CompressorRecords.ShrinkTermPackets

end VPVNP
end Computability
end OAI
