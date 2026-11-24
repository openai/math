import OAI.Computability.VPVNP.CompressorRecordsShrinkGreedy
import OAI.Computability.VPVNP.CompressorRecordsShrinkPlacement
import OAI.Computability.VPVNP.CompressorRecordsShrinkRankArena
import OAI.Computability.VPVNP.CompressorRecordsShrinkWidthArena

/-!
# Physical input to term selection at a shrinking level

Starting from the old incidence directory, run the two greedy assignments, a
preliminary layout, arc classification and ranking, width sorting, and both
prefix constructions. The preliminary layout places thin sites at their bundle
source. The thick-wire and CD assignments computed before term selection
depend only on the two thickness flags, the old slot, and the assigned bundle.

The report lists in the execution begin with the memory produced by their
predecessors. All counters needed by the list pass are explicitly cleared.
The original directory, the greedy colors and offsets, and the preliminary
placement records remain readable alongside the sorted AB and CD inputs.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkInput

open BurstRAM Compression PrimedStackRAM BundleKeys ShrinkRankSpace

variable {w a g : ℕ} (X : State a (packingLaneBits a g)) (T : IncidenceDirectory w) (start : ℕ)
local notation "N" => Fintype.card X.Base
local notation "S" => N*2^(packingLaneBits a g)
local notation "A" => S*2^a

/-- The start of the preliminary old-site placement columns, immediately after the greedy
workspace. -/
def placementBase := GreedyArena.greedyStop start N a
/-- The start of the bundle classification and ranking arena, immediately after the preliminary
placement columns. -/
def rankBase := ShrinkPlacement.stop X (placementBase X start)
/-- The layout of bucket, key, count, identifier, gathered-key, and rank storage for the old
ports. -/
abbrev plan := ShrinkRankArena.shape X (rankBase X start)
/-- The start of the sorted width and prefix tables following the bundle ranking arena. -/
def widthBase := (plan X start).stop
/-- The exclusive end of the deterministic shrinking-input arena, including width rectangles
and bundle totals. -/
def stop := widthBase X start+6*((plan X start).B*(plan X start).Q)+2*(plan X start).B

/-- The preliminary placement worker's operands, using the greedy color and offset columns and
the layout that assigns thin sites to their bundle source. -/
def placementBank := ShrinkPlacement.bank X T
  (ShrinkRAM.word w (GreedyArena.colorBase start))
  (ShrinkRAM.word w (GreedyArena.offsetBase start N a)) (placementBase X start) false

local notation "Z" => plan X start
local notation "sh" => placementBank X T start
local notation "classBank" => Shape.classifyBank (plan X start) T (placementBank X T start)
local notation "q" => Shape.collectBank (plan X start) w
local notation "dest" => ShrinkRAM.word w (Shape.ranks (plan X start))
local notation "wb" => widthBase X start

/-- Chronological execution of the deterministic, pre-selection part of a
shrinking level. Each component exposes its actual instruction tables. -/
structure Run (m : Memory w) where
  /-- The color and offset assignments supplying the preliminary placement pass. -/
  greedy : GreedyArena.Run X T start m
  /-- Reports of placing all old sites under the preliminary layout. -/
  sites : List (Report w)
  positions : runSegment ((template ShrinkRAM.visit 0).instantiate w sh).program 65 (some (ShrinkRAM.word w 0))
    greedy.post (List.replicate S []) = some sites
  siteWork : ShrinkRAM.ScanResult sh S 0 S greedy.post sites
  preliminary : ShrinkRAM.PlacementColumns X.slots X.baseIndex sh false (after greedy.post (eventLog sites))
  siteFrame : ∀ addr < placementBase X start, after greedy.post (eventLog sites) addr = greedy.post addr
  /-- Reports of clearing the thick-wire and CD row counts before appending any old ports. -/
  clear : List (Report w)
  /-- Reports of computing the bucket and sorting key for every old outgoing port. -/
  classify : List (Report w)
  /-- Reports of appending each old port identifier to its classified bundle row. -/
  append : List (Report w)
  /-- Reports of reading each row's identifiers to gather the corresponding old-port sorting
  keys. -/
  gather : List (Report w)
  /-- Reports of calculating each old port's rank in its classified row from the gathered keys. -/
  rank : List (Report w)
  ranking : ShrinkRankArena.Run X T sh (rankBase X start) (after greedy.post (eventLog sites))
    clear classify append gather rank
  /-- Reports of scattering old arc widths into their bundle rows at the computed ranks. -/
  scatter : List (Report w)
  /-- Reports of computing starts and totals of sorted thick-wire payloads in each bundle. -/
  thickPrefixes : List (Report w)
  /-- Reports of computing starts and totals of sorted CD motif payloads in each bundle. -/
  cdPrefixes : List (Report w)
  /-- Reports of splitting each thick payload total into AB piece widths and prefix offsets. -/
  abPieces : List (Report w)
  widths : ShrinkWidthArena.Run X T q dest wb
    (ShrinkRankArena.finalMemory (after greedy.post (eventLog sites)) clear classify append gather rank)
    scatter thickPrefixes cdPrefixes abPieces

theorem range_bounds :
    start ≤ placementBase X start ∧ placementBase X start ≤ rankBase X start ∧
      rankBase X start ≤ wb ∧ wb ≤ stop X start := by
  have hg := GreedyArena.bounds start N a
  change GreedyArena.colorBase start+N ≤ _ ∧ _ at hg
  have hpre : start ≤ placementBase X start := by
    change start ≤ GreedyArena.greedyStop start N a
    unfold GreedyArena.colorBase at hg
    omega
  have hrs : rankBase X start ≤ wb := by
    dsimp [widthBase,Shape.stop,Shape.ranks,Shape.gathered,Shape.ids,Shape.counts,plan,ShrinkRankArena.shape]
    omega
  exact ⟨hpre,Nat.le_add_right ..,hrs,by unfold stop; omega⟩

theorem pre_starts (room : stop X start < 2^w) (t : Fin 4) :
    (sh (t.natAdd 10)).val + S ≤ rankBase X start := by
  obtain ⟨_,_,hr,hw⟩ := range_bounds X start
  have fit := hr.trans_lt (hw.trans_lt room)
  rw [show (sh (t.natAdd 10)).val = placementBase X start+t.val*S from
    ShrinkPlacement.starts X T _ _ _ false fit t]
  change _ ≤ placementBase X start+4*S
  have hh := Nat.mul_le_mul_right S t.isLt
  rw [Nat.succ_mul] at hh; omega

namespace Run

variable {X T start} {m : Memory w} (r : Run X T start m)

/-- The memory after preliminary site placement and all bucket, append, key-gathering, and
ranking passes. -/
def rankPost := ShrinkRankArena.finalMemory (after r.greedy.post (eventLog r.sites))
  r.clear r.classify r.append r.gather r.rank

/-- The final shrinking-input memory containing the ranked widths, prefix tables, and split AB
piece data. -/
def post := ShrinkWidthArena.finalMemory r.rankPost r.scatter r.thickPrefixes r.cdPrefixes r.abPieces

theorem afterRank (addr : ℕ) (h : addr < widthBase X start) : r.post addr = r.rankPost addr :=
  r.widths.frame addr h

theorem afterSites (addr : ℕ) (h : addr < rankBase X start) :
    r.post addr = after r.greedy.post (eventLog r.sites) addr :=
  (r.afterRank addr (h.trans_le (range_bounds X start).2.2.1)).trans (r.ranking.below addr h)

theorem afterGreedy (addr : ℕ) (h : addr < placementBase X start) : r.post addr = r.greedy.post addr :=
  (r.afterSites addr (h.trans_le (range_bounds X start).2.1)).trans (r.siteFrame addr h)

theorem below (addr : ℕ) (h : addr < start) : r.post addr = m addr :=
  (r.afterGreedy addr (h.trans_le (range_bounds X start).1)).trans (r.greedy.below addr h)

theorem incidence : T.Represents X r.post := r.greedy.input.retain r.greedy.old r.below

theorem placement (room : stop X start < 2^w) :
    ShrinkRAM.PlacementColumns X.slots X.baseIndex sh false r.post :=
  r.preliminary.retain (pre_starts X T start room) r.afterSites

include r in
/-- The extents of the old color, offset, mate and shift columns in the
preliminary and selected-layout scans. -/
theorem inputBounds :
    (sh 6).val+N ≤ placementBase X start ∧ (sh 7).val+N ≤ placementBase X start ∧
    (sh 8).val+N*2^a ≤ placementBase X start ∧ (sh 9).val+N*2^a ≤ placementBase X start := by
  have hb := GreedyArena.bounds start N a
  have h₆ : (sh 6).val+N ≤ placementBase X start := by
    have hc : GreedyArena.colorBase start < 2^w := by have := r.greedy.room; omega
    change GreedyArena.colorBase start % (2^w)+N ≤ GreedyArena.greedyStop start N a
    rw [Nat.mod_eq_of_lt hc]; omega
  have h₇ : (sh 7).val+N ≤ placementBase X start := by
    have hc : GreedyArena.offsetBase start N a < 2^w := by have := r.greedy.room; omega
    change GreedyArena.offsetBase start N a % (2^w)+N ≤ GreedyArena.greedyStop start N a
    rw [Nat.mod_eq_of_lt hc]; omega
  have hs := Nat.mul_le_mul_right (2^a) (Nat.le_mul_of_pos_right N (Nat.two_pow_pos (packingLaneBits a g)))
  refine ⟨h₆,h₇,(Nat.add_le_add_left hs _).trans ((r.greedy.old 0).trans (range_bounds X start).1),
    (Nat.add_le_add_left hs _).trans ((r.greedy.old 2).trans (range_bounds X start).1)⟩

theorem incidence_after {out : Memory w} (frame : ∀ addr < stop X start, out addr = r.post addr) :
    T.Represents X out := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := range_bounds X start
  exact r.incidence.retain (fun c ↦ (r.greedy.old c).trans (h₁.trans (h₂.trans (h₃.trans h₄)))) frame

theorem placement_after {out : Memory w} (room : stop X start < 2^w)
    (frame : ∀ addr < stop X start, out addr = r.post addr) :
    ShrinkRAM.PlacementColumns X.slots X.baseIndex sh false out := by
  obtain ⟨_,_,h₃,h₄⟩ := range_bounds X start
  exact (r.placement room).retain (fun t ↦ (pre_starts X T start room t).trans (h₃.trans h₄)) frame

/-- Both assignments can be read in any later memory preserving the shrinking input. -/
theorem directory_before {out : Memory w} (frame : ∀ addr < placementBase X start, out addr = r.post addr) :
    Shrink.Directory X.slots X.baseIndex
      (ShrinkRAM.column sh out 6) (ShrinkRAM.column sh out 7)
      (ShrinkRAM.column sh out 8) (ShrinkRAM.column sh out 9) := by
  obtain ⟨h₆,h₇,h₈,h₉⟩ := r.inputBounds
  have after (z : ℕ) (h : z < placementBase X start) : out z = r.greedy.post z :=
    (frame z h).trans (r.afterGreedy z h)
  have keep (c : Fin 14) (j k : ℕ) (hc : (sh c).val+k ≤ placementBase X start) (hj : j<k) :
      ShrinkRAM.column sh out c j = ShrinkRAM.column sh r.greedy.post c j :=
    congrArg Fin.val (after _ ((Nat.mod_le ..).trans_lt ((Nat.add_lt_add_left
      ((Nat.mod_le ..).trans_lt hj) _).trans_le hc)))
  have dir : Shrink.Directory X.slots X.baseIndex (ShrinkRAM.column sh r.greedy.post 6)
      (ShrinkRAM.column sh r.greedy.post 7) (ShrinkRAM.column sh r.greedy.post 8) (ShrinkRAM.column sh r.greedy.post 9) :=
    r.greedy.directory
  constructor
  · intro v; exact (keep 6 _ _ h₆ (X.baseIndex v).isLt).trans (dir.color_at v)
  · intro v; exact (keep 7 _ _ h₇ (X.baseIndex v).isLt).trans (dir.offset_at v)
  · intro v i
    have h := CursorRAM.packed_lt (X.baseIndex v).isLt i.isLt
    exact (keep 8 _ _ h₈ h).trans (dir.mate_at v i)
  · intro v i
    have h := CursorRAM.packed_lt (X.baseIndex v).isLt i.isLt
    exact (keep 9 _ _ h₉ h).trans (dir.shift_at v i)

theorem directory_after {out : Memory w} (frame : ∀ addr < stop X start, out addr = r.post addr) :
    Shrink.Directory X.slots X.baseIndex
      (ShrinkRAM.column sh out 6) (ShrinkRAM.column sh out 7)
      (ShrinkRAM.column sh out 8) (ShrinkRAM.column sh out 9) := by
  obtain ⟨_,h₂,h₃,h₄⟩ := range_bounds X start
  exact r.directory_before fun addr h ↦ frame addr (h.trans_le (h₂.trans (h₃.trans h₄)))

theorem directory : Shrink.Directory X.slots X.baseIndex
    (ShrinkRAM.column sh r.post 6) (ShrinkRAM.column sh r.post 7)
    (ShrinkRAM.column sh r.post 8) (ShrinkRAM.column sh r.post 9) :=
  r.directory_after fun _ _ ↦ rfl

/-- Public parameters of the deterministic preliminary placement scan. -/
theorem bankParams (_r : Run X T start m) (room : stop X start < 2^w) :
    ShrinkRAM.Params sh a (Shrink.colors a) (Shrink.J a) g false := by
  have h := range_bounds X start
  exact ShrinkPlacement.params X T _ _ _ false (h.2.2.1.trans_lt (h.2.2.2.trans_lt room))

open scoped Classical in
/-- The actual sorted width and prefix arrays in the final memory. -/
theorem stored :
    DemandWidths.Stored X.packingData (Shrink.packedIndex X.baseIndex) X.packingWidth
      X.shrinkOrder X.shrinkNumber (ShrinkWidthArena.prefixBank X T q dest wb false)
        (ShrinkWidthArena.prefixBank X T q dest wb true) (ShrinkWidthArena.abBank X T q dest wb) r.post :=
  r.widths.stored

/-- Replay the reports of every native substep in their execution order. -/
def reports : List (Report w) :=
  r.greedy.reports ++ r.sites ++ r.clear ++ r.classify ++ r.append ++ r.gather ++ r.rank ++
    r.scatter ++ r.thickPrefixes ++ r.cdPrefixes ++ r.abPieces

private theorem after_append (mem : Memory w) (x y : List (Report w)) :
    after mem (eventLog (x++y)) = after (after mem (eventLog x)) (eventLog y) := by
  simp only [eventLog,List.flatMap_append,after,List.foldl_append]

theorem post_reports : after m (eventLog r.reports) = r.post := by
  simp only [reports,after_append,r.greedy.post_reports]
  rfl

/-- The exact deterministic pre-selection cost. All factors multiplying the
site, bundle and port counts depend only on the degree. -/
theorem reports_cost :
    let d := 2^a
    let t := Greedy.WalkLayout.tagCount d
    RAMBuckets.cost Report.probes r.reports =
      2+N*(16+7*d+8*d^2+5*t+8*t^2) + 9*S + 4*(Z).B + ((Z).Q+33)*A + 4*((Z).B*(Z).Q) := by
  intro d t
  have hg := r.greedy.reports_cost
  have hs := r.siteWork.cost
  have hz := r.ranking.clearCharge
  have hr := r.ranking.ranked.cost
  have hw := r.widths.cost
  change RAMBuckets.cost Report.probes r.greedy.reports = 2+N*(16+7*d+8*d^2+5*t+8*t^2) at hg
  change RAMBuckets.cost Report.probes r.sites = 9*S at hs
  change RAMBuckets.cost Report.probes r.classify + RAMBuckets.cost Report.probes r.append +
    RAMBuckets.cost Report.probes r.gather + RAMBuckets.cost Report.probes r.rank = ((Z).Q+23)*A at hr
  change RAMBuckets.cost Report.probes r.scatter + RAMBuckets.cost Report.probes r.thickPrefixes +
    RAMBuckets.cost Report.probes r.cdPrefixes + RAMBuckets.cost Report.probes r.abPieces =
    10*A+4*((Z).B*(Z).Q) at hw
  simp only [reports,RAMBuckets.cost_append]
  rw [Nat.add_mul] at hr ⊢
  change RAMBuckets.cost Report.probes r.clear = 4*(Z).B at hz
  omega

end Run

theorem build (m : Memory w) (old : T.Represents X m)
    (before : ∀ c : Fin 6, (T.column c).val+A ≤ start) (room : stop X start < 2^w)
    (widthFit : (Z).Q*X.maxWireWidth < 2^w) : Nonempty (Run X T start m) := by
  let n := N
  obtain ⟨hstart,hpre,hrank,hwidth⟩ := range_bounds X start
  have hg := GreedyArena.bounds start n a
  have hgreedy := hpre.trans_lt (hrank.trans_lt (hwidth.trans_lt room))
  obtain ⟨greedy⟩ := GreedyArena.build X T start m old before hgreedy
  let c := ShrinkRAM.word w (GreedyArena.colorBase start)
  let t := ShrinkRAM.word w (GreedyArena.offsetBase start n a)
  have hc : c.val+n ≤ placementBase X start := (Nat.add_le_add_right (Nat.mod_le ..) _).trans
    (by change GreedyArena.colorBase start+n ≤ GreedyArena.greedyStop start n a; omega)
  have ht : t.val+n ≤ placementBase X start := (Nat.add_le_add_right (Nat.mod_le ..) _).trans
    (by change GreedyArena.offsetBase start n a+n ≤ GreedyArena.greedyStop start n a; omega)
  have hdir : Shrink.Directory X.slots X.baseIndex (ShrinkRAM.column sh greedy.post 6)
      (ShrinkRAM.column sh greedy.post 7) (ShrinkRAM.column sh greedy.post 8) (ShrinkRAM.column sh greedy.post 9) :=
    greedy.directory
  have hbefore : ∀ j : Fin 6, (T.column j).val+A ≤ placementBase X start := fun j ↦ (before j).trans hstart
  obtain ⟨ss,shrun,swork,sdata,sframe⟩ := ShrinkPlacement.actual_run X T c t (placementBase X start)
    false greedy.post hdir (hrank.trans_lt (hwidth.trans_lt room)) hc ht hbefore
  let ms := after greedy.post (eventLog ss)
  have inc := greedy.incidence.retain hbefore sframe
  obtain ⟨z,cs,ls,gs,rs,ranking⟩ := ShrinkRankArena.build X T sh (rankBase X start) ms inc false
    sdata (fun j ↦ (hbefore j).trans hpre) (pre_starts X T start room) (hwidth.trans_lt room)
  let ranked := ShrinkRankArena.finalMemory ms z cs ls gs rs
  have v := (Z).values T sh Fintype.card_pos (hwidth.trans_lt room)
  have hstride : (Z).Q ≤ (q 4).val := v.stride.ge
  have hown : (q 1).val+A ≤ wb := by
    change (classBank 9).val+A ≤ wb
    rw [v.owner]
    change rankBase X start + A ≤ (Z).ranks+A
    apply Nat.add_le_add_right
    change rankBase X start ≤ ((rankBase X start+2*A+2*(Z).B)+(Z).rectangleSize)+(Z).rectangleSize
    omega
  have hd : (dest).val+A ≤ wb := by rw [v.ranks]; exact le_rfl
  have hwidthBefore : T.width.val+A ≤ wb := (before 5).trans (hstart.trans (hpre.trans hrank))
  have hroom : ShrinkWidthArena.stop X q wb < 2^w := by
    change wb+2*((Z).B*(q 4).val)+2*((Z).B*(q 4).val)+2*(Z).B+2*((Z).B*(Z).Q) < _
    rw [v.stride]
    change wb+6*((Z).B*(Z).Q)+2*(Z).B < _ at room
    omega
  have bounds := ShrinkWidthArena.scatterLayout X T q dest wb hstride hown hd hwidthBefore hroom
  have qpos : 0 < (Z).Q := by
    unfold Shape.Q cap PackingData.pieceCount
    have hc : 2 ≤ Shrink.colors a := by unfold Shrink.colors; have := Nat.two_pow_pos a; omega
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hc
    change 0 < 3*(2^(Shrink.colors a)*2^a)/4
    rw [hk,pow_add,show 2^2=4 by decide,Nat.mul_assoc 4]
    have := Nat.mul_pos (Nat.two_pow_pos k) (Nat.two_pow_pos a)
    omega
  have hfit (e : OldArc X.Base a g) : X.packingWidth e < 2^w :=
    ((X.width_le_maxWireWidth _).trans (Nat.le_mul_of_pos_left _ qpos)).trans_lt widthFit
  have hinput := BundleWidthScatter.ranked_input X T q dest (ShrinkRAM.word w wb) ranked bounds hfit
    ranking.motifs ranking.thick ranking.widths ranking.owners
  obtain ⟨ws,ts,us,ab,wr⟩ := ShrinkWidthArena.build X T q dest wb ranked hstride hown hd hwidthBefore hroom widthFit hinput
  exact ⟨⟨greedy,ss,shrun,swork,sdata,sframe,z,cs,ls,gs,rs,ranking,ws,ts,us,ab,wr⟩⟩

end CompressorRecords.ShrinkInput

end VPVNP
end Computability
end OAI
