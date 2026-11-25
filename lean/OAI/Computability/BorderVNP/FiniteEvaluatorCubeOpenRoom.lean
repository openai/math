import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenLayouts
import OAI.Computability.BorderVNP.RoutingISACubeArenaPreserveGroups
import OAI.Computability.BorderVNP.RoutingISASignedReaderArena

/-! # Word bounds for the signed bundle and cell-control writers

The cable offset and live-port arrays occupy the geometry region. The host
directory precedes the receiving-cell banks. After the immutable cube deck and
fragment workspace, the report allocation reserves the two compact header
tables followed by the bundle ranges and payloads. This order also proves the
non-aliasing premises for the native writers.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open Packing DiagonalTallyAllocation

variable {t : Layout} {frame offsets control live ports bundles width w : ℕ}

/-- Address placements and size ceilings for one reached public geometry. -/
structure Layout.OpenRoom (t : Layout) (frame offsets control live ports bundles width w : ℕ) : Prop where
  primary : frame+112 ≤ t.cube.hostDirectory
  offsetsLow : frame+112 ≤ offsets
  offsetsEnd : offsets+2*t.cube.cables+t.cube.cells ≤ t.cube.cellBank
  liveLow : frame+112 ≤ live
  liveEnd : live+2*ports+t.cube.cells ≤ t.cube.cellBank
  controlEnd : control+37 ≤ t.cube.header.header
  payloadEnd : t.p.bundlePayload+width ≤ t.cube.header.header
  rankEnd : t.p.bundleInverse+width ≤ t.cube.header.header
  markers : t.cube.cells+6*bundles+t.cube.cells ≤ width
  cells : t.cube.cells ≤ t.p.report.cells
  bundles : bundles ≤ t.p.report.bundles
  top : t.before.limit < 2^w

/-- The secondary header and full native host directory precede the receiving
banks, which in turn precede the signed report controls. -/
theorem Layout.open_table_order (t : Layout) :
    t.cube.header.header ≤ t.cube.cellBank ∧ t.cube.hostDirectory+2*t.cube.cells ≤ t.cube.cellBank ∧
    t.cube.cellBank ≤ t.before.start := by
  have pairBank : t.cube.pairBase ≤ t.cube.cellBank := Nat.le_add_right ..
  have header := t.cube.group_order.1.trans t.cube.separated.2.2.2.1
  have records : t.cube.records ≤ t.cube.pairBase := by
    dsimp only [CubeArena.Layout.pairBase,TableLayout.reserveEnd]
    omega
  have deck : t.cube.stop ≤ CubeConstants.arenaEnd t.cube.stop t.id := by
    unfold CubeConstants.arenaEnd CubeConstants.idBase
    omega
  exact ⟨header.trans pairBank,records.trans pairBank,
    t.cube.separated.2.2.2.2.2.trans (deck.trans t.constants_le_before)⟩

private theorem before_order (a : BeforeTasks) :
    a.start ≤ a.supplement ∧ a.supplement+a.bound.supplementStride*a.bound.cells=a.counters ∧
    a.counters+2*a.bound.cells=a.merged ∧ a.merged+a.bound.cells=a.four ∧
    a.four+4*a.bound.cells=a.six ∧ a.six+6*a.bound.cells=a.ranges ∧
    a.ranges+2*a.bound.cells=a.bundleTable ∧ a.bundleTable+6*a.bound.bundles=a.limit := by
  refine ⟨Nat.le_add_right ..,?_,rfl,rfl,rfl,rfl,rfl,rfl⟩
  rw [BeforeTasks.counters,Nat.mul_comm a.bound.cells a.bound.supplementStride]

section

variable (room : t.OpenRoom frame offsets control live ports bundles width w)
include room

/-- The two input sort banks lie below both compacted output arrays, whose
full length-only capacity fits in the machine address width. -/
theorem Layout.OpenRoom.bundle_fit : (t.bundleLayout frame control bundles).Fits w width := by
  obtain ⟨hdr,bank,start⟩ := t.open_table_order
  obtain ⟨sp,ct,mg,four,six,ranges,rows,last⟩ := before_order t.before
  have cell : t.cube.cells ≤ t.before.bound.cells := room.cells
  have bundle : bundles ≤ t.before.bound.bundles := room.bundles
  have primary := room.primary
  have controlEnd := room.controlEnd
  have payloadEnd := room.payloadEnd
  have rankEnd := room.rankEnd
  have top := room.top
  constructor
  · change frame+92 < 2^w; omega
  · change control+21 < 2^w; omega
  · exact room.markers
  · change t.p.bundlePayload+width < 2^w; omega
  · change t.p.bundleInverse+width < 2^w; omega
  · change t.before.ranges+2*t.cube.cells < 2^w; omega
  · change t.before.bundleTable+6*bundles < 2^w; omega
  · exact Or.inl (show t.before.ranges+2*t.cube.cells ≤ t.before.bundleTable by omega)
  · exact Or.inr (show t.p.bundleInverse+width ≤ t.before.ranges by omega)
  · exact Or.inr (show t.p.bundlePayload+width ≤ t.before.ranges by omega)
  · exact Or.inr (show t.p.bundleInverse+width ≤ t.before.bundleTable by omega)
  · exact Or.inr (show t.p.bundlePayload+width ≤ t.before.bundleTable by omega)

/-- The true signed cell-control layout is safe for every reached ownership
choice. Even its two per-cell bundle ordinal reads lie outside both tables
being written and outside the published frame count. -/
theorem Layout.OpenRoom.controls_fit (team : ℕ) : (t.controlRows team frame offsets control live ports).Room w := by
  obtain ⟨hdr,bank,start⟩ := t.open_table_order
  obtain ⟨sp,ct,mg,four,six,ranges,rows,last⟩ := before_order t.before
  have primary := room.primary
  have offsetsLow := room.offsetsLow
  have offsetsEnd := room.offsetsEnd
  have liveLow := room.liveLow
  have liveEnd := room.liveEnd
  have controlEnd := room.controlEnd
  have top := room.top
  have cell : t.cube.cells ≤ t.before.bound.cells := room.cells
  have supplement := Nat.mul_le_mul_left t.before.bound.supplementStride cell
  constructor
  · change frame+112 < 2^w ∧ control+19 < 2^w; omega
  · change t.cube.hostDirectory+2*t.cube.cells < 2^w ∧
      offsets+2*t.cube.cables+t.cube.cells < 2^w ∧ live+2*ports+t.cube.cells < 2^w ∧ t.before.ranges+2*t.cube.cells < 2^w
    omega
  · change t.before.four+4*t.cube.cells < 2^w ∧ t.before.six+6*t.cube.cells < 2^w; omega
  · change t.before.supplement+t.before.bound.supplementStride*t.cube.cells < 2^w ∧
      t.before.counters+2*t.cube.cells < 2^w ∧ t.before.merged+t.cube.cells < 2^w
    omega
  · intro c hc a ha hout
    change c < t.cube.cells at hc
    change a=t.cube.hostDirectory+2*c ∨ a=t.cube.hostDirectory+2*c+1 ∨
      a=offsets+2*t.cube.cables+c ∨ a=live+2*ports+c ∨ a=t.before.ranges+2*c ∨ a=t.before.ranges+2*c+1 at ha
    change (t.before.four ≤ a ∧ a < t.before.four+4*t.cube.cells) ∨
      (t.before.six ≤ a ∧ a < t.before.six+6*t.cube.cells) ∨ a=frame+90 at hout
    omega
  · change (t.before.four+4*t.cube.cells ≤ t.before.six ∨ t.before.six+6*t.cube.cells ≤ t.before.four) ∧
      frame+112 ≤ t.before.four ∧ frame+112 ≤ t.before.six
    omega

end

/-- The end of the signed reader covers all pre-task report reservations,
including the two compact tables and the bundle ranges and output. -/
theorem Layout.before_limit_le_endAddress (t : Layout) (w u v k : ℕ) : t.before.limit ≤ t.endAddress w u v k := by
  have tasks : t.before.limit ≤ t.after.start := by
    dsimp only [Layout.after,TypedTaskBuilder.Layout.windowsEnd]
    omega
  have tally : t.after.start ≤ t.after.localBase := by
    rw [AfterTasks.localBase,t.after.footprint]
    omega
  apply (tasks.trans tally).trans
  dsimp only [Layout.endAddress,Layout.entry,DiagonalResidueRAM.gateBase,Layout.valuation,Layout.tallyBits]
  omega

/-- Specialize the room proof to actual geometry output addresses. The sort
banks are a pair of adjacent blocks at the chosen output column. The geometry
allocator places every used output column before the secondary cube header. -/
theorem Layout.openRoom_of_geometry (t : Layout) {frame fresh profile gates outputs bits J ports bundles width w sortColumn u v k : ℕ}
    (low : frame+112 ≤ fresh)
    (routing : t.cube.cables*3+(RoutingOutputs.count t.cube.cables t.cube.cells J ports+
      ((t.cube.cells+(J+t.cube.cells))+37)) ≤ outputs)
    (sort : sortColumn+2*width ≤ outputs)
    (cube : t.cube.header.header = GeometryAdvice.Allocation.stop fresh profile gates outputs bits w)
    (payload : t.p.bundlePayload = GeometryAdvice.Allocation.dest fresh profile gates outputs bits+sortColumn)
    (rank : t.p.bundleInverse = t.p.bundlePayload+width)
    (markers : t.cube.cells+6*bundles+t.cube.cells ≤ width)
    (cells : t.cube.cells ≤ t.p.report.cells) (count : bundles ≤ t.p.report.bundles)
    (word : t.endAddress w u v k < 2^w) :
    let origin := GeometryAdvice.Allocation.dest fresh profile gates outputs bits
    let tables := RoutingOutputs.bases origin t.cube.cables t.cube.cells J
    t.OpenRoom frame tables.ends (RoutingOutputs.controlsBase origin t.cube.cables t.cube.cells J ports)
      tables.livePairs ports bundles width w := by
  intro origin tables
  have afterFrame : frame+112 ≤ origin := by
    dsimp only [origin,GeometryAdvice.Allocation.dest,GeometryAdvice.Allocation.temp]; omega
  have endCols : origin+outputs ≤ t.cube.header.header := by
    rw [cube]
    dsimp only [GeometryAdvice.Allocation.stop,GeometryAdvice.Allocation.packed,GeometryAdvice.Allocation.dense,origin]; omega
  have hdrBank := t.open_table_order.1
  obtain ⟨hdr,_,_,_,_,_,power,powers,group,team,owner,pair,_⟩ := t.cube.group_order
  have ctl : RoutingOutputs.controlsBase origin t.cube.cables t.cube.cells J ports+37 ≤ origin+outputs := by
    dsimp only [RoutingOutputs.controlsBase,RoutingOutputs.bases,RoutingOutputs.count] at routing ⊢
    omega
  constructor
  · omega
  · dsimp only [tables,RoutingOutputs.bases]; omega
  · dsimp only [tables,RoutingOutputs.controlsBase,RoutingOutputs.bases] at ctl ⊢; omega
  · dsimp only [tables,RoutingOutputs.bases]; omega
  · dsimp only [tables,RoutingOutputs.controlsBase,RoutingOutputs.bases] at ctl ⊢; omega
  · exact ctl.trans endCols
  · change t.p.bundlePayload=origin+sortColumn at payload; omega
  · change t.p.bundlePayload=origin+sortColumn at payload; omega
  · exact markers
  · exact cells
  · exact count
  · exact (t.before_limit_le_endAddress w u v k).trans_lt word

/-- The concrete signed profile emits routing words, private markers, 28 task
controls and nine fragment controls, then the chosen prefix, both marked
header banks, and the remaining outputs. Its literal output arity supplies
the two output-room premises directly. -/
theorem Layout.openRoom_of_profile (t : Layout) {frame fresh profile gates bits J ports b q o w u v k : ℕ}
    (low : frame+112 ≤ fresh)
    (markers : t.cube.cells+6*J+t.cube.cells ≤ 2^b)
    (cells : t.cube.cells ≤ t.p.report.cells) (count : J ≤ t.p.report.bundles)
    (word : t.endAddress w u v k < 2^w) :
    let outputs := t.cube.cables*3+(RoutingOutputs.count t.cube.cables t.cube.cells J ports+
      ((t.cube.cells+(J+t.cube.cells))+(28+(9+(q+((2^b+2^b)+o))))))
    let origin := GeometryAdvice.Allocation.dest fresh profile gates outputs bits
    let tables := RoutingOutputs.bases origin t.cube.cables t.cube.cells J
    let control := RoutingOutputs.controlsBase origin t.cube.cables t.cube.cells J ports
    t.cube.header.header = GeometryAdvice.Allocation.stop fresh profile gates outputs bits w →
    t.p.bundlePayload = control+37+q → t.p.bundleInverse = t.p.bundlePayload+2^b →
    t.OpenRoom frame tables.ends control tables.livePairs ports J (2^b) w := by
  intro outputs origin tables control cube payload rank
  let sortColumn := t.cube.cables*3+RoutingOutputs.count t.cube.cables t.cube.cells J ports+
    (t.cube.cells+(J+t.cube.cells))+37+q
  apply t.openRoom_of_geometry (sortColumn:=sortColumn) low _ _ cube _ rank markers cells count word
  · dsimp only [outputs]; omega
  · dsimp only [sortColumn,outputs]; omega
  · rw [payload]
    change control+37+q=origin+sortColumn
    dsimp only [control,sortColumn,RoutingOutputs.controlsBase,RoutingOutputs.bases,RoutingOutputs.count]
    omega

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
