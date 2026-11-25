import OAI.Computability.BorderVNP.RoutingISAScheduleClock
import OAI.Computability.BorderVNP.CubeLabelNative
import OAI.Computability.BorderVNP.CubeGroupNativeCheckedRun
import OAI.Computability.BorderVNP.CubeISAHeaderInstallGeometry
import OAI.Computability.BorderVNP.CubeISALengthScan
import OAI.Computability.BorderVNP.TransmissionDataProgram

/-! # Measured native grouping work on the actual boundary memories

The eleven boundary checks are the frame reads, representability and
non-aliasing premises of the individual word programs. A failed validation
has no returning run. Every returning execution with the indicated layout
satisfies the clock derived from the counted native loops.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM BorderVNP.Cube

/-- Concrete placements of the public arrays at their stages. -/
structure Placements where
  /-- Processed cable interval directory. -/
  intervals : NativeIntervals.Layout
  /-- Scalar data used to install the secondary header. -/
  header : CubeHeaderInstall.Inputs
  /-- Base of the copied broadcast. -/
  broadcast : ℕ
  /-- Address of the little-endian powers table. -/
  powers : ℕ
  /-- Histogram of local traffic by symbol. -/
  groups : GroupWeights.Layout
  /-- Owner and team load arrays. -/
  teams : TeamNative.Layout
  /-- True per-team exterior budget. -/
  exterior : ℕ
  /-- Computed two-word cell entries. -/
  banks : CellBanks.Layout
  /-- The full product-label pair directory. -/
  pairs : PairDirectory.Layout
  /-- Shared intervals appended to the data demand prefix. -/
  shared : SharedRows.Layout

private theorem bounded_cost {w k : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {c : Code} {s m es t mt} {post : NatState → Prop} (r : Runs pub mac c s m es t mt)
    (det : c.deterministic=true) (b : BoundedRun pub mac c s m k post) : traceCost es ≤ k := by
  obtain ⟨fs,u,mu,r',h,_⟩ := b
  obtain ⟨rfl,_,_⟩ := r'.unique_of_deterministic det r
  exact h

private theorem checked_cost {w k : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {c : Code} {s m es t mt} {ok : Prop} {post : NatState → Prop} (r : Runs pub mac c s m es t mt)
    (det : c.deterministic=true) (test : TestRun pub mac c s m k ok post) : traceCost es ≤ k :=
  bounded_cost r det (test.complete (test.sound r).1)

/-- A word fragment and its clock derived from raw operands at entry. -/
structure Pass {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) where
  /-- Native instructions. -/
  code : Code
  /-- Computed allowance. -/
  ticks : ℕ
  /-- Required addresses, field contents and representable values. -/
  ready : Memory w → Prop
  /-- Bound on every returning execution at a ready memory. -/
  measured : ∀ {s m es t mt}, ready m → Runs pub mac code s m es t mt → traceCost es ≤ ticks

variable {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)

/-- The actual frame satisfies each successive operand precondition on all
memories returned by the preceding fragments. -/
def AtEntries : List (Pass pub mac) → Bank w → Memory w → Prop
  | [], _, _ => True
  | p :: ps, s, m => p.ready m ∧ ∀ es t mt, Runs pub mac p.code s m es t mt → AtEntries ps t mt

private theorem block_cost (ps : List (Pass pub mac)) (nonempty : ps ≠ []) {s m es t mt}
    (ready : AtEntries pub mac ps s m) (run : Runs pub mac (.block (ps.map Pass.code)) s m es t mt) :
    traceCost es ≤ (ps.map Pass.ticks).sum := by
  induction ps generalizing s m es t mt with
  | nil => contradiction
  | cons p tail ih =>
    cases tail with
    | nil => simpa using p.measured ready.1 run
    | cons q qs =>
      obtain ⟨e,u,mu,f,rfl,first,rest⟩ := CellDispatch.seq_split run
      simpa only [traceCost,VPVNP.RAMBuckets.cost_append,List.map_cons,List.sum_cons] using
        Nat.add_le_add (p.measured ready.1 first) (ih (by simp) (ready.2 e u mu first) rest)

private def labels (z : ℕ) (m₀ : Memory w) : Pass pub mac :=
  let base := (pub 0).val
  let old := readings m₀
  let l := LabelIndex.layout base old
  let lab := old (base+48)
  ⟨LabelIndex.directoryProgram,LabelIndex.directoryTicks l z old,fun m =>
    m=m₀ ∧ LabelIndex.Endpoints l old ∧ LabelIndex.Allocated l ∧ l.labels=z+1 ∧
    lab+l.cells ≤ l.heads ∧ base+56 < l.heads ∧ l.dataMean+l.labels ≤ 2^w ∧
    LabelIndex.wordEnvelope l.labels (LabelIndex.inputWidth l old) < 2^w,
    by
      rintro s m es t mt ⟨rfl,ep,alloc,sz,sep,frame,room,cap⟩ run
      obtain ⟨fs,u,mu,other,b,_⟩ := LabelIndex.native_table_codes pub mac z s m ep alloc sz sep frame room cap
      obtain ⟨rfl,_,_⟩ := other.unique_of_deterministic LabelIndex.directoryProgram_deterministic run
      exact b⟩

private def intervals (l : LabelIndex.Layout) (p : Placements) : Pass pub mac :=
  let i := p.intervals
  ⟨NativeIntervals.prepare,NativeIntervals.setup.slots+(4*l.labels^2+2)+(2+l.cableCount*(NativeIntervals.cableStep.slots+1)),
    fun m => i.Fits w (readings m) ∧ (pub 0).val=i.frame ∧ i.Fields (readings m) ∧ i.alphabet=l.labels ∧ i.count=l.cableCount,
    by
      rintro s m es t mt ⟨fit,base,fields,z,rows⟩ run
      simpa only [← z,← rows] using bounded_cost run (by decide) (NativeIntervals.run_prepare pub mac i s m fit base fields)⟩

private def powers (p : Placements) : Pass pub mac :=
  let d := p.header.d
  let a := p.header.a
  ⟨CubePowers.install,16+5*a,fun m =>
    readings m (readings pub 0+59)=d ∧ readings m (readings pub 0+60)=a ∧
    readings m (readings pub 0+62)=p.powers ∧ 1 ≤ d ∧ readings pub 0+62 < 2^w ∧ p.powers+a < 2^w ∧ d^a < 2^w,
    by
      rintro s m es t mt ⟨hd,ha,hb,positive,base,room,count⟩ run
      exact bounded_cost run (by decide) (CubePowers.install_run pub mac s m d a p.powers hd ha hb positive base room count)⟩

private def installHeader (n bits : ℕ) (p : Placements) : Pass pub mac :=
  let h := p.header
  ⟨CubeHeaderInstall.install n bits,h.cost n bits,fun m => h.Loaded (readings pub) (readings m) ∧ h.Fits w n bits (readings pub 0),
    by
      rintro s m es t mt ⟨load,fit⟩ run
      exact bounded_cost run (CubeHeaderInstall.install_deterministic ..) (CubeHeaderInstall.install_run pub mac s m h load fit)⟩

private def decodeHeader (p : Placements) : Pass pub mac :=
  let d := p.header.decoder p.broadcast
  ⟨HeaderDecode.program,HeaderDecode.cost d + HeaderTotals.cost d.a (d.d*d.d),fun m =>
    HeaderDecode.Fits d w ∧ HeaderDecode.AtFrame d (readings pub) (readings m) ∧
    readings pub 0+63 < 2^w ∧ d.header+12 < 2^w ∧ d.totals+d.a ≤ 2^w ∧
    (d.dense+d.entries ≤ d.totals ∨ d.totals+d.a ≤ d.dense) ∧ d.d*d.d*d.cap < 2^w,
    by
      rintro s m es t mt ⟨fit,fields,base,header,totals,apart,sumFits⟩ run
      exact checked_cost run (by decide) (HeaderDecode.program_run _ _ _ fit fields base header totals apart sumFits)⟩

private def minimum (p : Placements) : Pass pub mac :=
  ⟨CubeLengths.minimum,CubeLengths.minSetup.slots+CubeLengths.pivot.slots+p.header.a*(CubeLengths.minBody.slots+1)+2,
    fun m => CubeLengths.Fits w (readings pub) (readings m) ∧
      (CubeLengths.layout (readings pub) (readings m)).coordinates=p.header.a,
    by
      rintro s m es t mt ⟨fit,axes⟩ run
      simpa only [axes] using checked_cost run (by decide) (CubeLengths.minimum_run s m fit)⟩

private def assign (p : Placements) : Pass pub mac :=
  let g := p.groups
  let t := p.teams
  let X := p.exterior
  ⟨GroupWeights.checkedSchedule,GroupWeights.checkedTicks g t,fun m =>
    readings pub 0=g.frame ∧ GroupWeights.CheckedFrame g t (readings m) w X ∧
    ∑ i ∈ Finset.range g.groups,g.weight (readings m) i < 2^w,
    by
      rintro s m es u mu ⟨base,h,sumFits⟩ run
      let first := GroupWeights.run_schedule pub mac g t s m base h.fields h.setup h.fits h.allocated h.frameFit h.frame
        h.groups h.weights h.keepAssign sumFits
      let test := GroupWeights.checked_test pub mac g t s m X first _ rfl (base ▸ h.budgetFields)
        (base ▸ h.budgetFits) (base ▸ h.keepBudget)
      exact checked_cost run (by decide) test⟩

private def cellBanks (l : LabelIndex.Layout) (p : Placements) : Pass pub mac :=
  let b := p.banks
  ⟨CellBanks.install,CellBanks.setup.slots+l.cells*15+1,fun m =>
    readings pub 0=b.frame ∧ b.Fields (readings m) ∧ b.Fits w ∧ b.cells=l.cells,
    by
      rintro s m es t mt ⟨base,fields,fit,cells⟩ run
      simpa only [cells] using bounded_cost run (by decide) (CellBanks.install_run pub mac b s m base fields fit)⟩

private def pairs (l : LabelIndex.Layout) (p : Placements) : Pass pub mac :=
  let v := p.pairs
  ⟨PairDirectory.directory,30+l.labels*l.labels*(24+27*p.header.a),fun m =>
    v.Fits w ∧ (pub 0).val=v.frame ∧ v.Fields (readings m) ∧ v.Z=l.labels ∧ v.axes=p.header.a,
    by
      rintro s m es t mt ⟨fit,base,fields,z,axes⟩ run
      simpa only [PairDirectory.Layout.count,z,axes] using
        (PairDirectory.directory_image_of_run pub mac v fit base fields run).1⟩

private def data (l : LabelIndex.Layout) : Pass pub mac :=
  ⟨Transmission.DataWriter.program,Transmission.DataWriter.setup.slots+l.deliveryCount*(Transmission.DataWriter.step.slots+1)+5,
    fun m => let d := Transmission.DataWriter.layout (readings pub) (readings m)
      (pub 0).val+72 < 2^w ∧ 0 < d.pins.teams ∧ d.pins.stride < 2^w ∧
      d.output+d.count*7 < 2^w ∧ Transmission.DataWriter.Separate d (readings m) ∧
      (∀ i < d.count, Transmission.DataWriter.RowFits w d (readings m) i) ∧ d.count=l.deliveryCount,
    by
      rintro s m es t mt ⟨base,teams,stride,endFit,apart,rowFit,count⟩ run
      obtain ⟨fs,u,other,b⟩ := Transmission.DataWriter.program_runs pub mac s m base teams stride endFit apart rowFit
      obtain ⟨rfl,_,_⟩ := other.unique_of_deterministic (by decide) run
      simpa only [count] using b⟩

private def sharedRows (p : Placements) : Pass pub mac :=
  let x := p.shared
  ⟨SharedRows.program,SharedRows.budget p.groups.groups,fun m =>
    x.Fits w (readings m) ∧ (pub 0).val=x.frame ∧ x.Fields (readings m) ∧ x.groups=p.groups.groups,
    by
      rintro s m es t mt ⟨fit,base,fields,g⟩ run
      simpa only [g] using bounded_cost run (by decide) (SharedRows.run_program pub mac x s m fit base fields)⟩

/-- The native stage checks in the precise sequence of `scheduleGroups`. -/
def passes (z n bits : ℕ) (m : Memory w) (p : Placements) : List (Pass pub mac) :=
  let l := LabelIndex.layout (pub 0).val (readings m)
  [labels pub mac z m,intervals pub mac l p,powers pub mac p,installHeader pub mac n bits p,
    decodeHeader pub mac p,minimum pub mac p,assign pub mac p,cellBanks pub mac l p,pairs pub mac l p,
    data pub mac l,sharedRows pub mac p]

/-- Every returning execution incurs at most the sum of the two measured
components. The only hypotheses on the path are the public input, word-room
and layout predicates at each preceding fragment's output. -/
theorem scheduleGroups_traceCost (z n bits : ℕ) (p : Placements) {s m es t mt}
    (ready : AtEntries pub mac (passes pub mac z n bits m p) s m)
    (run : Runs pub mac (scheduleGroups n bits) s m es t mt) :
    let l := LabelIndex.layout (pub 0).val (readings m)
    traceCost es ≤ descriptorTicks l (readings m) z p.header.a p.groups p.teams +
      declarationTicks (p.header.decoder p.broadcast) n bits := by
  let ps := passes pub mac z n bits m p
  have charged := block_cost pub mac ps (by simp [ps,passes]) ready run
  apply charged.trans_eq
  simp only [ps,passes,labels,intervals,powers,installHeader,decodeHeader,minimum,assign,cellBanks,
    pairs,data,sharedRows,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,
    descriptorTicks,declarationTicks,CubeHeaderInstall.Inputs.cost,CubeHeaderInstall.Inputs.decoder]
  ac_rfl

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
