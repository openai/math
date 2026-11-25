import OAI.Hierarchy.TraceSeedWriter
import OAI.Hierarchy.TraceIterationPlacement
import OAI.ThreeFlat.Diagonal.SeedDirectoryWords

namespace OAI
/-! # Initial graph, widths and public directory at the mounted trace addresses -/
noncomputable section
namespace Hierarchy.TraceSeedWriter
open ThreeFlat Diagonal Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM RAM NavigationPass NavigationDirectory TraceDistribution TraceAdmission Filter
open scoped Classical BigOperators
variable {F : Type} [Field F] (B : Block F)

/-- At the allocated addresses the complete initial graph, width and kernel row files
are disjoint from the physical scan controls. -/
theorem placed {w β : ℕ} {A : Archive} (atBase : ArchivePlacement A β w) (hw : 7≤w)
    (top : β+8*(2^w)^4<2^(64*w))
    (g : 6*(A.axes*A.initialDegree)≤(2^w)^4)
    (width : (A.axes*A.initialDegree)*A.remainingLanes≤(2^w)^4)
    (records : (7+8*A.initialDegree)*A.initialSites≤(2^w)^4) :
    Space A (64*w) ∧ A.cursor.dense≤A.cursor.graph ∧ A.cursor.dense≤A.cursor.width ∧
      A.cursor.graph+6*(A.axes*A.initialDegree)≤A.cursor.heap ∧
      A.cursor.width+(A.axes*A.initialDegree)*A.remainingLanes≤A.cursor.heap := by
  have h : 64≤(2^w)^4 := calc
    64 ≤ 2^w := by
      change 2^6≤2^w;exact Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ (2^w)^4 := Nat.le_self_pow (by decide) _
  rw [atBase.graph,atBase.dense,atBase.width,atBase.heap]
  refine ⟨⟨⟨?_,?_,?_,?_⟩,?_,?_,?_⟩,by omega,by omega,by omega,by omega⟩
  · rw [atBase.control];omega
  · rw [atBase.seed,atBase.graph];omega
  · rw [atBase.graph,atBase.width];omega
  · rw [atBase.width,atBase.control];omega
  · rw [atBase.width,atBase.records];omega
  · rw [Archive.metadataEnd,atBase.records,atBase.control];omega
  · rw [atBase.control];omega

/-- The three initial scan extents fit a sector simultaneously. -/
theorem eventual_seed_arrays {u s : ℕ→ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ (A : Archive) (_de : A.initialDegree=2^(B.exponent 0))
      (_ax : A.axes=u w+1-w/2) (_lanes : A.remainingLanes=2^A.axes),
      6*(A.axes*A.initialDegree)≤(2^w)^4 ∧
      (A.axes*A.initialDegree)*A.remainingLanes≤(2^w)^4 ∧
      (7+8*A.initialDegree)*A.initialSites≤(2^w)^4 := by
  let d:=2^(B.exponent 0)
  filter_upwards [record_room scale (7+8*d)] with w room
  intro A de ax lanes
  have small : 2^(3*w/5)≤(2^w)^4 := by
    rw [←pow_mul];exact Nat.pow_le_pow_right (by decide) (by omega)
  have core : (7+8*d)*((u w+1-w/2)*2^(u w+1-w/2))≤2^(3*w/5) := by
    apply le_trans _ room
    ring_nf
    omega
  have paid : (7+8*A.initialDegree)*A.initialSites≤(2^w)^4 := by
    simpa only [Archive.initialSites,lanes,ax,de,d] using core.trans small
  have axis : A.axes≤A.initialSites := Nat.le_mul_of_pos_right _ (by rw [lanes];exact Nat.two_pow_pos _)
  exact ⟨(Nat.mul_le_mul_left 6 (Nat.mul_le_mul_right _ axis)).trans (by
      calc
        6*(A.initialSites*A.initialDegree) ≤ (7+8*A.initialDegree)*A.initialSites := by ring_nf;omega
        _ ≤ _ := paid),by
      calc
        (A.axes*A.initialDegree)*A.remainingLanes = A.initialDegree*A.initialSites := by
          unfold Archive.initialSites;ring
        _ ≤ (7+8*A.initialDegree)*A.initialSites := Nat.mul_le_mul_right _ (by omega)
        _ ≤ _ := paid,paid⟩

/-- All public seed and stage words are genuine values.  Only the two terminal
scalars vary with the chosen terminal address range. -/
theorem directory_fits {W lim cap d : ℕ} (P : Program F d) (A : Archive) (rem : ℕ)
    (space : Space A W) (cur : Word W) (steps : List Stage) (edges : ℕ)
    (shape : steps=P.directory rem A.axes) (positive : 0<A.axes)
    (limits : A.TraceLimits lim cur steps edges cap) (node : A.cursor.node=0)
    (fits : A.remainingLanes=2^A.axes) (lane : A.remainingLanes<2^W)
    (deg : 2*A.initialDegree<2^W) (head : A.cursor.dense≤A.cursor.graph)
    (heap : A.initialRecords≤A.cursor.heap)
    (terminalCapacity : (A.terminal steps edges W).capacity+1<2^W)
    (terminalPrefix : (A.terminal steps edges W).prefixBase<2^W)
    (terminalEdges : edges+1<2^W) :
    ∀ v∈A.directory steps edges W,v<2^W := by
  have bounds := space.meta
  have capG : A.cursor.graph+6*(A.axes*A.initialDegree)≤A.initialRecords :=
    space.graphBefore.trans ((Nat.le_add_right ..).trans space.widthsToRecords)
  have axesFit : A.axes<2^W := Nat.lt_two_pow_self.trans (by simpa only [fits] using lane)
  have fin := bounds.endFit
  unfold Archive.metadataEnd at fin
  have widthFit := space.widthsToRecords
  have limit := limits.tables
  rw [Archive.directory_length] at limit
  have hist := limits.raw
  have extent := limits.controls.trans_lt cur.isLt
  have headers : A.cursor.header+64*steps.length≤A.cursor.heap := by
    rw [limits.origin];rw [Nat.mul_add] at limit;omega
  have tape:=tape_word_lt A.K steps A.cursor (2^W)
    (by simpa only [shape] using P.directory_positive rem A.axes positive) headers hist (by rw [node];exact Nat.zero_le _)
    ((Nat.le_add_right ..).trans (capG.trans heap))
    ((Nat.le_add_right ..).trans (widthFit.trans heap)) extent
  intro v hv
  rcases List.mem_append.mp hv with seed|body
  · obtain ⟨⟨i,hi⟩,rfl⟩:=List.mem_ofFn.mp seed
    rw [Nat.add_mul] at fin
    have : 5*A.initialSites≤7*A.initialSites := by omega
    interval_cases i <;> norm_num [Archive.seedWords] <;> omega
  · rcases List.mem_append.mp body with middle|last
    · exact tape v middle
    · obtain ⟨⟨i,hi⟩,rfl⟩:=List.mem_ofFn.mp last
      change (A.terminal steps edges W).edges+1<2^W at terminalEdges
      interval_cases i <;> norm_num [TerminalWireArchive.header] <;> omega

open scoped Fin.CommRing in
/-- Mount actual big-endian public template words and the physical selector bits
after its branch flag. Both history selectors point to the same raw body. -/
theorem sources {W : ℕ} (A : Archive) (steps : List Stage) (edges rawStatic rawGuess : ℕ)
    (raw : ℕ→Bool) (input : Memory W) (cap : A.codebookWords=0)
    (static : A.rawStatic=rawStatic) (book : A.rawCodebook=rawStatic)
    (dest : A.staticCodebook=A.seed) (phase : A.phase<A.seed)
    (old : A.oldHistory=rawGuess) (new : A.newHistory=rawGuess)
    (seedFit : A.seed<2^W) (dirLow : rawStatic+W*(A.directory steps edges W).length≤A.seed)
    (histLow : rawGuess+W*A.histWords steps≤A.seed)
    (separate : A.seed+(A.directory steps edges W).length≤A.cursor.dense)
    (fits : ∀v∈A.directory steps edges W,v<2^W)
    (params : ∀i<(A.directory steps edges W).length,∀j<W,input (rawStatic+W*i+j)=
      (((((A.directory steps edges W)[i]?.getD 0:ℕ):Word W).val.testBit (W-1-j)).toNat:Word W))
    (hist : ∀i<W*A.histWords steps,input (rawGuess+i)=(raw i).toNat) :
    A.SeedSources steps edges [] [] raw input := by
  have read : (A.hist steps).source input=rawGuess := by
    simp [Archive.hist,PackedStageArchive.Layout.source,old,new]
  refine ⟨by simpa using cap,by simp [static,book],phase,by rw [dest],
    by simpa [dest] using seedFit,by simpa only [static] using dirLow,
    by simpa only [read] using histLow,separate,fits,?_,by simpa only [read] using hist⟩
  simpa only [List.nil_append,List.append_nil,book] using params

/-- Full native startup time, including packing the public headers and chosen raw
histograms, publishing the initial five-field kernels and advancing both cells. -/
theorem eventual_seed_time {u s : ℕ→ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ (A : Archive) (edges : ℕ)
      (_fit : B.blockCharge*s w≤u w+1-w/2) (_de : A.initialDegree=2^(B.exponent 0))
      (_ax : A.axes=u w+1-w/2) (_lanes : A.remainingLanes=2^A.axes)
      (_alpha : A.K=B.alphabetCap) (_cap : A.codebookWords=0),
      let P:=B.repeat (s w)
      let steps:=P.directory (A.axes-P.charge) A.axes
      A.bootTime steps edges (64*w)+A.seedTime+6≤2^(3*w/5) := by
  let d:=2^(B.exponent 0)
  let D:=2028*d+6*d+Archive.metadataCoefficient d
  let C:=(B.levels+1)*B.costFactors.sum*B.alphabetCap
  let SH:=64*(B.levels+3)
  let total:=6*(SH+C+1)+D+100
  filter_upwards [record_room scale total] with w room
  intro A edges fit de ax lanes alpha cap P steps
  let n:=s w
  let v:=A.axes*2^A.axes
  have positive : 0<A.remainingLanes := by rw [lanes];exact Nat.two_pow_pos _
  have seed : A.seedTime≤59+D*v := by
    simpa only [D,d,v,Archive.initialSites,lanes,de] using A.seedTime_linear positive
  have len : (A.directory steps edges (64*w)).length≤SH*(n+1) := by
    rw [Archive.directory_length,Program.directory_length]
    change 64*((B.repeat n).length+2)≤_
    rw [B.length_repeat]
    dsimp [SH,n];ring_nf;omega
  have cnt : A.histWords steps≤C*n*v := by
    have count:=stage_count_sum_le B n A.axes (by simpa only [n,ax] using fit)
    change A.K*(steps.map Stage.motifs).sum≤_
    rw [alpha,Nat.mul_comm]
    calc
      _ ≤ ((B.levels+1)*n*B.costFactors.sum*(A.axes*2^A.axes))*B.alphabetCap :=
          Nat.mul_le_mul_right _ count
      _ = _ := by dsimp [C,v];ring
  have price : 5*(64*w)+6≤6*(64*w+1) := by omega
  have boot : A.bootTime steps edges (64*w)≤
      33+SH*(n+1)*(6*(64*w+1))+(C*n*v)*(6*(64*w+1)) := by
    unfold Archive.bootTime
    rw [cap,zero_mul]
    have a:=Nat.mul_le_mul len price
    have b:=Nat.mul_le_mul cnt price
    omega
  calc
    _ ≤ (33+SH*(n+1)*(6*(64*w+1))+(C*n*v)*(6*(64*w+1)))+(59+D*v)+6 :=
        Nat.add_le_add_right (Nat.add_le_add boot seed) _
    _ ≤ total*(n+1)*(1+v)*(64*w+1) := by dsimp [total];ring_nf;omega
    _ ≤ _ := by simpa only [n,v,ax] using room


end Hierarchy.TraceSeedWriter

end
end OAI
