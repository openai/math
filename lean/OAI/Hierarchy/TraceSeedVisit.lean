import OAI.Hierarchy.TraceSeedDirectories
import OAI.Hierarchy.TraceSeedLayerWords
import OAI.Hierarchy.TraceIterationTerminalRoom
import OAI.Hierarchy.TraceSeedPlacement

namespace OAI
/-! # Executable initialization of the counted repeated-stage visitor -/
noncomputable section
namespace Hierarchy.TraceSeedWriter
open ThreeFlat Diagonal Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM RAM RAM.PhysicalProcedure NavigationPass NavigationDirectory TraceDistribution TraceAdmission Filter
open scoped Classical BigOperators Fin.CommRing
variable {F : Type} [Field F] (B : Block F)

theorem archive_placement (w axes off slots cap rawStatic : ℕ) :
    ArchivePlacement (archive B w axes off slots cap rawStatic) (16*2^(32*w)) w :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- All scalar premises of the real initialization scans at a given width. -/
structure Fits (A : Archive) (steps : List Stage) (edges n k W : ℕ) : Prop where
  space : Space A W
  mount : A.MountedRange steps edges W
  bits : A.relayWidth<2^W
  axes : k+1≤W
  degree : 2*A.initialDegree<2^W
  lanes : 2^(k+1)<2^W
  word : 8<2^W
  clock : n<2^W
  denseGraph : A.cursor.dense≤A.cursor.graph
  denseWidth : A.cursor.dense≤A.cursor.width
  graphHeap : A.cursor.graph+6*(A.axes*A.initialDegree)≤A.cursor.heap
  widthHeap : A.cursor.width+(A.axes*A.initialDegree)*A.remainingLanes≤A.cursor.heap

/-- Coordinates and word bounds of the genuine initial node-bank header. -/
theorem layer_words {W k n edges : ℕ} {A : Archive} {steps : List Stage}
    (s : Fits A steps edges n k W) (node : A.cursor.node=0) (axes : k+1=A.axes)
    (lanes : A.remainingLanes=2^(k+1)) : LayerWords A (k+1) W := by
  have endFit:=s.space.meta.endFit
  rw [Archive.metadataEnd,Nat.add_mul] at endFit
  have base : A.seed<2^W :=
    ((Nat.le_add_right ..).trans (s.space.seedBefore.trans
      (s.space.toRelayWindow.columns.1.trans s.space.toRelayWindow.columns.2))).trans_lt s.space.controlRoom
  have extent : A.initialSites<2^W := by omega
  refine ⟨node,?_,rfl,rfl,rfl,?_,?_,base,?_⟩
  · change A.axes*A.remainingLanes=_
    rw [←axes,lanes]
  · change A.initialRecords<_;omega
  · change A.initialRecords+5*A.initialSites<_;omega
  · change A.cursor.node+A.initialSites<_;simpa only [node,zero_add] using extent

/-- No bounds on a stage-selected graph or history are inputs to the seed writer. -/
theorem eventual_fits {u s : ℕ→ℕ} (scale : Scale u s) (a b : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ (A : Archive) (β edges k off slots : ℕ)
      (_fit : B.blockCharge*s w≤k+1) (_ax : k+1=u w+1-w/2)
      (_de : 2^(B.exponent 0)=A.initialDegree) (_dims : k+1=A.axes)
      (_lanes : A.remainingLanes=2^(k+1)) (_wire : A.relayWidth=2^(w/2)*(off*slots*3))
      (_ports : off*slots*3≤a*(w+1)^b) (_alpha : A.K=B.alphabetCap)
      (_atBase : ArchivePlacement A β w) (_top : β+8*(2^w)^4<2^(64*w)),
      let P:=B.repeat (s w)
      let steps:=P.directory (k+1-P.charge) (k+1)
      Fits A steps edges (s w) k (64*w) := by
  have cap:=(tendsto_order.mp scale.cap).2 2 (by norm_num)
  filter_upwards [eventual_seed_arrays B scale, eventual_stage_headers B scale,
    eventual_record_length B scale, multiplicity_small scale 1 a b 1,record_room scale 1,cap,
    eventually_ge_atTop (7+2*2^(B.exponent 0))] with w arrays headers counts widths room upper large
  intro A β edges k off slots fit ax de dims lanes wire ports alpha atBase top P steps
  have hw : 7≤w := by omega
  have cardinal : 2^(3*w/5)≤(2^w)^4 := by rw [←pow_mul];exact Nat.pow_le_pow_right (by decide) (by omega)
  have wordFit : 2^(3*w/5)<2^(64*w) := Nat.pow_lt_pow_right (by decide) (by omega)
  have vfit : B.blockCharge*s w≤u w+1-w/2 := by simpa only [ax] using fit
  have arr:=arrays A de.symm (dims.symm.trans ax) (by simpa only [←dims] using lanes)
  have hull:=placed atBase hw top arr.1 arr.2.1 arr.2.2
  have lens : (A.directory steps edges (64*w)).length≤(2^w)^4 := by
    rw [Archive.directory_length];exact (headers _ _).trans cardinal
  have histogram : (64*w)*A.histWords steps≤2^(3*w/5) := by
    simpa only [Archive.histWords,alpha,steps,P,ax,stageCounts,Nat.mul_comm,Nat.mul_left_comm,
      Nat.mul_assoc] using counts vfit
  have words : A.histWords steps≤(2^w)^4 :=
    (Nat.le_mul_of_pos_left _ (by omega : 0<64*w)).trans (histogram.trans cardinal)
  have pos : (0:ℝ)<w := by exact_mod_cast (by omega : 0<w)
  have ub : u w≤2*w := by exact_mod_cast ((div_lt_iff₀ pos).mp upper).le
  have ks : k+1<64*w := by omega
  have nsize : s w ≤ 2^(3*w/5) := by
    apply le_trans _ room
    ring_nf;omega
  have widthCap : 2^(w/2)*(a*(w+1)^b)+1≤2^(3*w/5) := by simpa only [one_mul,one_pow,mul_one] using widths
  refine ⟨hull.1,⟨?_,?_⟩,?_,ks.le,?_,Nat.pow_lt_pow_right (by decide) ks,?_,
    nsize.trans_lt wordFit,hull.2.1,hull.2.2.1,hull.2.2.2.1,hull.2.2.2.2⟩
  · rw [atBase.seed,atBase.graph];omega
  · rw [atBase.dense,atBase.graph];omega
  · rw [wire];exact (Nat.mul_le_mul_left _ ports).trans_lt (by omega)
  · rw [←de];exact (by omega : 2*2^B.exponent 0≤64*w).trans_lt Nat.lt_two_pow_self
  · exact (by omega : 8≤64*w).trans_lt Nat.lt_two_pow_self

/-- The actual prestate of the counted controller. The initially read public
program and raw history determine the whole memory before the first stage. -/
theorem «initialize» {W k low off slots : ℕ} (hk : 2≤k+1) (A : Archive) (ss : List Stage)
    (edges n : ℕ) (de : 2^(B.exponent 0)=A.initialDegree) (ax : k+1=A.axes)
    (lanes : A.remainingLanes=2^(k+1)) (wire : A.relayWidth=2^low*(off*slots*3))
    (first : A.cursor.header=A.seed+64) (fits : Fits A ss edges n k W)
    (bits : ℕ→Bool) (input : Memory W) (src : A.SeedSources ss edges [] [] bits input) :
    let result:=memory A ss edges [] bits input n
    (procedure A ss edges n).Spec (fun m=>m=input) (fun _ out=>out=result) (A.bootTime ss edges W+A.seedTime+6) ∧
    A.Visit ss edges bits (A.control:Word W) [] (B.cursorState hk low off slots) result ∧
    (result (((A.control+1:ℕ):Word W).val)).val=n ∧
    A.seedData.Reads (fun z=>(result z).val) ∧
    A.seedData.Footprint (fun j=>A.initialRecords≤j ∧ j<A.metadataEnd) (fun z=>(result z).val) ∧
    ∀i,i<A.seed→ result i=input i := by
  intro result
  have r:=ready A ss edges B hk low off slots de ax lanes wire [] [] bits input n fits.space fits.mount src
    fits.bits fits.axes fits.degree fits.lanes fits.word first fits.clock
  have layers:=Archive.InitialNodeMetadata.seedData A
    (Archive.reseedDegree de (B.cursorState hk low off slots).graph) (finCongr ax) result
    r.nodes lanes fits.degree fits.bits fits.space.meta.endFit
  exact ⟨run A ss edges [] [] bits input n fits.space fits.mount src (de ▸ Nat.two_pow_pos _) (ax ▸ fits.axes) fits.word,
    r.visit lanes fits.denseGraph fits.denseWidth fits.graphHeap fits.widthHeap,r.counter,layers.1,
    Archive.InitialNodeMetadata.seedFootprint A (Archive.reseedDegree de (B.cursorState hk low off slots).graph)
      (finCongr ax) result r.nodes lanes fits.degree fits.bits fits.space.meta.endFit,r.low⟩

/-- On the native sector layout, both input observations are bitwise reads of the
receiver's input tape. The public directory consists of the original program's
stage coordinates and genuine terminal edge count. -/
theorem eventual_initialize {u s : ℕ→ℕ} (scale : Scale u s) (a b : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ (A : Archive) (k off slots : ℕ) (hk : 2≤k+1)
      (_fit : B.blockCharge*s w≤k+1) (_ax : k+1=u w+1-w/2)
      (_de : 2^(B.exponent 0)=A.initialDegree) (_dims : k+1=A.axes)
      (_lanes : A.remainingLanes=2^(k+1)) (_wire : A.relayWidth=2^(w/2)*(off*slots*3))
      (_ports : off*slots*3≤a*(w+1)^b) (_alpha : A.K=B.alphabetCap),
      let W:=64*w
      let J:=2^(32*w)
      let P:=B.repeat (s w)
      let rem:=k+1-P.charge
      let ss:=P.directory rem (k+1)
      let edges:=P.finalEdges rem (k+1)
      ∀ (_atBase : ArchivePlacement A (16*J) w) (_phase : A.phase=12*J)
        (_old : A.oldHistory=12*J+1) (_new : A.newHistory=12*J+1)
        (_pair : A.pairCapacity≤J) (rawStatic : ℕ) (_staticLow : rawStatic≤13*J)
        (_static : A.rawStatic=rawStatic) (_book : A.rawCodebook=rawStatic)
        (_empty : A.codebookWords=0) (_dest : A.staticCodebook=A.seed)
        (bits : ℕ→Bool) (input : Memory W)
        (_params : ∀i<(A.directory ss edges W).length,∀j<W,input (rawStatic+W*i+j)=
          (((((A.directory ss edges W)[i]?.getD 0:ℕ):Word W).val.testBit (W-1-j)).toNat:Word W))
        (_body : ∀i<W*A.histWords ss,input (12*J+1+i)=(bits i).toNat),
        let result:=memory A ss edges [] bits input (s w)
        (procedure A ss edges (s w)).Spec (fun m=>m=input) (fun _ out=>out=result) (2^(3*w/5)) ∧
        A.Visit ss edges bits (A.control:Word W) [] (B.cursorState hk (w/2) off slots) result ∧
        (result (((A.control+1:ℕ):Word W).val)).val=s w ∧
        A.seedData.Reads (fun z=>(result z).val) ∧
        A.seedData.Footprint (fun j=>A.initialRecords≤j ∧ j<A.metadataEnd) (fun z=>(result z).val) ∧
        ∀i,i<A.seed ∨ 17*J≤ i→ result i=input i := by
  filter_upwards [eventual_fits B scale a b,eventual_seed_time B scale,eventual_terminal_room B scale,
    eventual_iteration_limits B scale,eventually_ge_atTop 7] with w resources time terminal limits hw
  intro A k off slots hk fit ax de dims lanes wire ports alpha W J P rem ss edges atBase phase old new pair
    rawStatic staticLow static book empty dest bits input params body result
  have vfit : B.blockCharge*s w≤u w+1-w/2 := by simpa only [ax] using fit
  have top := sector_placement_room (w:=w) (by omega)
  have seed:=resources A (16*J) edges k off slots fit ax de dims lanes wire ports alpha atBase top.2
  have c : (A.control:Word W).val=A.control := Fin.val_cast_of_lt seed.space.controlRoom
  have lim : A.TraceLimits (2^w) (A.control:Word W) ss edges (2^(3*w/5)) := by
    simpa only [ss,rem,P,ax] using limits vfit A (16*J) edges (A.control:Word W) alpha atBase c
  have term : A.TerminalRoom ss edges W := by
    simpa only [ss,rem,edges,P,ax] using (terminal vfit A atBase alpha phase old new pair).2
  have budget : A.bootTime ss edges W + A.seedTime + 6≤2^(3*w/5) := by
    simpa only [ss,W,rem,P,←dims] using time A edges vfit de.symm (dims.symm.trans ax)
      (by simpa only [←dims] using lanes) alpha empty
  have hdr : ∀v∈A.directory ss edges W,v<2^W := by
    apply directory_fits P A rem seed.space (A.control:Word W) ss edges
      (by simp only [ss,←dims]) (by omega) lim atBase.node (by simpa only [←dims] using lanes)
      (by simpa only [lanes] using seed.lanes) seed.degree seed.denseGraph
    · rw [atBase.records,atBase.heap];omega
    · exact term.bounds.capacity
    · exact (Nat.le_add_right ..).trans_lt term.bounds.prefix
    · exact (Nat.le_add_left ..).trans_lt term.bounds.prefix
  have small : 2^(3*w/5)≤J := Nat.pow_le_pow_right (by decide) (by omega)
  have bytes : W*(A.directory ss edges W).length≤J := by
    refine le_trans ?_ (budget.trans small)
    rw [Nat.mul_comm]
    have amount := Nat.mul_le_mul_left (A.directory ss edges W).length (by omega : W≤5*W+6)
    unfold Archive.bootTime
    omega
  have bitsRoom:=lim.capacity.trans small
  have jPos : 0<J := Nat.two_pow_pos _
  have sf : A.seed<2^W := by rw [atBase.seed];exact (Nat.le_add_right ..).trans_lt top.2
  have src := sources A ss edges rawStatic (12*J+1) bits input empty static book dest
    (by rw [phase,atBase.seed];omega) old new sf
    (by rw [atBase.seed];omega) (by rw [atBase.seed];omega) lim.tables hdr params body
  obtain ⟨run,visit,clock,rows,foot,low⟩ := «initialize» B hk A ss edges (s w) de dims lanes wire
    lim.origin seed bits input src
  refine ⟨?_,visit,clock,rows,foot,?_⟩
  · intro programCount registerCount wordCount machine
    exact Procedure.Spec.mono run (fun _ h => h) (fun _ _ h => h) budget machine
  intro i hi
  rcases hi with h|h
  · exact low _ h
  · apply memory_above A ss edges bits input (s w) seed.space seed.mount src i
    rw [atBase.control]
    have o:=top.1
    have positive : 0<(2^w)^4 := Nat.pow_pos (Nat.two_pow_pos _)
    omega


end Hierarchy.TraceSeedWriter

end
end OAI
