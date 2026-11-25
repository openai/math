import OAI.ThreeFlat.Diagonal.InitialSeedProcedure
import OAI.ThreeFlat.Diagonal.PhysicalRecordFamily

namespace OAI
/-! # Public directory field bounds for the physical archive -/
namespace ThreeFlat.Diagonal.NavigationDirectory
open CompressorPacking.Native.ShrinkStage

/-- All physical dimensions whose scalar values are written without a stride have
a positive base and lane radix. This includes the smallest one-site allocation. -/
def Stage.positive : Stage → Prop
  | .shrink x => 0<x.oldBase ∧ 0<x.oldDegree ∧ 0<x.tagRadix ∧ 0<x.residual
  | .refresh v m l _ _ => 0<v ∧ 0 < m ∧ 0 < l

theorem Stage.nodes_le_heapWords (s : Stage) : s.nodes≤ s.heapWords := by
  cases s <;> simp only [Stage.nodes,Stage.heapWords,Nat.add_mul] <;> omega

set_option maxHeartbeats 2400000 in
/-- Each literal and pointer in the complete 64-word stage header lies below the
next heap extent. This accounts for the elected-layout field and dispatch degree. -/
theorem allocated_word_le (K : ℕ) (c : Cursor) (s : Stage) (pos : s.positive)
    (header : c.header+64≤c.heap) (counts : c.dense≤c.heap) (nodes : c.node≤c.heap)
    (graph : c.graph≤c.heap) (width : c.width≤c.heap) (i : Fin 64) :
    (allocate K c s).words i.val≤(allocate K c s).next.heap := by
  obtain ⟨i,hi⟩:=i
  cases s with
  | shrink x =>
    rcases pos with ⟨v,d,t,l⟩
    have lanes : x.originalLanes≤x.originalSites := Nat.le_mul_of_pos_left _ v
    have first : x.residual≤x.originalLanes :=
      ((Nat.le_mul_of_pos_right _ t).trans (Nat.le_mul_of_pos_right _ d)).trans
        (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos x.colorBits))
    have second : x.tagRadix≤x.originalLanes :=
      ((Nat.le_mul_of_pos_left _ l).trans (Nat.le_mul_of_pos_right _ d)).trans
        (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos x.colorBits))
    have third : x.oldDegree≤x.originalLanes :=
      (Nat.le_mul_of_pos_left _ (Nat.mul_pos l t)).trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos x.colorBits))
    interval_cases i <;> norm_num [allocate,headerWord,extraEnd,headerExtra] <;> omega
  | refresh v m l h p =>
    obtain ⟨vp,mp,lp⟩:=pos
    let x:=RefreshStageLayout.counts v m l h p
    have lo : l≤x.motifs:=Nat.le_mul_of_pos_left _ vp
    have port : m≤x.oldGraphRows:=Nat.le_mul_of_pos_left _ vp
    have motifs : x.choiceSpan=3*x.motifs:=rfl
    have rows : x.splitSpan=3*x.oldGraphRows:=rfl
    have graphRows : x.graphSpan=6*x.newGraphRows:=rfl
    dsimp only [x] at lo port motifs rows graphRows
    interval_cases i <;> norm_num [allocate,RefreshStageLayout.words,RefreshStageLayout.extraEnd,
      RefreshStageLayout.headerExtra,Nat.add_mul] <;> omega

theorem tape_word_lt (K : ℕ) (steps : List Stage) (c : Cursor) (bound : ℕ)
    (pos : ∀ s∈steps,s.positive) (header : c.header+64*steps.length≤c.heap)
    (counts : c.dense+K*(steps.map Stage.motifs).sum≤c.heap) (nodes : c.node≤c.heap)
    (graph : c.graph≤c.heap) (width : c.width≤c.heap)
    (room : c.heap+(steps.map Stage.heapWords).sum<bound) : ∀v∈tape K steps c,v<bound := by
  induction steps generalizing c with
  | nil => simp [tape]
  | cons s ss ih =>
    let out:=(allocate K c s).next
    have heap : out.heap=c.heap+s.heapWords:=heap_step ..
    have head : out.header=c.header+64 := by cases s <;> rfl
    have den : out.dense=c.dense+K*s.motifs := by cases s <;> rfl
    have id : out.node=c.node+s.nodes := by cases s <;> rfl
    have nh:=s.nodes_le_heapWords
    have ranges:=successor_resident K c s
    have g : out.graph≤out.heap := (Nat.le_add_right ..).trans ranges.2.2.1
    have w : out.width≤out.heap := (Nat.le_add_right ..).trans ranges.2.2.2
    simp only [List.length_cons,List.map_cons,List.sum_cons,Nat.mul_add] at header counts room
    intro v hv
    rcases List.mem_append.mp hv with hi|tail
    · obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hi
      have roomNext : out.heap<bound := by omega
      exact (allocated_word_le K c s (pos _ List.mem_cons_self) (by omega) (by omega) nodes graph width i).trans_lt roomNext
    · exact ih out (fun a ha=>pos a (List.mem_cons_of_mem _ ha)) (by omega) (by omega) (by omega)
        g w (by omega) _ tail


end ThreeFlat.Diagonal.NavigationDirectory

namespace ThreeFlat.Diagonal.PhysicalStage.Program
open NavigationDirectory CompressorPacking.Native.ShrinkStage
variable {F : Type} [Field F]

theorem directory_positive {s : ℕ} (P : Program F s) (r v : ℕ) (hv : 0<v) :
    ∀ z∈P.directory r v,z.positive := by
  induction P generalizing v with
  | done => simp [directory]
  | shrink s t T small tail ih =>
    intro z hz
    rcases List.mem_cons.mp hz with eq|rest
    · subst z; exact ⟨hv,Nat.two_pow_pos _,Nat.two_pow_pos _,Nat.two_pow_pos _⟩
    · exact ih _ (Nat.mul_pos hv (Nat.two_pow_pos _)) z rest
  | refresh s t h p c g b T hm hh sym rows zero conn deg tail ih =>
    intro z hz
    rcases List.mem_cons.mp hz with eq|rest
    · subst z; exact ⟨hv,Nat.two_pow_pos _,Nat.two_pow_pos _⟩
    · exact ih _ (Nat.mul_pos hv (Nat.two_pow_pos _)) z rest


end ThreeFlat.Diagonal.PhysicalStage.Program

namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM PrivateRAM RAM PhysicalStage
open scoped Classical
noncomputable section

theorem Archive.seedTime_linear (A : Archive) (lanes : 0<A.remainingLanes) :
    A.seedTime≤59+(2028*A.initialDegree+6*A.initialDegree+
      Archive.metadataCoefficient A.initialDegree)*A.initialSites := by
  have sites : A.axes≤A.initialSites := Nat.le_mul_of_pos_right _ lanes
  unfold Archive.seedTime
  calc
    _≤59+2028*(A.initialSites*A.initialDegree)+6*((A.axes*A.initialDegree)*A.remainingLanes)+
        Archive.metadataCoefficient A.initialDegree*A.initialSites := by gcongr
    _=_ := by unfold Archive.initialSites;ring

end

end ThreeFlat.Diagonal.NavigationPass

end OAI
