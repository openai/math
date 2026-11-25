import OAI.ThreeFlat.Diagonal.NavigationRootPublication
import OAI.ThreeFlat.Diagonal.TraceEndpointInterval
import OAI.ThreeFlat.RAM.HistoryInitialEndpointScan

namespace OAI
/-! # Group-local endpoint positions for selected initial trace leaves -/

namespace ThreeFlat.Diagonal.NavigationPass.RootArchive

open Computability.VPVNP.BurstRAM RAM HistoryContraction TickWorkspace
open scoped Fin.CommRing BigOperators

variable {W : ℕ}

/-- The first position of this lane in the old or new pair half of its
scheduled group counts earlier intervals in the same group. -/
def packedStart (a : RootArchive) (g : Fin a.initialLanes→Fin a.groups) (i : Fin a.initialLanes) :=
  BucketRows.count g ((List.ofFn a.lane).take i.val) (g i)

private theorem split_lane (a : RootArchive) (i : Fin a.initialLanes) :
    ((List.ofFn a.lane).take i.val)++a.lane i::((List.ofFn a.lane).drop (i.val+1))=List.ofFn a.lane := by
  let xs:=List.ofFn a.lane
  have hi : i.val<xs.length := by simp [xs]
  have atI : xs[i.val]=a.lane i:=by simp [xs]
  change xs.take i.val++_::xs.drop (i.val+1)=xs
  rw [←atI,List.getElem_cons_drop,List.take_append_drop]

theorem packed_start (a : RootArchive) (g : Fin a.initialLanes→Fin a.groups) (i : Fin a.initialLanes) :
    (a.packedRow g i).offset=a.packedStart g i := by
  let xs:=List.ofFn a.lane
  let before:=xs.take i.val
  let after:=xs.drop (i.val+1)
  have split : before++a.lane i::after=xs:=a.split_lane i
  have n : (BucketRows.pack g (fun _=>0) before).length=i.val := by
    simp [before,xs,BucketRows.pack_length]
  have row:=BucketRows.middle g before (a.lane i) after
  rw [split] at row
  have obs:=congrArg (fun l : List (BucketRow (Fin a.groups))=>l[i.val]?) row
  have ok : i.val<(BucketRows.pack g (fun _=>0) xs).length:=by
    simp [BucketRows.pack_length,xs]
  rw [List.getElem?_eq_getElem ok,List.getElem?_append_right (by omega),n,Nat.sub_self] at obs
  exact congrArg BucketRow.offset (Option.some.inj obs)

theorem packed_slice (a : RootArchive) (g : Fin a.initialLanes→Fin a.groups) (i : Fin a.initialLanes) :
    a.packedStart g i+(a.lane i).size≤BucketRows.count g (List.ofFn a.lane) (g i) := by
  let xs:=List.ofFn a.lane
  change BucketRows.count g (xs.take i.val) (g i)+(a.lane i).size≤BucketRows.count g xs (g i)
  have split : xs.take i.val ++ a.lane i :: xs.drop (i.val+1) = xs := a.split_lane i
  conv_rhs => rw [←split]
  simp [BucketRows.count,lane,List.map_append,List.sum_append]

theorem lane_pairs (a : RootArchive) (i : Fin a.initialLanes) (low : ℕ) (span : a.pairsPerLane=2^low) :
    (a.lane i).size=TraceSuffix.pairs a.totalPairs low i.val := by
  rw [TraceSuffix.pairs_interval]
  simp only [lane,Bucket.size,clipped,TraceSuffix.boundary,span,Nat.min_comm a.totalPairs]

theorem groups_le_total (a : RootArchive) (g : Fin a.initialLanes→Fin a.groups) (j : Fin a.groups)
    (low : ℕ) (span : a.pairsPerLane=2^low) :
    BucketRows.count g (List.ofFn a.lane) j≤a.totalPairs := by
  have all : BucketRows.count g (List.ofFn a.lane) j ≤ ∑ i : Fin a.initialLanes, (a.lane i).size := by
    simp only [BucketRows.count,List.map_ofFn,List.sum_ofFn,Function.comp_def]
    apply Finset.sum_le_sum
    intro i _
    split <;> omega
  simp_rw [fun i=>a.lane_pairs i low span] at all
  rw [TraceSuffix.pairs_prefix] at all
  exact all.trans (Nat.min_le_left ..)

/-- A single selected lane can have a positive global position and start
at zero in its own pair half. Both nonempty intervals here have width one. -/
theorem second_lane_alone :
    let xs : List (Bucket Bool):=[⟨false,0,1⟩,⟨true,1,2⟩]
    BucketRows.pack id (fun _=>0) xs=[⟨false,0,1,0⟩,⟨true,1,2,0⟩] := by decide

/-- The three native reads used to seed the leaf come from the group-local
row and the evaluator's two initialized pair pointers. -/
theorem pair_words {F : Type*} [Field F] [Fintype F] {B : TickActiveROM.Layout} {p H J : ℕ}
    {fit : RAM.Contraction.Fits (TickWeightedBank.shape F p H J) W} {clock : TickChronology.Clock}
    (x : TickActiveROM.CellInput B clock fit) (a : RootArchive)
    (g : Fin a.initialLanes→Fin a.groups) (i : Fin a.initialLanes) (low : ℕ)
    (span : a.pairsPerLane=2^low) (globalFit : a.totalPairs<2^W)
    (m out : Memory W) (done : a.packedPost g m out)
    (sel : TickPairHeader.selected out B.clockWords B.groupCounts clock.groups=(x.count:Word W))
    (rowHigh : B.auxRequest+8*B.bits≤base a.age 5)
    (boundsHigh : B.bounds+4≤base a.age 5) (boundsLow : B.bounds+4≤B.auxRequest)
    (boundsFit : B.bounds+4≤2^W) (auxFit : B.oldAux+B.bits<2^W) :
    let prepared:=x.filled .evaluate out
    (prepared (base a.age 5+4*i.val+3)).val=a.packedStart g i ∧
    (prepared (B.bounds+2)).val=B.oldAux+1+B.capacity ∧
    (prepared (B.bounds+3)).val=B.oldAux+1+B.capacity+x.count := by
  have r := done.1 i (3:Fin 4)
  change out (base a.age 5+4*i.val+3)=((a.packedRow g i).offset:Word W) at r
  rw [a.packed_start] at r
  have width:=a.packed_slice g i
  have count:=a.groups_le_total g (g i) low span
  have short : a.packedStart g i<2^W := by omega
  have val := TickActiveROM.bound_values B clock out x.count x.pairSpace boundsFit sel
  have room:=x.pairSpace
  have room0 : B.oldAux+1+B.capacity<2^W := by omega
  have room1 : B.oldAux+1+B.capacity+x.count<2^W := by omega
  refine ⟨?_,?_,?_⟩
  · rw [filled_high x out .evaluate _ boundsFit (by omega) (by omega),r,Fin.val_cast_of_lt short]
  · rw [show x.filled .evaluate out (B.bounds+2)=TickActiveROM.boundsMemory B clock out (B.bounds+2) from
      fill_frame _ _ _ _ _ (.inl (by omega))]
    have pointer : TickActiveROM.boundsMemory B clock out (B.bounds+2) =
        ((B.oldAux+(1+B.capacity):ℕ):Word W) := val 2
    rw [pointer]
    change ((B.oldAux+(1+B.capacity):ℕ):Word W).val=_
    rw [←Nat.add_assoc,Fin.val_cast_of_lt room0]
  · rw [show x.filled .evaluate out (B.bounds+3)=TickActiveROM.boundsMemory B clock out (B.bounds+3) from
      fill_frame _ _ _ _ _ (.inl (by omega))]
    have pointer : TickActiveROM.boundsMemory B clock out (B.bounds+3) =
        ((B.oldAux+(1+B.capacity)+x.count:ℕ):Word W) := val 3
    rw [pointer]
    change ((B.oldAux+(1+B.capacity)+x.count:ℕ):Word W).val=_
    rw [←Nat.add_assoc B.oldAux,Fin.val_cast_of_lt room1]


/-- Actual published memory, followed by the selected node's preceding
writes off S2 and S5, satisfies the leaf endpoint scanner's full mount. -/
theorem pairMount {F : Type*} [Field F] [Fintype F] {p H J : ℕ}
    {fit : RAM.Contraction.Fits (TickWeightedBank.shape F p H J) W} {clock : TickChronology.Clock}
    (a : RootArchive) (aux teams cap q nt ns np : ℕ)
    (x : TickActiveROM.CellInput (TickPhysicalABI.mounted a.age aux teams cap q nt ns np) clock fit)
    (N : Nodes a) (slots : ℕ) (ls : List Layers) (m prepared src : Memory W)
    (groups : Fin a.initialLanes→Fin a.groups) (cur : Fin a.groups) (i : Fin a.initialLanes)
    (low : ℕ) (span : a.pairsPerLane=2^low) (groupsEq : a.groups=clock.groups)
    (groupSize : BucketRows.count groups (List.ofFn a.lane) cur=x.count)
    (output : a.preparedInput x N slots ls m groups prepared) (room : OutputRoom a W)
    (clockFits : base a.age 1<2^W) (clockLow : base a.age 1<a.protectedBelow)
    (clockAt : m (base a.age 1)=(cur.val:Word W))
    (rowHigh : base a.age 3+8*aux≤base a.age 5)
    (boundsHigh : base a.age 2+4≤base a.age 5) (boundsLow : base a.age 2+4≤base a.age 3)
    (boundsFit : base a.age 2+4≤2^W)
    (auxFit : (TickPhysicalABI.mounted a.age aux teams cap q nt ns np).oldAux+aux<2^W)
    (A : HistoryInitialSeed.Layout) (z : HistoryInitialSeed.Site)
    (interval : A.intervals=base a.age 5) (bounds : A.bounds=base a.age 2)
    (laneId : z.lane=i.val) (selected : z.stage=0 → groups i=cur)
    (ext : z.extPins=(if z.stage=0 then 2*TraceSuffix.pairs a.totalPairs low z.lane else 0))
    (frame : src (A.intervals+4*z.lane+3)=prepared (A.intervals+4*z.lane+3) ∧
      src (A.bounds+2)=prepared (A.bounds+2) ∧ src (A.bounds+3)=prepared (A.bounds+3))
    (keepRows : HistoryInitialSeed.Protected A z (A.intervals+4*z.lane) 4)
    (keepBounds : HistoryInitialSeed.Protected A z A.bounds 4)
    (rowFits : A.intervals+4*z.lane+3<2^W) :
    HistoryInitialSeed.PairMount (aux:=aux) (cap:=cap) (packedCount:=x.count) q nt ns np a.age teams
      a.totalPairs low (a.packedStart groups i) A z src := by
  obtain ⟨b,o,branch,done,rfl⟩:=output
  have getClock := (a.read_low N slots ls groups m b o branch done room.current _ clockLow).trans clockAt
  have roomGroups:=room.countersEnd
  have curFit : cur.val<2^W := by have:=cur.isLt;omega
  have sel:=a.output_selected groups b o done room (base a.age 1) cur.val clockFits curFit getClock
  rw [dite_eq_left cur.isLt,groupSize] at sel
  have rs:=a.pair_words x groups i low span room.pairCount _ o done (by
    change TickPairHeader.selected o (base a.age 1 : Word W) (base a.age 8 : Word W)
      (clock.groups : Word W) = (x.count : Word W)
    simpa only [groupsEq] using sel)
    rowHigh boundsHigh boundsLow boundsFit auxFit
  refine ⟨ext,?_,?_,?_,?_,keepRows,keepBounds,rowFits,by omega⟩
  · rw [frame.1,interval,laneId];exact rs.1
  · intro h
    have offset:=a.packed_slice groups i
    rw [a.lane_pairs i low span,selected h,groupSize] at offset
    simpa [laneId] using offset
  · rw [frame.2.1,bounds];exact rs.2.1
  · rw [frame.2.2,bounds];exact rs.2.2


end ThreeFlat.Diagonal.NavigationPass.RootArchive

end OAI
