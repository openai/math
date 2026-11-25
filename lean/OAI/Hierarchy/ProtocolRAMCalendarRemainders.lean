import OAI.Hierarchy.ProtocolRAMCalendarSegments
import OAI.Hierarchy.ProtocolRAMCalendarArena

namespace OAI
/-! # Ordinals and authentic execution remainders of every scheduled event -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section
variable {w q d : ℕ}

/-- Enumerate all outer acquisitions once in the order the calendar actually
executes them. Empty phase or trial ranges need no exceptional dummy row. -/
def outerDates (c : Mesh) : Fin ((c.inject+c.cool)*c.outerFuel)≃Fin (c.inject+c.cool)×Fin c.outerFuel :=
  finProdFinEquiv.symm

theorem outer_index (c : Mesh) (p : Fin (c.inject+c.cool)) (h : Fin c.outerFuel) :
    ((outerDates c).symm (p,h)).val=p.val*c.outerFuel+h.val := by
  change h.val+c.outerFuel*p.val=_
  ac_rfl

theorem outer_date_position (c : Mesh) (i : Fin ((c.inject+c.cool)*c.outerFuel)) :
    position c (.attempt (.outer ((outerDates c i).1.val) ((outerDates c i).2.val)))=i.val*trialSize c+(outerDates c i).1.val := by
  obtain ⟨⟨p,h⟩,rfl⟩:=(outerDates c).symm.surjective i
  simp only [Equiv.apply_symm_apply,outer_index,position,trialBase,phaseSize]
  ring

theorem outer_date_strict (c : Mesh) : StrictMono (fun i : Fin ((c.inject+c.cool)*c.outerFuel) =>
    position c (.attempt (.outer (outerDates c i).1.val (outerDates c i).2.val))) := by
  intro i j lt
  change position c (.attempt (.outer (outerDates c i).1.val (outerDates c i).2.val)) <
    position c (.attempt (.outer (outerDates c j).1.val (outerDates c j).2.val))
  rw [outer_date_position c i,outer_date_position c j]
  have phase : (outerDates c i).1.val≤(outerDates c j).1.val := Nat.div_le_div_right (c:=c.outerFuel) lt.le
  have step := Nat.mul_lt_mul_of_pos_right lt (show 0<trialSize c by unfold trialSize;omega)
  omega

/-- A cut is certified against one concrete execution, with the state at entry
and the still-to-run suffix both indexed by the fixed chronological event. -/
structure Slot (C : Chart w q d) (mem : Memory w) (e : Event) (prior tail : List Event) (current : Memory w) : Prop where
  events : Calendar.events C.mesh=prior++e::tail
  entry : run C prior mem=current
  prefixReady : mounted C prior mem
  currentReady : ready C e current
  tailReady : mounted C tail (after C e current)
  finish : run C (Calendar.events C.mesh) mem=run C tail (after C e current)
  earlier : ∀a∈prior,position C.mesh a<position C.mesh e
  later : ∀a∈tail,position C.mesh e<position C.mesh a

theorem slot_of_split (C : Chart w q d) (mem : Memory w) (e : Event) (prior tail : List Event) (current : Memory w)
    (split : events C.mesh=prior++e::tail) (entry : run C prior mem=current) (whole : mounted C (events C.mesh) mem) :
    Slot C mem e prior tail current := by
  have schedule:=whole
  rw [split,mounted_append,entry] at schedule
  have ordered : ((events C.mesh).map (position C.mesh)).Pairwise (·<·) := by rw [positions];exact List.pairwise_lt_range
  rw [split,List.map_append,List.map_cons] at ordered
  obtain ⟨_,following,cross⟩:=List.pairwise_append.mp ordered
  exact ⟨split,entry,schedule.1,schedule.2.1,schedule.2.2,by rw [split,run_append,entry];rfl,
    fun a ha=>cross _ (List.mem_map_of_mem ha) _ (List.mem_cons_self ..),
    fun a ha=>(List.pairwise_cons.mp following).1 _ (List.mem_map_of_mem ha)⟩

/-- This covers both kinds of feeds as well as outer and inner attempts. -/
theorem ordinal_slot (C : Chart w q d) (mem : Memory w) (u : Fin (events C.mesh).length)
    (whole : mounted C (events C.mesh) mem) :
    let ls:=events C.mesh
    Slot C mem ls[u.val] (ls.take u.val) (ls.drop (u.val+1)) (run C (ls.take u.val) mem) := by
  intro ls
  apply slot_of_split C mem _ _ _ _ _ rfl whole
  calc ls=(ls.take u.val)++ls.drop u.val := (List.take_append_drop ..).symm
       _=_ := by rw [List.drop_eq_getElem_cons u.isLt]

private theorem split_blocks {α : Type*} (f : ℕ→List α) {i n : ℕ} (inside : i<n) :
    ∃suffix,(List.range n).flatMap f=(List.range i).flatMap f++f i++suffix := by
  let later:=(List.range (n-(i+1))).map ((i+1)+·)
  refine ⟨later.flatMap f,?_⟩
  have split : List.range n=List.range (i+1)++later := by
    calc List.range n=List.range ((i+1)+(n-(i+1))) := by rw [Nat.add_sub_of_le inside]
         _=_ := List.range_add
  rw [split,List.flatMap_append,List.range_succ,List.flatMap_append]
  simp

def outerPrefix (c : Mesh) (p h : ℕ) :=
  (List.range p).flatMap (outerBlock c)++(List.range h).flatMap (trialBlock c p)

theorem outer_slot (C : Chart w q d) (mem : Memory w) (p h : ℕ)
    (phase : p<C.mesh.inject+C.mesh.cool) (trial : h<C.mesh.outerFuel) (all : mounted C (events C.mesh) mem) :
    ∃tail,Slot C mem (.attempt (.outer p h)) (outerPrefix C.mesh p h) tail (trialState C mem p h) := by
  let c:=C.mesh
  obtain ⟨later,phases⟩:=split_blocks (outerBlock c) phase
  obtain ⟨trials,heads⟩:=split_blocks (trialBlock c p) trial
  let tail:=(List.range c.reserveSteps).flatMap (reserveBlock c p h)++trials++[.feed (.outer p)]++later
  refine ⟨tail,slot_of_split C mem _ _ tail _ ?_ (run_append C _ _ mem) all⟩
  change (List.range (c.inject+c.cool)).flatMap (outerBlock c)=_
  rw [phases,outerBlock,heads]
  simp [trialBlock,outerPrefix,tail,List.append_assoc,c]

theorem outer_remainder (C : Chart w q d) (mem : Memory w) (p h : ℕ)
    (phase : p<C.mesh.inject+C.mesh.cool) (trial : h<C.mesh.outerFuel) (mountedAll : mounted C (events C.mesh) mem) :
    let a:=Event.attempt (.outer p h)
    let first:=after C a (trialState C mem p h)
    ∃tail,run C (events C.mesh) mem=run C tail first ∧ mounted C tail first ∧
      ∀e∈tail,position C.mesh a<position C.mesh e := by
  obtain ⟨tail,cut⟩:=outer_slot C mem p h phase trial mountedAll
  exact ⟨tail,cut.finish,cut.tailReady,cut.later⟩

def innerPrefix (c : Mesh) (p h j b : ℕ) :=
  ((outerPrefix c p h++[.attempt (.outer p h)])++(List.range j).flatMap (reserveBlock c p h))++
    (List.range b).map (fun i=>.attempt (.inner p h j i))

private theorem split_map {α : Type*} (f : ℕ→α) {i n : ℕ} (inside : i<n) :
    ∃tail,(List.range n).map f=(List.range i).map f++f i::tail := by
  let later:=(List.range (n-(i+1))).map ((i+1)+·)
  refine ⟨later.map f,?_⟩
  have split : List.range n=List.range (i+1)++later := by
    calc List.range n=List.range ((i+1)+(n-(i+1))) := by rw [Nat.add_sub_of_le inside]
         _=_ := List.range_add
  rw [split,List.map_append,List.range_succ,List.map_append]
  simp [List.append_assoc]

/-- Each inner histogram has its genuine preceding trial/repair state,
including every preceding reserve slice and earlier gated inner operation. -/
theorem inner_slot (C : Chart w q d) (mem : Memory w) (p h j b : ℕ)
    (phase : p<C.mesh.inject+C.mesh.cool) (trial : h<C.mesh.outerFuel) (slice : j<C.mesh.reserveSteps)
    (inner : b<C.mesh.innerFuel) (all : mounted C (events C.mesh) mem) :
    ∃tail,Slot C mem (.attempt (.inner p h j b)) (innerPrefix C.mesh p h j b) tail (innerState C mem p h j b) := by
  let c:=C.mesh
  obtain ⟨later,phases⟩:=split_blocks (outerBlock c) phase
  obtain ⟨trials,heads⟩:=split_blocks (trialBlock c p) trial
  obtain ⟨reserves,parts⟩:=split_blocks (reserveBlock c p h) slice
  obtain ⟨inners,items⟩:=split_map (fun n=>Event.attempt (.inner p h j n)) inner
  let tail:=inners++[Event.feed (.inner p h j)]++reserves++trials++[Event.feed (.outer p)]++later
  refine ⟨tail,slot_of_split C mem _ _ tail _ ?_ ?_ all⟩
  · change (List.range (c.inject+c.cool)).flatMap (outerBlock c)=_
    rw [phases,outerBlock,heads,trialBlock,parts,reserveBlock,items]
    simp [innerPrefix,outerPrefix,tail,List.append_assoc,c]
  · have outer : run C (outerPrefix c p h) mem=trialState C mem p h := run_append C _ _ mem
    rw [innerPrefix,run_append,run_append,run_append,outer]
    rfl

theorem inner_remainder (C : Chart w q d) (mem : Memory w) (p h j b : ℕ)
    (phase : p<C.mesh.inject+C.mesh.cool) (trial : h<C.mesh.outerFuel) (slice : j<C.mesh.reserveSteps)
    (inner : b<C.mesh.innerFuel) (mountedAll : mounted C (events C.mesh) mem) :
    let a:=Event.attempt (.inner p h j b)
    let first:=after C a (innerState C mem p h j b)
    ∃tail,run C (events C.mesh) mem=run C tail first ∧ mounted C tail first ∧
      ∀e∈tail,position C.mesh a<position C.mesh e := by
  obtain ⟨tail,cut⟩:=inner_slot C mem p h j b phase trial slice inner mountedAll
  exact ⟨tail,cut.finish,cut.tailReady,cut.later⟩

theorem outer_feed_slot (C : Chart w q d) (mem : Memory w) (p : ℕ)
    (phase : p<C.mesh.inject+C.mesh.cool) (all : mounted C (events C.mesh) mem) :
    ∃tail,Slot C mem (.feed (.outer p)) (outerPrefix C.mesh p C.mesh.outerFuel) tail
      (trialState C mem p C.mesh.outerFuel) := by
  let c:=C.mesh
  obtain ⟨tail,split⟩:=split_blocks (outerBlock c) phase
  refine ⟨tail,slot_of_split C mem _ _ _ _ ?_ (run_append C _ _ mem) all⟩
  change (List.range (c.inject+c.cool)).flatMap (outerBlock c)=_
  rw [split,outerBlock]
  simp [outerPrefix,List.append_assoc,c]

theorem inner_feed_slot (C : Chart w q d) (mem : Memory w) (p h j : ℕ)
    (phase : p<C.mesh.inject+C.mesh.cool) (trial : h<C.mesh.outerFuel) (slice : j<C.mesh.reserveSteps)
    (all : mounted C (events C.mesh) mem) :
    ∃tail,Slot C mem (.feed (.inner p h j)) (innerPrefix C.mesh p h j C.mesh.innerFuel) tail
      (innerState C mem p h j C.mesh.innerFuel) := by
  let c:=C.mesh
  obtain ⟨later,phases⟩:=split_blocks (outerBlock c) phase
  obtain ⟨trials,heads⟩:=split_blocks (trialBlock c p) trial
  obtain ⟨reserves,parts⟩:=split_blocks (reserveBlock c p h) slice
  let tail:=reserves++trials++[Event.feed (.outer p)]++later
  refine ⟨tail,slot_of_split C mem _ _ tail _ ?_ ?_ all⟩
  · change (List.range (c.inject+c.cool)).flatMap (outerBlock c)=_
    rw [phases,outerBlock,heads,trialBlock,parts,reserveBlock]
    simp [innerPrefix,outerPrefix,tail,List.append_assoc,c]
  · have outer : run C (outerPrefix c p h) mem=trialState C mem p h := run_append C _ _ mem
    rw [innerPrefix,run_append,run_append,run_append,outer]
    rfl

theorem Slot.ordinal {C : Chart w q d} {mem current : Memory w} {e : Event} {prior tail : List Event}
    (cut : Slot C mem e prior tail current) : position C.mesh e=prior.length := by
  have small : prior.length<(Calendar.events C.mesh).length := by rw [cut.events,List.length_append,List.length_cons];omega
  have val:=congrArg (fun ns : List ℕ=>ns[prior.length]?) (positions C.mesh)
  change ((Calendar.events C.mesh).map (position C.mesh))[prior.length]?=(List.range (Calendar.events C.mesh).length)[prior.length]? at val
  rw [List.getElem?_range small,cut.events,List.map_append,List.map_cons,List.getElem?_append_right (by simp)] at val
  simpa only [List.length_map,Nat.sub_self,List.getElem?_cons_zero,Option.some.injEq] using val

theorem Slot.native {C : Chart w q d} {mem current : Memory w} {e : Event} {prior tail : List Event}
    (cut : Slot C mem e prior tail current) :
    (code C prior).Exec mem current (cost C prior) ∧ (step C e).Exec current (after C e current) (ticks C e) ∧
      (code C tail).Exec (after C e current) (run C (Calendar.events C.mesh) mem) (cost C tail) := by
  refine ⟨cut.entry ▸ run_exec C prior mem cut.prefixReady,step_exec C e current cut.currentReady,?_⟩
  rw [cut.finish]
  exact run_exec C tail _ cut.tailReady

theorem Slot.word {C : Chart w q d} {mem current : Memory w} {e : Event} {prior tail : List Event}
    (cut : Slot C mem e prior tail current) (x : ℕ) (safe : ∀t∈tail,protected C x t) :
    run C (Calendar.events C.mesh) mem x=after C e current x :=
  (congrFun cut.finish x).trans (run_frame C tail _ x cut.tailReady safe)

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
