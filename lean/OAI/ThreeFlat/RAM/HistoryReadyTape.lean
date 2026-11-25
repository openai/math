import OAI.ThreeFlat.RAM.HistoryCommandLink
import OAI.ThreeFlat.RAM.PhysicalProcedure

namespace OAI
/-! # Executing a regular list of native seven-word rows from memory -/

namespace ThreeFlat.RAM.HistoryReadyTape

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr DescriptorScan PhysicalProcedure HistoryJoinController
open scoped Fin.CommRing

structure Job (w : ℕ) where
  start : ℕ
  count : ℕ
  word : ℕ → Word w

variable {w k : ℕ} {α : Type*}

def Job.finish (x : Job w) := x.start+x.count

def after (ctrl : Word w) : List (Job w) → Memory w → Memory w
  | [],m => m
  | x::xs,m => after ctrl xs (bumpMemory ctrl (fillSegment x.start x.count x.word m))

def cost (binds : ℕ) : List (Job w) → ℕ
  | [] => 6
  | x::xs => 19+x.count*(2*binds+4)+cost binds xs

/-- The two tape-bound columns are determined by genuine generated output
sizes. All seven control fields can coexist with the other operands in the
same immutable interval while the operations write the disjoint outputs. -/
def Loaded (base : ℕ) (jobs : List (Job w)) (m : Memory w) :=
  ∀ (j : Fin jobs.length), m (base+7*j.val+1)=(jobs.get j).start ∧
    m (base+7*j.val+6)=(jobs.get j).finish

def Away (a span : ℕ) (jobs : List (Job w)) :=
  ∀ j ∈ jobs, j.finish≤a ∨ a+span≤j.start

def readJobs (e : Term w k 1) (pub : Fin k→Word w) (ctrl : Word w) :
    List (Job w) → Memory w → Prop
  | [],_ => True
  | x::xs,m => (∀ a : Word w, ∀ mem : Memory w, x.start≤a.val → a.val<x.finish →
      agreesOutside x.start x.finish mem m → e.eval pub mem (fun _ => a)=x.word a.val) ∧
      readJobs e pub ctrl xs (bumpMemory ctrl (fillSegment x.start x.count x.word m))

theorem after_append (ctrl : Word w) (xs ys : List (Job w)) (m : Memory w) :
    after ctrl (xs++ys) m=after ctrl ys (after ctrl xs m) := by
  induction xs generalizing m with
  | nil => rfl
  | cons x xs ih => exact ih _

theorem read_append (e : Term w k 1) (pub : Fin k→Word w) (ctrl : Word w)
    (xs ys : List (Job w)) (m : Memory w) :
    readJobs e pub ctrl (xs++ys) m ↔ readJobs e pub ctrl xs m ∧ readJobs e pub ctrl ys (after ctrl xs m) := by
  induction xs generalizing m with
  | nil => simp [readJobs,after]
  | cons x xs ih => simp only [List.cons_append,readJobs,after,ih,and_assoc]

/-- One actual operand header and copy interval per child. The invariant
at child i describes precisely the scratch image returned by its prefix. -/
theorem read_children (e : Term w k 1) (pub : Fin k→Word w) (ctrl : Word w)
    (children : List α) (ops : α→List (Job w)) (m : Memory w)
    (valid : ∀ before x rest,children=before++x::rest →
      readJobs e pub ctrl (ops x) (after ctrl (before.flatMap ops) m)) :
    readJobs e pub ctrl (children.flatMap ops) m := by
  induction children generalizing m with
  | nil => trivial
  | cons x xs ih =>
    rw [List.flatMap_cons,read_append]
    refine ⟨valid [] x xs rfl,?_⟩
    apply ih
    intro before y rest e
    have h := valid (x::before) y rest (by simp [e])
    simpa [after_append] using h

theorem after_away (ctrl : Word w) (xs : List (Job w)) (m : Memory w) (a : ℕ)
    (different : a≠ctrl.val) (outside : ∀ x∈xs,a<x.start ∨ x.finish≤a) : after ctrl xs m a=m a := by
  induction xs generalizing m with
  | nil => rfl
  | cons x xs ih =>
    rw [after,ih _ (fun y h => outside _ (List.mem_cons_of_mem _ h))]
    have h := outside x (List.mem_cons_self ..)
    simp [bumpMemory,writeMemory,different,fillSegment,show ¬(x.start≤a ∧ a<x.start+x.count) by
      change ¬(x.start≤a ∧ a<x.finish);omega]


theorem pass (e : Term w k 1) (pub : Fin k→Word w) (ctrl : Word w)
    (base : ℕ) (jobs : List (Job w)) (m : Memory w)
    (earlier : ctrl.val+2≤base)
    (room : base+7*jobs.length<2^w)
    (cursor : m ctrl.val=(base : Word w))
    (stop : m (ctrl+1).val=((base+7*jobs.length : ℕ) : Word w))
    (loaded : Loaded base jobs m)
    (apart : Away ctrl.val 2 jobs)
    (safe : Away base (7*jobs.length) jobs)
    (fits : ∀ j∈jobs,j.finish<2^w)
    (reads : readJobs e pub ctrl jobs m) :
    HistoryCommandSweep.Pass e pub ctrl m (after ctrl jobs m) (cost e.binds jobs) := by
  induction jobs generalizing base m with
  | nil =>
    apply HistoryCommandSweep.Pass.done
    rw [cursor,stop]; simp
  | cons x xs ih =>
    let mem := fillSegment x.start x.count x.word m
    let next := bumpMemory ctrl mem
    have size : (x::xs).length=xs.length+1 := rfl
    have endpoint : base+7*(x::xs).length=(base+7)+7*xs.length := by rw [size]; omega
    have b : base<2^w := by omega
    have nb : base+7<2^w := by rw [endpoint] at room; omega
    have ctrlFit : ctrl.val+1<2^w := by omega
    have val1 : (ctrl+1).val=ctrl.val+1 := by
      simp [Fin.val_add,Nat.mod_eq_of_lt ctrlFit,Nat.mod_eq_of_lt (show 1<2^w by omega)]
    have ctrlOut : ∀ z, ctrl.val≤z → z<ctrl.val+2 → mem z=m z := by
      intro z lo hi
      have h := apart x (List.mem_cons_self ..)
      simp only [mem,fillSegment]
      rw [ite_eq_right (by change ¬(x.start≤z ∧ z<x.finish); omega)]
    have bankOut : ∀ z,base≤z → z<base+7*(x::xs).length → next z=m z := by
      intro z lo hi
      have h := safe x (List.mem_cons_self ..)
      have ne : z≠ctrl.val := by omega
      change writeMemory mem ctrl (mem ctrl.val+7) z=m z
      simp [writeMemory,ne,mem,fillSegment,
        show ¬(x.start≤z ∧ z<x.start+x.count) by change ¬(x.start≤z ∧ z<x.finish); omega]
    have nextC : next ctrl.val=((base+7 : ℕ) : Word w) := by
      simp [next,bumpMemory,writeMemory,ctrlOut _ le_rfl (by omega),cursor]
    have nextS : next (ctrl+1).val=(((base+7)+7*xs.length : ℕ) : Word w) := by
      have ne : (ctrl+1).val≠ctrl.val := by omega
      simp only [next,bumpMemory,writeMemory,ite_eq_right ne]
      rw [ctrlOut (ctrl+1).val (by omega) (by omega),←endpoint]
      exact stop
    have vals := loaded (0 : Fin (x::xs).length)
    have low : m (base+1)=(x.start : Word w) := by simpa using vals.1
    have high : m (base+6)=(x.finish : Word w) := by simpa using vals.2
    have xf := fits x (List.mem_cons_self ..)
    have xlo : x.start<2^w := by unfold Job.finish at xf; omega
    have low' : (m (m ctrl.val+1).val).val=x.start := by
      rw [cursor]
      rw [←Nat.cast_one (R:=Word w),←Nat.cast_add,Fin.val_cast_of_lt (by omega),low,Fin.val_cast_of_lt xlo]
    have high' : (m (m ctrl.val+6).val).val=x.finish := by
      rw [cursor]
      rw [show (6:Word w)=((6:ℕ):Word w) by norm_num,←Nat.cast_add,Fin.val_cast_of_lt (by omega),
          high,Fin.val_cast_of_lt xf]
    apply HistoryCommandSweep.Pass.next (count:=x.count) (start:=x.start) (finish:=x.finish)
      (word:=x.word)
    · rw [cursor,stop]
      change (((base:Word w)).val)<_
      rw [Fin.val_cast_of_lt b,Fin.val_cast_of_lt room,endpoint]; omega
    · exact low'
    · exact high'
    · rfl
    · exact reads.1
    · apply ih (base+7) next (by omega) (endpoint ▸ room) nextC nextS
      · intro j
        have v := loaded j.succ
        have one : base+7*j.succ.val+1=(base+7)+7*j.val+1 := by simp [Nat.mul_add]; omega
        have six : base+7*j.succ.val+6=(base+7)+7*j.val+6 := by simp [Nat.mul_add]; omega
        have bound := j.isLt
        rw [bankOut _ (by omega) (by rw [endpoint]; omega),bankOut _ (by omega) (by rw [endpoint]; omega)]
        rw [one,six] at v
        simpa only [List.get_cons_succ'] using v
      · intro y hy; exact apart y (List.mem_cons_of_mem _ hy)
      · intro y hy
        have h := safe y (List.mem_cons_of_mem _ hy)
        rw [endpoint] at h
        omega
      · intro y hy; exact fits y (List.mem_cons_of_mem _ hy)
      · exact reads.2

def execute (e : Term w k 1) (base : Fin k) (data : Fin k→Word w) : Procedure w :=
  ⟨18+(e.labels+6),4+e.binds,k,HistoryCommandSweep.block e base,data⟩

theorem execute_spec (e : Term w k 1) (base : Fin k) (data : Fin k→Word w)
    (pre : Memory w→Prop) (jobs : List (Job w)) (start : ℕ)
    (earlier : (data base).val+2≤ start) (room : start+7*jobs.length<2^w)
    (away : Away (data base).val 2 jobs) (frame : Away start (7*jobs.length) jobs)
    (fits : ∀ j∈jobs,j.finish<2^w)
    (state : ∀ m,pre m → m (data base).val=(start : Word w) ∧
      m (data base+1).val=((start+7*jobs.length : ℕ) : Word w) ∧ Loaded start jobs m ∧
      readJobs e data (data base) jobs m) :
    (execute e base data).Spec pre (fun m z => z=after (data base) jobs m) (cost e.binds jobs) := by
  intro P R K M pc reg pub exit installed publicValues c m initial hm
  obtain ⟨cur,endWord,stored,reads⟩ := state m hm
  have drive := pass e data (data base) start jobs m earlier room cur endWord stored away frame fits reads
  have same : (fun i : Fin k=>M.publicData (pub i))=data := funext publicValues
  have baseValue : M.publicData (pub base)=data base := publicValues base
  have useTape : HistoryCommandSweep.Pass e (M.publicData∘pub) (M.publicData (pub base)) m
      (after (data base) jobs m) (cost e.binds jobs) := by
    change HistoryCommandSweep.Pass e (fun i : Fin k=>M.publicData (pub i)) _ _ _ _
    rw [same,baseValue]
    exact drive
  obtain ⟨t,ht,z,hz,run⟩ :=
    HistoryCommandSweep.advance_block e base M pc reg pub exit installed useTape c initial
  exact ⟨t,ht,z,_,run,hz,rfl⟩

end ThreeFlat.RAM.HistoryReadyTape

end OAI
