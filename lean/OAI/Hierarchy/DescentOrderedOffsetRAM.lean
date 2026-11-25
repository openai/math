import OAI.ThreeFlat.RAM.OrdinalOpLoop
import OAI.ThreeFlat.RAM.PhysicalExactRun
import OAI.Hierarchy.DescentSparseWordOrder

namespace OAI
/-! # A native scatter of every sparse packet's starting bit address -/

namespace Hierarchy.DescentOrderedWords.OffsetRAM
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators
variable {w n sites : ℕ}

def ops : List (Op 8 4) :=
  [.publicWord 2 0, .binary .add 2 2 0, .binary .add 2 2 0, .read 3 2,
   .publicWord 4 1, .binary .add 4 4 3, .read 5 4, .publicWord 6 2,
   .binary .add 6 6 0, .write 6 5, .constant 7 1, .binary .add 2 2 7,
   .read 3 2, .binary .add 5 5 3, .write 4 5, .binary .add 0 0 7]

def params (w src bins out n : ℕ) : Fin 4 → Word w := ![src,bins,out,n]

def program (w src bins out n : ℕ) : Procedure w :=
  ⟨19,8,4,OrdinalOpLoop.block w ops 0 1 3,params w src bins out n⟩

variable (tag : Fin n→Fin sites) (size : Fin n→ℕ) (bins out : ℕ) (m : Memory w)

def image : ℕ→Memory w
  | 0 => m
  | t+1 =>
    let prev := image t
    if hi : t<n then
      let i : Fin n := ⟨t,hi⟩
      let c := bins+(tag i).val
      fun a=>if a=c then prev c+(size i:Word w) else if a=out+t then prev c else prev a
    else prev

private theorem image_step (i : Fin n) (a : ℕ) :
    image tag size bins out m (i.val+1) a =
      let prev := image tag size bins out m i.val
      let c := bins+(tag i).val
      if a=c then prev c+(size i : Word w) else if a=out+i.val then prev c else prev a := by
  simp only [image, dite_eq_left i.isLt]

theorem frame (t a : ℕ) (left : a<bins) (away : a<out) : image tag size bins out m t a=m a := by
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases ht : t<n
    · have ne : a≠bins+(tag ⟨t,ht⟩).val := by omega
      have no : a≠out+t := by omega
      simpa only [image,dite_eq_left ht,ite_eq_right ne,ite_eq_right no] using ih
    · simpa [image,ht] using ih

def totalBefore (c : Fin sites) (t : ℕ) := ∑i : Fin n,if i.val<t ∧ tag i=c then size i else 0

private theorem nextTotal (c : Fin sites) (i : Fin n) :
    totalBefore tag size c (i.val+1)=totalBefore tag size c i.val+if tag i=c then size i else 0 := by
  have split (j : Fin n) :
      (if j.val < i.val+1 ∧ tag j=c then size j else 0)=
      (if j.val < i.val ∧ tag j=c then size j else 0)+(if j=i then (if tag i=c then size i else 0) else 0) := by
    by_cases eq : j=i
    · subst j;simp
    · have neq : j.val≠i.val := fun h=>eq (Fin.ext h)
      have same : j.val < i.val+1 ↔ j.val < i.val := by omega
      simp [eq,same]
  unfold totalBefore
  simp_rw [split]
  rw [Finset.sum_add_distrib]
  simp

theorem counter (separate : bins+sites≤out) (c : Fin sites) (t : ℕ) (live : t≤n) :
    image tag size bins out m t (bins+c.val)=m (bins+c.val)+(totalBefore tag size c t : Word w) := by
  induction t with
  | zero => simp [image,totalBefore]
  | succ t ih =>
    have ht : t<n := by omega
    let i : Fin n := ⟨t,ht⟩
    have later : bins+c.val≠out+t := by have := c.isLt;omega
    have step := nextTotal tag size c i
    change totalBefore tag size c (t+1)=_ at step
    rw [image_step tag size bins out m i, step]
    dsimp only
    by_cases yes : tag i=c
    · have eqn : bins+c.val=bins+(tag i).val := by rw [yes]
      rw [ite_eq_left eqn, ite_eq_left yes, ←eqn, Nat.cast_add, ih (by omega), add_assoc]
    · have ne : bins+c.val≠bins+(tag i).val := fun eq=>yes (Fin.ext (by omega))
      rw [ite_eq_right ne, ite_eq_right later, ite_eq_right yes, Nat.add_zero]
      exact ih (by omega)

theorem read_row (separate : bins+sites≤out) (i : Fin n) (t : ℕ) (after : i.val<t) (live : t≤n) :
    image tag size bins out m t (out+i.val)=m (bins+(tag i).val)+(totalBefore tag size (tag i) i.val : Word w) := by
  induction t with
  | zero => omega
  | succ t ih =>
    have ht : t<n := by omega
    let j : Fin n := ⟨t,ht⟩
    have away : out+i.val≠bins+(tag j).val := by have := (tag j).isLt;omega
    rw [image_step tag size bins out m j]
    dsimp only
    rw [ite_eq_right away]
    by_cases now : i.val=t
    · rw [ite_eq_left (congrArg (out+·) now)]
      obtain rfl : i=j := Fin.ext now
      exact counter tag size bins out m separate (tag j) t (by omega)
    · have past : i.val<t := by omega
      have ne : out+i.val≠out+t := by omega
      rw [ite_eq_right ne]
      exact ih past (by omega)

set_option maxRecDepth 12288 in
private theorem traceRow {r k : ℕ} (reg : Fin 8 ↪ Fin r) (pub : Fin 4→Fin k)
    (bank : Fin k→Word w) (state : Word w) (rs : Regs w r) (mem : Memory w) :
    let i := rs (reg 0)
    let p := bank (pub 0)+i+i
    let c := bank (pub 1)+mem p.val
    let dst := bank (pub 2)+i
    let half := writeMemory mem dst (mem c.val)
    ∃ es z, trace bank state (ops.map (OrdinalOpLoop.relocate reg pub)) rs mem=
      some (es,z,writeMemory half c (mem c.val+half (p+1).val)) ∧ z (reg 0)=i+1 ∧ z (reg 1)=rs (reg 1) := by
  simp [ops,OrdinalOpLoop.relocate,trace,Op.effect,BinaryOp.eval,Function.update,reg.injective.eq_iff]

theorem run (src : ℕ) (sourceFits : src+2*n≤bins) (separate : bins+sites≤out) (fit : out+n≤2^w)
    (loaded : ∀i, m (src+2*i.val)=((tag i).val:Word w) ∧ m (src+2*i.val+1)=(size i:Word w)) :
    (program w src bins out n).Exec m (image tag size bins out m n) (3+17*n) := by
  intro pcs regs pubs M pc reg pub exit rom data cfg mem entry hm
  subst mem
  change Fin 8 ↪ Fin regs at reg
  change Fin 4 → Fin pubs at pub
  change ∀i,M.publicData (pub i)=params w src bins out n i at data
  obtain ⟨z,advance,stop⟩ := OrdinalOpLoop.advance_block ops 0 1 (by decide) 3 M pc reg pub exit rom n
    (by have := Nat.two_pow_pos w;omega) (data 3) (image tag size bins out m) (by
      intro t ht state rs cur limit
      let i : Fin n := ⟨t,ht⟩
      let prior := image tag size bins out m t
      obtain ⟨events,z,actual,inc,keep⟩ := traceRow reg pub M.publicData state rs prior
      refine ⟨events,z,?_,by simpa [cur] using inc,keep.trans limit⟩
      rw [data 0,data 1,data 2,cur] at actual
      let p := (src:Word w)+(t:Word w)+(t:Word w)
      have pos : p=((src+2*t:ℕ):Word w) := by dsimp [p];rw [←Nat.cast_add,←Nat.cast_add];congr 1;omega
      have pval : p.val=src+2*t := by rw [pos,Fin.val_cast_of_lt (by omega)]
      have qval : (p+1).val=src+2*t+1 := by rw [pos,←Nat.cast_one (R:=Word w),←Nat.cast_add,Fin.val_cast_of_lt (by omega)]
      have key : prior p.val=((tag i).val:Word w) := by
        rw [pval]
        exact (frame tag size bins out m t (src+2*t) (by omega) (by omega)).trans (loaded i).1
      have width : prior (p+1).val=(size i:Word w) := by
        rw [qval]
        exact (frame tag size bins out m t (src+2*t+1) (by omega) (by omega)).trans (loaded i).2
      have binFits : bins+(tag i).val<2^w := by have := (tag i).isLt;omega
      have outFits : out+t<2^w := by omega
      have different : src+2*t+1≠out+t := by omega
      let c := ((bins+(tag i).val:ℕ):Word w)
      let dst := ((out+t:ℕ):Word w)
      have cval : c.val=bins+(tag i).val := Fin.val_cast_of_lt binFits
      have dval : dst.val=out+t := Fin.val_cast_of_lt outFits
      change trace _ _ _ _ _=some (_,_,writeMemory (writeMemory prior ((out:Word w)+(t:Word w)) (prior (((bins:Word w)+prior p.val).val)))
        ((bins:Word w)+prior p.val) (prior (((bins:Word w)+prior p.val).val)+writeMemory prior ((out:Word w)+(t:Word w))
          (prior (((bins:Word w)+prior p.val).val)) (p+1).val)) at actual
      rw [key,←Nat.cast_add,←Nat.cast_add] at actual
      have half : writeMemory prior dst (prior c.val) (p+1).val=(size i:Word w) := by
        simpa only [writeMemory,qval,dval,ite_eq_right different] using width
      have updateMem : writeMemory (writeMemory prior dst (prior c.val)) c (prior c.val+(size i:Word w))=
          image tag size bins out m (t+1) := by
        funext a
        simp only [writeMemory,cval,dval,image,dite_eq_left ht]
        rfl
      rwa [half,updateMem] at actual) cfg entry
  exact ⟨_,by change 3+n*17≤3+17*n;omega,z,_,advance,stop,rfl⟩

theorem row_offset_at (separate : bins+sites≤out) (i : Fin n) (zero : m (bins+(tag i).val)=0) (fit : totalBefore tag size (tag i) i.val<2^w) :
    (image tag size bins out m n (out+i.val)).val=offset (Function.Embedding.refl (Fin n))
      (fun j=>if tag j=tag i then size j else 0) i := by
  rw [read_row tag size bins out m separate i n i.isLt le_rfl,zero,zero_add,Fin.val_cast_of_lt fit]
  simp only [totalBefore,offset,before,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases lt : j.val < i.val <;> by_cases same : tag j=tag i <;> simp [lt,same,Fin.lt_def]

theorem row_offset (separate : bins+sites≤out) (zero : ∀c : Fin sites,m (bins+c.val)=0)
    (i : Fin n) (fit : totalBefore tag size (tag i) i.val<2^w) :
    (image tag size bins out m n (out+i.val)).val=offset (Function.Embedding.refl (Fin n))
      (fun j=>if tag j=tag i then size j else 0) i :=
  row_offset_at tag size bins out m separate i (zero _) fit

end Hierarchy.DescentOrderedWords.OffsetRAM

end OAI
