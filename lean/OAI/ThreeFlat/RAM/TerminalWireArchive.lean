import OAI.ThreeFlat.RAM.TerminalWireHeader
import Mathlib.Algebra.Ring.Fin
import OAI.ThreeFlat.RAM.CheckRowsBlock
import OAI.ThreeFlat.RAM.TickProcedureContracts
import OAI.ThreeFlat.RAM.HeaderPipeline
import OAI.ThreeFlat.RAM.MotifRows

namespace OAI
/-! # Validate the final shared boundary-wire suffix after histogram admission -/

namespace ThreeFlat.RAM.HeaderScan

open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.CompressorPacking.Native PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
variable {W : ℕ}

private theorem snoc_fill (lo i : ℕ) (word : ℕ → Word W) (m : Memory W) (bound : lo+i<2^W) :
    writeMemory (fillSegment lo i word m) ((lo+i : ℕ) : Word W) (word (lo+i)) =
      fillSegment lo (i+1) word m := by
  funext a
  unfold writeMemory
  rw [Fin.val_cast_of_lt bound]
  by_cases h : a=lo+i
  · subst a; simp [fillSegment]
  · have eq : (lo≤a ∧ a<lo+i) ↔ (lo≤a ∧ a<lo+(i+1)) := by omega
    simp [fillSegment,h,eq]

/-- A read after an earlier write in the same header scan observes precisely that
earlier word. The initial external memory outside the generated prefix is arbitrary. -/
theorem sweep_prefix (op : Word W → Memory W → Word W) (word : ℕ → Word W)
    (m : Memory W) (lo n : ℕ) (bound : lo+n<2^W)
    (correct : ∀ i<n,op ((lo+i : ℕ):Word W) (fillSegment lo i word m)=word (lo+i)) :
    sweep op n (lo:Word W) m = fillSegment lo n word m := by
  have step (k i : ℕ) (h : i+k=n) :
      sweep op k ((lo+i : ℕ):Word W) (fillSegment lo i word m)=fillSegment lo n word m := by
    induction k generalizing i with
    | zero => simp_all [sweep]
    | succ k ih =>
      rw [sweep,correct i (by omega),snoc_fill lo i word m (by omega)]
      have bump : ((lo+i : ℕ):Word W)+1 = ((lo+(i+1):ℕ):Word W) := by
        simp [Nat.cast_add,add_assoc]
      rw [bump]
      exact ih (i+1) (by omega)
  simpa only [Nat.add_zero,fillSegment_zero] using step n 0 (by omega)

theorem prefix_spec (current : Word W) (baseOff countOff lo n : ℕ) (e : Term W 0 1)
    (m : Memory W) (word : ℕ → Word W) (bound : lo+n<2^W)
    (base : (headerWord m current baseOff).val=lo)
    (count : (headerWord m current countOff).val=n)
    (correct : ∀ i<n,e.eval Fin.elim0 (fillSegment lo i word m) (fun _ => ((lo+i:ℕ):Word W))=word (lo+i)) :
    (procedure current baseOff countOff e).Spec (·=m) (fun _ after => after=fillSegment lo n word m)
      (11+n*(2*e.binds+4)) := by
  let P := Pipeline.scan current baseOff countOff e
  have fit : P.fits m := by
    change (headerWord m current baseOff).val+(headerWord m current countOff).val<2^W
    rwa [base,count]
  have ready : P.program.Spec (fun n => n=m) (fun _ after => after=P.run m) (P.ticks m) := by
    intro p r k
    exact P.correct m fit
  have startWord : headerWord m current baseOff=(lo:Word W) := by
    rw [←base,Fin.cast_val_eq_self]
  have runEq : P.run m = fillSegment lo n word m := by
    change sweep (fun a m' => e.eval Fin.elim0 m' (fun _ => a))
      (headerWord m current countOff).val (headerWord m current baseOff) m = _
    rw [count,startWord]
    exact sweep_prefix (fun a m' => e.eval Fin.elim0 m' (fun _ => a)) word m lo n bound correct
  have timeEq : P.ticks m = 11+n*(2*e.binds+4) := by
    change 11+(headerWord m current countOff).val*(2*e.binds+4) = _
    rw [count]
  rw [←runEq,←timeEq]
  exact @ready

end ThreeFlat.RAM.HeaderScan

namespace ThreeFlat.RAM.TerminalWireArchive

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPinsExpr MotifRows PhysicalProcedure
open scoped Classical Fin.CommRing
variable {W : ℕ}

/-- Saturation at capacity+1 gives well-defined reject behavior even for oversized widths. -/
def addWidth (cap prev width : ℕ) := if cap<prev ∨ cap-prev<width then cap+1 else prev+width

theorem addWidth_eq (cap prev width : ℕ) : addWidth cap prev width = min (cap+1) (prev+width) := by
  unfold addWidth
  split_ifs <;> omega

def prefixWord (x : Layout) : Formula 1 :=
  let i := Formula.cut (.reg 0) (.lit x.prefixBase)
  let prev := Formula.load (.cut (.reg 0) (.lit 1))
  let width := Formula.load (plus (.lit x.widthBase) (.cut i (.lit 1)))
  let tooBig := Formula.lit (x.capacity+1)
  Formula.select .eq i (.lit 0) (.lit 0)
    (.select .lt (.lit x.capacity) prev tooBig
      (.select .lt (.cut (.lit x.capacity) prev) width tooBig (plus prev width)))

/-- The end sentinel positions the same deterministic bounded row checker on every terminal
record, including one with no capacity left after the histogram prefix. -/
def checkWord (x : Layout) : Formula 1 :=
  let n := Formula.load (.lit (x.prefixBase+x.edges))
  let src := Formula.select .eq (.load (.lit x.phase)) (.lit 1) (.lit x.newSource) (.lit x.oldSource)
  .select .lt (.lit x.capacity) n (.lit 0)
    (.select .eq (.reg 0) (.lit x.capacity) (.lit 1)
      (.select .lt (.reg 0) n (.lit 1)
        (.select .eq (.load (plus src (.reg 0))) (.lit 0) (.lit 1) (.lit 0))))

def check (x : Layout) : Procedure W :=
  ⟨_,_,0,CheckRowsBlock.block (HeaderScan.closed (checkWord x) : DescriptorExpr.Term W 0 1) x.current,
    Fin.elim0⟩

def program (x : Layout) : Procedure W :=
  (HeaderScan.procedure (x.current : Word W) 1 2 (HeaderScan.closed (prefixWord x))).seq (check x)

theorem prefix_value (x : Layout) (mem : ℕ → ℕ) (p : Fin 1 → ℕ) (i : ℕ) (cursor : p 0=x.prefixBase+i) :
    Formula.natural W (fun _ => 0) mem p (prefixWord x) =
      if i=0 then 0 else addWidth x.capacity (mem (p 0-1)) (mem (x.widthBase+(i-1))) := by
  have h : p 0-x.prefixBase=i := by omega
  simp only [prefixWord,plus,Formula.natural,natTest,natOp,h,decide_eq_true_eq,addWidth]
  split_ifs <;> simp_all; omega

private theorem check_value (x : Layout) (mem : ℕ → ℕ) (i : ℕ) :
    Formula.natural W (fun _ => 0) mem (fun _ => i) (checkWord x) =
      (if x.capacity < mem (x.prefixBase+x.edges) then 0 else if i=x.capacity then 1
       else if i < mem (x.prefixBase+x.edges) then 1
       else if mem ((if mem x.phase=1 then x.newSource else x.oldSource)+i)=0 then 1 else 0) := by
  by_cases phase : mem x.phase=1 <;>
    simp only [checkWord,plus,Formula.natural,natTest,natOp,phase,decide_eq_true_eq,
      ite_true,ite_false,decide_true,decide_false,Bool.false_eq_true] <;>
    by_cases a : x.capacity < mem (x.prefixBase+x.edges) <;>
    by_cases b : i=x.capacity <;> by_cases c : i < mem (x.prefixBase+x.edges) <;>
    simp [a,b,c]

theorem all_checks (x : Layout) (mem : ℕ → ℕ) (n : ℕ) (total : mem (x.prefixBase+x.edges)=n) :
    (∀ i<x.capacity+1, Formula.natural W (fun _ => 0) mem (fun _ => i) (checkWord x)=1) ↔
    n ≤ x.capacity ∧ ∀ i : ℕ, n ≤ i → i < x.capacity →
      mem ((if mem x.phase=1 then x.newSource else x.oldSource)+i)=0 := by
  simp only [check_value,total]
  constructor
  · intro checks
    have cap := checks x.capacity (by omega)
    have fits : n≤x.capacity := by split_ifs at cap <;> omega
    refine ⟨fits,?_⟩
    intro i hi ci
    have z := checks i (by omega)
    by_contra nz
    simp only [ite_eq_right (not_lt.mpr fits),ite_eq_right (Nat.ne_of_lt ci),ite_eq_right (not_lt.mpr hi),
      ite_eq_right nz] at z; contradiction
  · rintro ⟨fits,pad⟩ i hi
    by_cases h : i=x.capacity
    · simp [h,show ¬x.capacity<n by omega]
    · by_cases live : i<n
      · simp [h,live,show ¬x.capacity<n by omega]
      · simp [h,live,show ¬x.capacity<n by omega,pad i (by omega) (by omega)]

/-- All arithmetic operands and addressed final-record spans fit in one word. -/
structure Bounds (x : Layout) (W : ℕ) : Prop where
  phase : x.phase < 2^W
  current : x.current < 2^W
  capacity : x.capacity+1 < 2^W
  «prefix» : x.prefixBase+(x.edges+1) < 2^W
  widths : x.widthBase+x.edges < 2^W
  oldBits : x.oldSource+x.capacity < 2^W
  newBits : x.newSource+x.capacity < 2^W

private theorem closed_natural (f : Formula 1) (m : Memory W) (i : ℕ)
    (pub : Fin 0 → Word W)
    (fit : f.Fits W (fun _ => 0) (fun a => (m a).val) (fun _ => i)) :
    (HeaderScan.closed f).eval pub m (fun _ => (i:Word W)) =
      (f.natural W (fun _ => 0) (fun a => (m a).val) (fun _ => i) : Word W) := by
  rw [HeaderScan.eval_closed]
  simpa using f.value_eq_natural (fun _ => 0) (fun a => (m a).val) (fun _ => i) fit

private theorem prefix_fits (x : Layout) (room : Bounds x W) (m : Memory W)
    (i : ℕ) (hi : i≤x.edges) :
    (prefixWord x).Fits W (fun _ => 0) (fun a => (m a).val) (fun _ => x.prefixBase+i) := by
  have one : 1<2^W := by have := room.capacity; omega
  have space := room.prefix
  have cap := room.capacity
  have width := room.widths
  simp only [prefixWord,plus,Formula.Fits,Formula.natural,natOp,natTest,opFits,
    decide_eq_true_eq,true_and,and_true,add_tsub_cancel_left]
  split_ifs <;> simp_all only [Fin.isLt,true_and,and_true] <;> omega

private theorem check_fits (x : Layout) (room : Bounds x W) (m : Memory W)
    (i : ℕ) (hi : i≤x.capacity) :
    (checkWord x).Fits W (fun _ => 0) (fun a => (m a).val) (fun _ => i) := by
  have bound := room.capacity
  have pub := room.phase
  have front := room.prefix
  have left := room.oldBits
  have right := room.newBits
  have read (j : ℕ) : (m j).val < 2^W := (m j).isLt
  by_cases phase : (m x.phase).val=1 <;>
   simp only [checkWord,plus,Formula.Fits,Formula.natural,natOp,natTest,opFits,
    phase,decide_true,decide_false,Bool.false_eq_true,ite_false,ite_true,
    decide_eq_true_eq,read,true_and,and_true] <;>
   split_ifs <;> simp_all only [true_and,and_true] <;> repeat' apply And.intro <;> omega

/-- Natural sum of the widths on a genuine terminal branch, clipped at the first overflow. -/
def total (x : Layout) (m : Memory W) (i : ℕ) :=
  min (x.capacity+1) (∑ j ∈ Finset.range i,(m (x.widthBase+j)).val)

private theorem total_succ (x : Layout) (m : Memory W) (i : ℕ) :
    total x m (i+1) = addWidth x.capacity (total x m i) (m (x.widthBase+i)).val := by
  simp only [total,Finset.sum_range_succ,addWidth_eq]
  omega

def «prefix» (x : Layout) (m : Memory W) (address : ℕ) : Word W :=
  (total x m (address-x.prefixBase) : Word W)

def image (x : Layout) (m : Memory W) : Memory W :=
  fillSegment x.prefixBase (x.edges+1) («prefix» x m) m

theorem prefix_steps (x : Layout) (room : Bounds x W) (m : Memory W)
    (base : (HeaderScan.headerWord m (x.current:Word W) 1).val=x.prefixBase)
    (count : (HeaderScan.headerWord m (x.current:Word W) 2).val=x.edges+1)
    (disjoint : ∀ j<x.edges,x.widthBase+j<x.prefixBase ∨ x.prefixBase+x.edges<x.widthBase+j) :
    (HeaderScan.procedure (x.current:Word W) 1 2 (HeaderScan.closed (prefixWord x))).Spec
      (·=m) (fun _ after => after=image x m) (11+(x.edges+1)*(2*(prefixWord x).work+4)) := by
  rw [←HeaderScan.binds_closed (w:=W) (prefixWord x)]
  apply HeaderScan.prefix_spec _ _ _ _ _ _ m («prefix» x m) room.prefix base count
  intro i hi
  let μ := fillSegment x.prefixBase i («prefix» x m) m
  rw [closed_natural _ μ _ _ (prefix_fits x room μ i (by omega)),
    prefix_value x _ _ i rfl]
  cases i with
  | zero => simp [«prefix»,total]
  | succ i =>
    have hprev : (μ (x.prefixBase+(i+1)-1)).val=total x m i := by
      have fit : total x m i<2^W := lt_of_le_of_lt (min_le_left ..) room.capacity
      simp [μ,fillSegment,«prefix»,show x.prefixBase+(i+1)-1=x.prefixBase+i by omega,
        Fin.val_cast_of_lt fit]
    have hwidth : μ (x.widthBase+i)=m (x.widthBase+i) := by
      have sep := disjoint i (by omega)
      simp [μ,fillSegment,show ¬(x.prefixBase≤x.widthBase+i ∧ x.widthBase+i<x.prefixBase+(i+1)) by omega]
    have prev : (μ (x.prefixBase+i)).val = total x m i := by simpa only [Nat.add_succ,Nat.succ_sub_one] using hprev
    simp [«prefix»,prev,hwidth,total_succ]

theorem image_entry (x : Layout) (m : Memory W) (room : Bounds x W) (i : ℕ) (hi : i≤x.edges) :
    (image x m (x.prefixBase+i)).val=total x m i := by
  have fit : total x m i<2^W := lt_of_le_of_lt (min_le_left ..) room.capacity
  simp [image,fillSegment,show x.prefixBase+i<x.prefixBase+(x.edges+1) by omega,
    «prefix»,Fin.val_cast_of_lt fit]

/-- The clipped native accumulator agrees with every requested physical edge address
on a fitting terminal word array. This includes the final one-past-the-last total. -/
theorem image_exact (x : Layout) (m : Memory W) (room : Bounds x W) {edges : ℕ}
    (w : Fin edges → ℕ) (size : x.edges=edges) (loaded : ∀ j : Fin edges,(m (x.widthBase+j.val)).val=w j)
    (fits : ∑ j,w j ≤ x.capacity) (i : ℕ) (hi : i≤edges) :
    (image x m (x.prefixBase+i)).val=∑ j : Fin i,w (j.castLE hi) := by
  rw [image_entry x m room i (by omega),total]
  have whole : (∑ j ∈ Finset.range edges,(m (x.widthBase+j)).val) = ∑ j,w j := by
    rw [←Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun j _=>loaded j)
  have small : (∑ j ∈ Finset.range i,(m (x.widthBase+j)).val) ≤ x.capacity+1 := by
    have monotone : (∑ j ∈ Finset.range i,(m (x.widthBase+j)).val) ≤
      ∑ j ∈ Finset.range edges,(m (x.widthBase+j)).val :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hi) (by intros; omega)
    omega
  rw [min_eq_right small,←Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl (fun j _=>loaded (j.castLE hi))

/-- Accepted words consist of a finite live suffix and zero padding. -/
def canonical (x : Layout) (m : Memory W) : Prop :=
  let n := (m (x.prefixBase+x.edges)).val
  n ≤ x.capacity ∧ ∀ i : ℕ, n ≤ i → i < x.capacity →
    m ((if (m x.phase).val=1 then x.newSource else x.oldSource)+i)=0

theorem check_steps {F : Type*} [Semiring F] (field : FieldCode F W)
    (x : Layout) (room : Bounds x W) :
    TickStageSpec.Admission field (check (W:=W) x).block (check x).publicData
      (fun m => (m (m x.current).val).val=x.capacity+1) (canonical x) (fun old new_ => new_=old)
      (6+(x.capacity+1)*(2*(checkWord x).work+4)) := by
  intro p r k M pc reg pub exit installed words c m start hp
  let e : DescriptorExpr.Term W 0 1 := HeaderScan.closed (checkWord x)
  obtain ⟨t,ht,d,run,atPC,reject⟩ := CheckRowsBlock.advance_block e x.current pc reg pub exit M
    installed c m start
  rw [Fin.val_cast_of_lt room.current,hp] at ht atPC
  let pinsRead : Fin 0 → Word W := M.publicData ∘ pub
  have eb : e.binds=(checkWord x).work := HeaderScan.binds_closed _
  rw [eb] at ht
  have equivalent : (∀ i,i<x.capacity+1 → e.eval pinsRead m (fun _ => (i:Word W))=1)
      ↔ canonical x m := by
    have one : 1<2^W := by have := room.capacity; omega
    have perRow (i : ℕ) (hi : i<x.capacity+1) :
        e.eval pinsRead m (fun _ => (i:Word W))=1 ↔
        (checkWord x).natural W (fun _ => 0) (fun a => (m a).val) (fun _ => i)=1 := by
      change (HeaderScan.closed (checkWord x) : DescriptorExpr.Term W 0 1).eval pinsRead m (fun _=>(i:Word W))=1 ↔ _
      rw [closed_natural _ _ _ _ (check_fits x room m i (by omega))]
      have bits : (checkWord x).natural W (fun _ => 0) (fun a => (m a).val) (fun _ => i)<2^W := by
        rw [check_value]
        split_ifs <;> omega
      rw [Fin.ext_iff,Fin.val_cast_of_lt bits,Fin.val_one',Nat.mod_eq_of_lt one]
    refine Iff.trans ⟨fun f i hi => (perRow i hi).mp (f i hi),fun f i hi => (perRow i hi).mpr (f i hi)⟩ ?_
    have hz (a : ℕ) : (m a).val = 0 ↔ m a = 0 :=
      ⟨fun h => Fin.ext (by simpa only [Fin.val_zero] using h),fun h => by simp only [h, Fin.val_zero]⟩
    simpa only [canonical, hz] using all_checks (W:=W) x (fun a => (m a).val) _ rfl
  change d.pc=(if ∀ i : ℕ, i<x.capacity+1 → e.eval pinsRead m (fun _=>(i:Word W))=1 then exit
    else pc ((8:Fin 9).castAdd e.labels)) at atPC
  constructor
  · intro ok
    rw [ite_eq_left (equivalent.mpr ok)] at atPC
    exact ⟨t,ht,d,m,atPC,rfl,run⟩
  · intro no extra
    rw [ite_eq_right (fun h => no (equivalent.mp h))] at atPC
    let cap := 6+(x.capacity+1)*(2*(checkWord x).work+4)
    change mass field M.program (extra+cap) c m=0
    rw [show extra+cap=(extra+(cap-t))+t by omega,mass_of_advance field _ run]
    generalize extra+(cap-t)=rest
    cases rest with
    | zero => rfl
    | succ rest =>
      have rom : M.code d.pc = .reject := by rw [atPC]; exact reject
      simp only [mass,Machine.program,rom,Instr.run]

/-- The complete genuine suffix procedure returns with its filled physical prefix table
precisely for an admitted padded wire suffix, with a common upper bound on all paths. -/
theorem admission {F : Type*} [Semiring F] (field : FieldCode F W) (x : Layout)
    (room : Bounds x W) (m : Memory W)
    (base : (HeaderScan.headerWord m (x.current:Word W) 1).val=x.prefixBase)
    (count : (HeaderScan.headerWord m (x.current:Word W) 2).val=x.edges+1)
    (disjoint : ∀ j<x.edges,x.widthBase+j<x.prefixBase ∨ x.prefixBase+x.edges<x.widthBase+j)
    (cap : (image x m ((image x m x.current).val)).val=x.capacity+1) :
    TickStageSpec.Admission field (program (W:=W) x).block (program x).publicData (·=m)
      (fun _ => canonical x (image x m)) (fun _old out =>
        ∃ tmp, tmp=image x m ∧ out=tmp)
      ((11+(x.edges+1)*(2*(prefixWord x).work+4))+(6+(x.capacity+1)*(2*(checkWord x).work+4))) := by
  apply TickStageSpec.admission_seq field _ _ (TickStageSpec.admission_of_spec field _
    (prefix_steps x room m base count disjoint)) (check_steps field x room)
  · intros; trivial
  · rintro _ _ rfl _ rfl
    exact ⟨cap,Iff.rfl⟩

end ThreeFlat.RAM.TerminalWireArchive

end OAI
