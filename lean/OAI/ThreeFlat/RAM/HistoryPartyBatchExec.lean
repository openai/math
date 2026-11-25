import OAI.ThreeFlat.RAM.HistoryPartyBatch
import OAI.ThreeFlat.RAM.HistoryPartyBootExec
import OAI.ThreeFlat.RAM.HistoryPartySpecialization
import OAI.ThreeFlat.RAM.HistoryPartyTapeRun
import OAI.ThreeFlat.RAM.HistorySelectedRead
import OAI.ThreeFlat.RAM.HistoryGeneratedStore
import OAI.ThreeFlat.RAM.ExpressionReads
import OAI.ThreeFlat.RAM.PhysicalExactRun
import OAI.ThreeFlat.RAM.HeaderPipeline
import OAI.ThreeFlat.RAM.WordQuotients

namespace OAI
/-! # Native generation of a selected party's batch header, command rows and operands -/

namespace ThreeFlat.RAM.HistoryPartyBatchExec

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr PhysicalProcedure
open HistoryPartyBatch HistoryPartyHeader
open scoped Fin.CommRing

variable {w : ℕ}

/-- Values assigned to the registers of the batch-header descriptor at one physical column. -/
def headerRegs (A : Layout) (j : ℕ) (i : Fin 13) :=
  if i=0 then A.seed+4 else if i=5 then j else 0

theorem offset_eval (base i : ℕ) (m : Memory w) :
    (absAddr (W:=w) base).eval Fin.elim0 m (fun _ => ((base+i : ℕ):Word w)) = (i:Word w) := by
  simp [absAddr,Term.eval,BinaryOp.eval,Nat.cast_add]

theorem closed_eval {n : ℕ} (f : Formula n) (raw : ℕ → ℕ) (regs : Fin n → ℕ)
    (fit : f.Fits w (fun _ => 0) raw regs) :
    (HeaderScan.closed f : Term w 0 n).eval Fin.elim0 (fun x => (raw x : Word w))
      (fun i => (regs i : Word w)) = (f.natural w (fun _ => 0) raw regs : Word w) := by
  rw [HeaderScan.eval_closed]
  exact f.value_eq_natural (fun _ => 0) raw regs fit

theorem actualHeader_eval (A : Layout) (R : Registers) (B : Kind) (checks : Bool)
    (raw : ℕ → ℕ) (j : Fin 26)
    (args : ∀ i : Fin 11, raw (A.seed+4+i.val)=R.words i)
    (grid : ∀ i : Fin 7, raw (R.grid+i.val)=B.words i)
    (fit : (HistoryPartyHeader.formula checks).Fits w (fun _ => 0) raw (headerRegs A j.val)) :
    (actualHeader w A checks).eval Fin.elim0 (fun x => (raw x:Word w))
      (fun _ => ((A.batch+j.val : ℕ):Word w)) =
      ((HistoryPartyHeader.batch R B raw checks).words j : Word w) := by
  unfold actualHeader
  rw [Term.eval_instantiate]
  have operands :
      (fun i : Fin 13 => ((if i=0 then Term.literal ((A.seed+4 : ℕ):Word w)
        else if i=5 then absAddr A.batch else Term.literal 0 : Term w 0 1)).eval Fin.elim0
          (fun x => (raw x:Word w)) (fun _ => ((A.batch+j.val : ℕ):Word w))) =
        fun i => (headerRegs A j.val i : Word w) := by
    funext i
    by_cases z : i=0 <;> by_cases f : i=5 <;> simp [headerRegs,z,f]
    simpa only [Nat.cast_add] using offset_eval A.batch j.val (fun x => (raw x : Word w))
  rw [operands,closed_eval _ raw _ fit]
  rw [HistoryPartyHeader.formula_word w R B checks (A.seed+4) (fun _ => 0) raw
    (headerRegs A j.val) j args grid (by simp [headerRegs]) (by simp [headerRegs])]

def bankStart (A : Layout) (commands : Bool) := if commands then A.commands else A.arguments
def stride (commands : Bool) : ℕ := if commands then 21 else 23
def batchRegs (A : Layout) (i col : ℕ) : Fin 3 → ℕ := ![A.batch,i,col]

private theorem batch_eval (A : Layout) (commands : Bool) (raw : ℕ→ℕ) (i col : ℕ)
    (fc : col < stride commands) (fs : stride commands < 2^w) (fi : stride commands*i+col < 2^w)
    (fit : (if commands then HistoryBatchTape.rawCommand else HistoryBatchTape.rawArguments).Fits
      w (fun _ => 0) raw (batchRegs A i col)) :
    (batchTerm w A commands).eval Fin.elim0 (fun x => (raw x : Word w))
      (fun _ => ((bankStart A commands+(stride commands*i+col):ℕ):Word w)) =
      ((if commands then HistoryBatchTape.rawCommand else HistoryBatchTape.rawArguments).natural
        w (fun _ => 0) raw (batchRegs A i col) : Word w) := by
  let step := stride commands
  let key := step*i+col
  let m : Memory w := fun x => (raw x : Word w)
  let addr : Word w := ((bankStart A commands+key : ℕ) : Word w)
  have pos : 0 < step := Nat.zero_lt_of_lt fc
  have div : BinaryOp.div.eval (key : Word w) (step : Word w) = (i : Word w) := by
    rw [WordQuotients.div_at key step fi fs]
    congr 1
    dsimp [key]
    rw [Nat.mul_add_div pos,Nat.div_eq_of_lt fc,Nat.add_zero]
  have mod : BinaryOp.mod.eval (key : Word w) (step : Word w) = (col : Word w) := by
    rw [WordQuotients.mod_at key step fi fs]
    congr 1
    dsimp [key]
    rw [Nat.mul_add_mod,Nat.mod_eq_of_lt fc]
  have address : (absAddr (bankStart A commands)).eval Fin.elim0 m (fun _ => addr) = (key : Word w) :=
    offset_eval _ _ _
  have liter : (if commands then (21:Word w) else 23) = (step : Word w) := by cases commands <;> rfl
  unfold batchTerm
  rw [Term.eval_instantiate]
  change (HeaderScan.closed _).eval Fin.elim0 m
    (fun j => ((![.literal (A.batch:Word w),
      .binary .div (absAddr (bankStart A commands)) (.literal (if commands then (21:Word w) else 23)),
      .binary .mod (absAddr (bankStart A commands)) (.literal (if commands then (21:Word w) else 23))]
      : Fin 3 → Term w 0 1) j).eval Fin.elim0 m (fun _ => addr)) = _
  have regs :
      (fun j => ((![.literal (A.batch:Word w),
        .binary .div (absAddr (bankStart A commands)) (.literal (if commands then (21:Word w) else 23)),
        .binary .mod (absAddr (bankStart A commands)) (.literal (if commands then (21:Word w) else 23))]
        : Fin 3 → Term w 0 1) j).eval Fin.elim0 m (fun _ => addr)) =
      fun j => (batchRegs A i col j : Word w) := by
    funext j
    fin_cases j <;> simp [batchRegs,liter,address,div,mod]
  rw [regs]
  exact closed_eval _ raw _ fit

theorem command_eval (A : Layout) (T : HistoryBatchTape.Header) (raw : ℕ→ℕ)
    (i : ℕ) (j : Fin 3) (u : Fin 7) (room : 21 < 2^w) (key : 21*i+(7*j.val+u.val) < 2^w)
    (stored : ∀ k : Fin 26, raw (A.batch+k.val)=T.words k)
    (fit : HistoryBatchTape.rawCommand.Fits w (fun _ => 0) raw (batchRegs A i (7*j.val+u.val))) :
    (batchTerm w A true).eval Fin.elim0 (fun x => (raw x:Word w))
      (fun _ => ((A.commands+(21*i+(7*j.val+u.val)):ℕ):Word w)) =
      (HistoryBatchTape.command T i j u : Word w) := by
  apply (batch_eval A true raw i (7*j.val+u.val)
    (by change 7*j.val+u.val<21; have := j.isLt; have := u.isLt; omega) room key fit).trans
  exact congrArg (fun x : ℕ => (x:Word w)) (HistoryBatchTape.command_value w (fun _=>0) raw T A.batch i j u stored)

theorem argument_eval (A : Layout) (T : HistoryBatchTape.Header) (raw : ℕ→ℕ)
    (i : ℕ) (u : Fin 23) (room : 23 < 2^w) (key : 23*i+u.val < 2^w)
    (stored : ∀ k : Fin 26, raw (A.batch+k.val)=T.words k)
    (fit : HistoryBatchTape.rawArguments.Fits w (fun _=>0) raw (batchRegs A i u.val)) :
    (batchTerm w A false).eval Fin.elim0 (fun x => (raw x:Word w))
      (fun _ => ((A.arguments+(23*i+u.val):ℕ):Word w)) =
      (HistoryBatchTape.arguments T raw i u : Word w) := by
  apply (batch_eval A false raw i u.val u.isLt room key fit).trans
  exact congrArg (fun x : ℕ=> (x:Word w)) (HistoryBatchTape.argument_value w (fun _=>0) raw T A.batch i u stored)

def numeric (input : Memory w) (a : ℕ) : ℕ := (input a).val

theorem word_numeric (input : Memory w) : (fun a => (numeric input a : Word w)) = input :=
  funext fun a => Fin.cast_val_eq_self (input a)

/-- Every address probed by the row expression lies outside this write interval. -/
def Protected (e : Term w 0 1) (input : Memory w) (lo n : ℕ) :=
  ∀ (a : Word w), lo ≤ a.val → a.val < lo+n →
    ∀ x ∈ e.reads Fin.elim0 input (fun _ => a), x<lo ∨ lo+n≤x

def headerWord (T : HistoryBatchTape.Header) (base address : ℕ) : Word w :=
  if h : address-base < 26 then (T.words ⟨address-base,h⟩ : Word w) else 0

theorem headerWord_at (T : HistoryBatchTape.Header) (base : ℕ) (j : Fin 26) :
    headerWord (w:=w) T base (base+j.val) = (T.words j : Word w) := by
  simp [headerWord,j.isLt]

def commandWord (T : HistoryBatchTape.Header) (base addr : ℕ) : Word w :=
  let z := addr-base
  let row := z/21
  let job : Fin 3 := ⟨z%21/7, by omega⟩
  let col : Fin 7 := ⟨z%7, Nat.mod_lt _ (by decide)⟩
  (HistoryBatchTape.command T row job col : Word w)

def argWord (T : HistoryBatchTape.Header) (raw : ℕ→ℕ) (base addr : ℕ) : Word w :=
  let z := addr-base
  (HistoryBatchTape.arguments T raw (z/23) ⟨z%23,Nat.mod_lt _ (by decide)⟩ : Word w)

theorem commandWord_at (T : HistoryBatchTape.Header) (base i : ℕ) (j : Fin 3) (u : Fin 7) :
    commandWord (w:=w) T base (base+(21*i+(7*j.val+u.val))) = (HistoryBatchTape.command T i j u : Word w) := by
  let z := 21*i+(7*j.val+u.val)
  have row : z/21=i := by dsimp [z]; have := j.isLt; have := u.isLt; omega
  have job : (⟨z%21/7,by omega⟩ : Fin 3)=j := Fin.ext (by dsimp [z]; have := j.isLt; have := u.isLt; omega)
  have col : (⟨z%7,Nat.mod_lt _ (by decide)⟩ : Fin 7)=u :=
    Fin.ext (by dsimp [z]; have := u.isLt; omega)
  change commandWord T base (base+z) = _
  simp only [commandWord,Nat.add_sub_cancel_left,row,job,col]

theorem argWord_at (T : HistoryBatchTape.Header) (raw : ℕ→ℕ) (base i : ℕ) (u : Fin 23) :
    argWord (w:=w) T raw base (base+(23*i+u.val)) = (HistoryBatchTape.arguments T raw i u : Word w) := by
  simp [argWord,Nat.mul_add_div (by decide : 0<23),Nat.div_eq_of_lt u.isLt,
    Nat.mod_eq_of_lt u.isLt]

theorem fixed_exec (e : Term w 0 1) (input : Memory w) (lo n : ℕ) (word : ℕ→Word w)
    (cap : lo+n<2^w) (protect : Protected e input lo n)
    (correct : ∀ (a : Word w), lo≤a.val → a.val<lo+n → e.eval Fin.elim0 input (fun _=>a) = word a.val) :
    (PhysicalInputPhases.writing e Fin.elim0 lo n).Exec input (fillSegment lo n word input)
      (4+n*(2*e.binds+4)) := by
  intro P R K machine pc reg pub exit installed params cfg src entry original
  subst src
  refine PhysicalInputPhases.writing_spec e Fin.elim0 lo n cap (fun m => m=input) word ?_
    machine pc reg pub exit installed params cfg input entry rfl
  intro orig eq a m low high frame
  subst orig
  exact (e.eval_eq_of_agrees_reads Fin.elim0 input m (fun _=>a)
    (fun x hx => frame x (protect a low high x hx))).trans (correct a low high)

/-- Resident concrete sources of the selector and payload batch header. -/
structure HeaderProtected (A : Layout) (R : Registers) (B : Kind) (checks : Bool) (input : Memory w) : Prop where
  args : ∀ j : Fin 11, A.seed+4+j.val<A.batch ∨ A.batch+26≤A.seed+4+j.val
  grid : ∀ j : Fin 7, R.grid+j.val<A.batch ∨ A.batch+26≤R.grid+j.val
  incident : ∀ j : Fin 4, R.incident+j.val<A.batch ∨ A.batch+26≤R.incident+j.val
  dyadic : ∀ j : Fin 3, R.dyadic+j.val<A.batch ∨ A.batch+26≤R.dyadic+j.val
  lookup : ∀ i : Fin 2, let x := R.lutBase+R.lutStride*(if checks then B.selectorPage else B.tilePage)+i.val
    x<A.batch ∨ A.batch+26≤x
  counts : ∀ i : Fin 2, let x := R.countBase+2*numeric input (R.dyadic+1)+i.val
    x<A.batch ∨ A.batch+26≤x

theorem header_exec (A : Layout) (R : Registers) (B : Kind) (checks : Bool) (input : Memory w)
    (args : ∀ j : Fin 11, numeric input (A.seed+4+j.val)=R.words j)
    (grid : ∀ j : Fin 7, numeric input (R.grid+j.val)=B.words j)
    (cap : A.batch+26 < 2^w)
    (seedRoom : A.seed+37<2^w) (protect : HeaderProtected A R B checks input)
    (rooms : HistoryPartyHeader.ReadRoom w R B checks (numeric input)) :
    (PhysicalInputPhases.writing (actualHeader w A checks) Fin.elim0 A.batch 26).Exec input
      (fillSegment A.batch 26 (headerWord (HistoryPartyHeader.batch R B (numeric input) checks) A.batch) input)
      (4+26*(2*(actualHeader w A checks).binds+4)) := by
  intro P regs K machine pc reg pub exit installed params cfg src start original
  subst src
  refine PhysicalInputPhases.writing_spec (actualHeader w A checks) Fin.elim0 A.batch 26 cap
    (fun m => m=input) (headerWord (HistoryPartyHeader.batch R B (numeric input) checks) A.batch)
    ?_ machine pc reg pub exit installed params cfg input start rfl
  intro orig initial a μ lo hi frame
  subst orig
  let j : Fin 26 := ⟨a.val-A.batch,by omega⟩
  have val : A.batch+j.val=a.val := Nat.add_sub_of_le lo
  have get (x : ℕ) (off : x<A.batch ∨ A.batch+26≤x) : numeric μ x=numeric input x :=
    congrArg Fin.val (frame x off)
  have args' (k : Fin 11) := (get _ (protect.args k)).trans (args k)
  have grid' (k : Fin 7) := (get _ (protect.grid k)).trans (grid k)
  have copies : numeric μ (R.incident+3)=numeric input (R.incident+3) := get _ (protect.incident 3)
  have hist : numeric μ (R.incident+1)=numeric input (R.incident+1) := get _ (protect.incident 1)
  have exp : numeric μ (R.dyadic+1)=numeric input (R.dyadic+1) := get _ (protect.dyadic 1)
  have n : numeric μ (R.dyadic+2)=numeric input (R.dyadic+2) := get _ (protect.dyadic 2)
  let lut := R.lutBase+R.lutStride*(if checks then B.selectorPage else B.tilePage)
  let ptr := R.countBase+2*numeric input (R.dyadic+1)
  have l : numeric μ lut=numeric input lut := get _ (protect.lookup 0)
  have l' : numeric μ (lut+1)=numeric input (lut+1) := get _ (protect.lookup 1)
  have c : numeric μ ptr=numeric input ptr := get _ (protect.counts 0)
  have c' : numeric μ (ptr+1)=numeric input (ptr+1) := get _ (protect.counts 1)
  have same : batch R B (numeric μ) checks=batch R B (numeric input) checks := by
    dsimp only [batch]
    rw [copies,hist,exp,n,l,l',c,c']
  have rooms' : HistoryPartyHeader.ReadRoom w R B checks (numeric μ) :=
    ⟨rooms.grid,rooms.incident,rooms.dyadic,rooms.lookup,by rw [exp]; exact rooms.counts⟩
  have fit := HistoryPartyHeader.formula_fits w R B checks (A.seed+4) (fun _=>0) (numeric μ)
    (headerRegs A j.val) j args' grid' (by simp [headerRegs]) (by simp [headerRegs]) (by omega) rooms'
  have eq := actualHeader_eval A R B checks (numeric μ) j args' grid' fit
  rw [word_numeric μ,val,Fin.cast_val_eq_self,same] at eq
  exact eq.trans (by rw [←val,headerWord_at])

theorem scan_exec (e : Term w 0 1) (control : Word w) (start length lo n : ℕ)
    (input : Memory w) (word : ℕ→Word w) (cap : lo+n<2^w) (protect : Protected e input lo n)
    (h0 : HeaderScan.headerWord input control start = (lo:Word w))
    (h1 : HeaderScan.headerWord input control length = (n:Word w))
    (correct : ∀ a : Word w, lo≤a.val → a.val<lo+n → e.eval Fin.elim0 input (fun _=>a)=word a.val) :
    (HeaderScan.procedure control start length e).Exec input (fillSegment lo n word input)
      (13+n*(2*e.binds+4)) := by
  intro P R K machine pc reg pub exit installed params cfg src entry original
  subst src
  refine HeaderScan.spec control start length e (fun m => m=input) (fun _ => lo) (fun _ => n)
    (fun _ => word) _ (fun _ _ => ⟨cap,le_rfl⟩) (fun m h => by subst m; exact ⟨h0,h1⟩) ?_
    machine pc reg pub exit installed params cfg input entry rfl
  intro orig eq a m low high frame
  subst orig
  exact (e.eval_eq_of_agrees_reads Fin.elim0 input m (fun _=>a)
    (fun x hx => frame x (protect a low high x hx))).trans (correct a low high)

theorem scan_dynamic (e : Term w 0 1) (control : Word w) (start length lo n : ℕ)
    (input : Memory w) (word : ℕ→Word w) (cap : lo+n<2^w)
    (h0 : HeaderScan.headerWord input control start=(lo:Word w)) (h1 : HeaderScan.headerWord input control length=(n:Word w))
    (correct : ∀ (a : Word w) (μ : Memory w), lo≤a.val → a.val<lo+n →
      DescriptorScan.agreesOutside lo (lo+n) μ input → e.eval Fin.elim0 μ (fun _=>a)=word a.val) :
    (HeaderScan.procedure control start length e).Exec input (fillSegment lo n word input)
      (13+n*(2*e.binds+4)) := by
  intro P R K machine pc reg pub exit installed params cfg src entry original
  subst src
  refine HeaderScan.spec control start length e (fun m=>m=input) (fun _=>lo) (fun _=>n)
    (fun _=>word) _ (fun _ _=>⟨cap,le_rfl⟩) (fun m h=>by subst m; exact ⟨h0,h1⟩) ?_
    machine pc reg pub exit installed params cfg input entry rfl
  intro orig eq
  subst orig
  exact correct

theorem commands_exec (A : Layout) (T : HistoryBatchTape.Header) (N : ℕ) (input : Memory w)
    (stored : ∀ j : Fin 26, numeric input (A.batch+j.val)=T.words j)
    (h0 : HeaderScan.headerWord input ((A.seed+28 : ℕ):Word w) 0 = (A.commands:Word w))
    (h1 : HeaderScan.headerWord input ((A.seed+28 : ℕ):Word w) 1 = ((21*N:ℕ):Word w))
    (small : 21<2^w) (cap : A.commands+21*N<2^w)
    (headerRoom : A.batch+26<2^w) (splitSize : T.r<2^w) (before : A.batch+26≤A.commands) :
    (HeaderScan.procedure ((A.seed+28:ℕ):Word w) 0 1 (batchTerm w A true)).Exec input
      (fillSegment A.commands (21*N) (commandWord T A.commands) input)
      (13+21*N*(2*(batchTerm w A true).binds+4)) := by
  apply scan_dynamic _ _ _ _ _ _ _ _ cap h0 h1
  intro a μ lo hi frame
  have live (k : Fin 26) : numeric μ (A.batch+k.val)=T.words k := by
    rw [numeric,frame _ (.inl (by have := k.isLt; omega))]
    exact stored k
  let z := a.val-A.commands
  let i : Fin N := ⟨z/21,by dsimp [z]; omega⟩
  let j : Fin 3 := ⟨z%21/7,by omega⟩
  let u : Fin 7 := ⟨z%7,Nat.mod_lt _ (by decide)⟩
  have split : 21*i.val+(7*j.val+u.val)=z := by dsimp [i,j,u]; omega
  have addr : A.commands+(21*i.val+(7*j.val+u.val))=a.val := by rw [split]; exact Nat.add_sub_of_le lo
  have eq := command_eval A T (numeric μ) i.val j u small (by dsimp [z] at split; omega) live (HistoryBatchTape.command_fits w _ _ T _ _ j u live headerRoom (by have := i.isLt; omega) splitSize)
  rw [word_numeric μ,addr,Fin.cast_val_eq_self] at eq
  exact eq.trans (by rw [←addr,commandWord_at])

theorem arguments_exec (A : Layout) (T : HistoryBatchTape.Header) (N : ℕ) (input : Memory w)
    (stored : ∀ j : Fin 26, numeric input (A.batch+j.val)=T.words j)
    (h0 : HeaderScan.headerWord input ((A.seed+28 : ℕ):Word w) 2 = (A.arguments:Word w))
    (h1 : HeaderScan.headerWord input ((A.seed+28 : ℕ):Word w) 3 = ((23*N:ℕ):Word w))
    (small : 23<2^w) (cap : A.arguments+23*N<2^w)
    (headerRoom : A.batch+26<2^w) (splitSize : T.r<2^w) (before : A.batch+26≤A.arguments)
    (quota : T.checks=true → ∀ i : Fin N, T.r≤ i.val → T.hist+(i.val-T.r)<2^w ∧
      (T.hist+(i.val-T.r)<A.arguments ∨ A.arguments+23*N≤T.hist+(i.val-T.r))) :
    (HeaderScan.procedure ((A.seed+28:ℕ):Word w) 2 3 (batchTerm w A false)).Exec input
      (fillSegment A.arguments (23*N) (argWord T (numeric input) A.arguments) input)
      (13+23*N*(2*(batchTerm w A false).binds+4)) := by
  apply scan_dynamic _ _ _ _ _ _ _ _ cap h0 h1
  intro a μ lo hi frame
  have live (k : Fin 26) : numeric μ (A.batch+k.val)=T.words k := by
    rw [numeric,frame _ (.inl (by have := k.isLt; omega))]
    exact stored k
  let z := a.val-A.arguments
  let i : Fin N := ⟨z/23,by dsimp [z]; omega⟩
  let u : Fin 23 := ⟨z%23,Nat.mod_lt _ (by decide)⟩
  have split : 23*i.val+u.val=z := by dsimp [i,u]; omega
  have addr : A.arguments+(23*i.val+u.val)=a.val := by rw [split]; exact Nat.add_sub_of_le lo
  have eq := argument_eval A T (numeric μ) i.val u small (by dsimp [z] at split; omega) live (HistoryBatchTape.argument_fits w _ _ T _ _ u live headerRoom (by have := i.isLt; omega) splitSize
      (fun c r => (quota c i r).1))
  rw [word_numeric μ,addr,Fin.cast_val_eq_self] at eq
  have value : HistoryBatchTape.arguments T (numeric μ) i.val u = HistoryBatchTape.arguments T (numeric input) i.val u := by
    unfold HistoryBatchTape.arguments
    by_cases read : T.checks=true ∧ ¬i.val<T.r
    · have outside := (quota read.1 i (by omega)).2
      simp only [ite_eq_left read,ite_eq_right read.2,numeric,frame _ outside]
    · simp only [ite_eq_right read]
  rw [value] at eq
  exact eq.trans (by rw [←addr,argWord_at])

def infoWord (T : HistoryBatchTape.Header) (base address : ℕ) : Word w :=
  if h : address-base<4 then ((info T).words ⟨address-base,h⟩:Word w) else 0

theorem result_exec (A : Layout) (T : HistoryBatchTape.Header) (target : ℕ) (input : Memory w)
    (stored : ∀ j : Fin 26, numeric input (A.batch+j.val)=T.words j)
    (targetWord : numeric input (A.seed+35) = target)
    (h0 : HeaderScan.headerWord input ((A.seed+28 : ℕ):Word w) 6=(target:Word w))
    (h1 : HeaderScan.headerWord input ((A.seed+28 : ℕ):Word w) 7=4)
    (cap : target+4<2^w)
    (seedRoom : A.seed+37<2^w) (batchRoom : A.batch+26<2^w)
    (batchAway : A.batch+26≤target ∨ target+4≤A.batch)
    (seedAway : A.seed+35<target ∨ target+4≤A.seed+35) :
    (HeaderScan.procedure ((A.seed+28:ℕ):Word w) 6 7 (HeaderScan.closed (resultWord A))).Exec
      input (fillSegment target 4 (infoWord T target) input)
      (13+4*(2*(HeaderScan.closed (resultWord A) : Term w 0 1).binds+4)) := by
  apply scan_dynamic _ _ _ _ _ _ _ _ cap h0 h1
  intro a μ lo hi frame
  have live (k : Fin 26) : numeric μ (A.batch+k.val)=T.words k := by
    rw [numeric,frame _ (by have := k.isLt; omega)]
    exact stored k
  have dst : numeric μ (A.seed+35)=target := by
    rw [numeric,frame _ seedAway]
    exact targetWord
  let j : Fin 4 := ⟨a.val-target,by omega⟩
  have addr : target+j.val=a.val := Nat.add_sub_of_le lo
  have e := closed_eval (resultWord A) (numeric μ) (fun _=>target+j.val)
    (result_fits A w target (numeric μ) j seedRoom batchRoom cap dst)
  rw [result_value A T w target (numeric μ) j live dst,word_numeric μ,addr,
    Fin.cast_val_eq_self] at e
  exact e.trans (by rw [←addr]; simp [infoWord,j.isLt])

theorem info_read (T : HistoryBatchTape.Header) (target : ℕ) (m : Memory w) (j : Fin 4) :
    fillSegment target 4 (infoWord T target) m (target+j.val) = ((info T).words j : Word w) := by
  simp [fillSegment,infoWord,j.isLt]

open Diagonal.HistoryContraction Diagonal.HistoryContraction.Tree BitNetwork.Ordered

/-- Specialize the three numeric prefix fields to the ordered child networks. -/
theorem shape_of_sizes {F : Type*} (T : HistoryBatchTape.Header) {r s h p : ℕ}
    (hr : T.r=r) (hs : T.s=s) {arity : Fin (r+s)→ℕ}
    (N : ∀ i, BitNetwork F (arity i)) (wire : ∀ i, Fin (arity i)→BitSource h p)
    (sz : BatchRows.Sizes N T.left T.right) (hp : T.parentPins=p) (hh : T.shared=h) :
    HistoryPartyTapeRun.Shape (p:=p) (h:=h) T (fun i => N (Fin.cast (congrArg₂ Nat.add hr hs) i)) := by
  subst r; subst s
  let b : Addresses := ⟨T.stream,T.maps,0,0⟩
  have eq (i : Fin (T.r+T.s)) :
      copy b wire (fun a => Tree.atom (N a)) i = T.row i.val :=
    BatchRows.record_at N wire _ _ sz b i
  constructor
  · intro i
    exact (congrArg Copy.count (eq i)).symm
  · intro i
    exact (sz.arities i).symm
  · exact hp
  · intro i
    rw [hh]
    exact congrArg (h+·) (congrArg Copy.bitPrefix (eq i)).symm

open private prefix_value from OAI.ThreeFlat.Diagonal.HistoryBatchRows

theorem placed_of_sizes {F : Type*} (T : HistoryBatchTape.Header) {r s h p : ℕ}
    (hr : T.r=r) (hs : T.s=s) {arity : Fin (r+s)→ℕ}
    (N : ∀ i, BitNetwork F (arity i)) (_wire : ∀ i, Fin (arity i)→BitSource h p)
    (sz : BatchRows.Sizes N T.left T.right) (i : Fin (T.r+T.s)) :
    (T.row i.val).dest=(info T).stream+4*before (fun a=> (N (Fin.cast (congrArg₂ Nat.add hr hs) a)).cells) i := by
  let idx := Fin.cast (congrArg₂ Nat.add hr hs)
  have rows (a : Fin (T.r+T.s)) :
      (N (idx a)).cells = if a.val<T.r then T.left.rows else T.right.rows := by
    simpa only [idx,Fin.val_cast,hr] using sz.cells (idx a)
  change (info T).stream + 4 * BatchRows.span T.r T.left.rows T.right.rows i.val =
    (info T).stream + 4 * before (fun a => (N (idx a)).cells) i
  exact congrArg (fun value => (info T).stream + 4 * value)
    (prefix_value (r:=T.r) (s:=T.s) (t:=fun a => (N (idx a)).cells)
      T.left.rows T.right.rows rows i).symm

/-- Consecutive concrete memory images of the selected party preparation. -/
structure Build (w : ℕ) where
  layout : Layout
  checks : Bool
  kind : Kind
  input : Memory w

namespace Build
variable (X : Build w)

def bootImage := HistoryPartyBootExec.output X.layout X.checks X.input
def regs := registers X.layout X.checks (numeric X.input)
def table := HistoryPartyHeader.batch X.regs X.kind (numeric X.bootImage) X.checks
def count := children X.layout X.checks (numeric X.input)
def target := dest X.layout X.checks (numeric X.input X.layout.cursor-1) 1
def headerImage := fillSegment X.layout.batch 26 (headerWord X.table X.layout.batch) X.bootImage
def commandImage := fillSegment X.layout.commands (21*X.count) (commandWord X.table X.layout.commands) X.headerImage
def tapeImage := fillSegment X.layout.arguments (23*X.count) (argWord X.table (numeric X.commandImage) X.layout.arguments) X.commandImage
def ctrl : Word w := ((X.layout.seed+33 : ℕ) : Word w)
def scanExpr (w : ℕ) := HistorySelectedOps.rows (.literal (0:Word w) : Term w 0 4) []
def scanned (jobs : List (HistoryReadyTape.Job w)) := HistoryReadyTape.after X.ctrl jobs X.tapeImage
def published (jobs : List (HistoryReadyTape.Job w)) :=
  fillSegment X.target 4 (infoWord X.table X.target) (X.scanned jobs)

theorem read_header (j : Fin 26) : X.headerImage (X.layout.batch+j.val)=(X.table.words j : Word w) := by
  simp [headerImage,fillSegment,headerWord_at,j.isLt]

theorem read_operand (i : Fin X.count) (u : Fin 23) :
    X.tapeImage (X.layout.arguments+(23*i.val+u.val)) =
      (HistoryBatchTape.arguments X.table (numeric X.commandImage) i.val u : Word w) := by
  have lt : 23*i.val+u.val < 23*X.count := by have := i.isLt; have := u.isLt; omega
  simp [tapeImage,fillSegment,lt,argWord_at]

theorem read_command (i : Fin X.count) (j : Fin 3) (u : Fin 7)
    (apart : X.layout.commands+21*X.count ≤ X.layout.arguments ∨
      X.layout.arguments+23*X.count ≤ X.layout.commands) :
    X.tapeImage (X.layout.commands+(21*i.val+(7*j.val+u.val))) =
      (HistoryBatchTape.command X.table i.val j u : Word w) := by
  let x := X.layout.commands+(21*i.val+(7*j.val+u.val))
  have range : 21*i.val+(7*j.val+u.val)<21*X.count := by
    have := i.isLt; have := j.isLt; have := u.isLt; omega
  have off : ¬(X.layout.arguments≤x ∧ x<X.layout.arguments+23*X.count) := by dsimp [x]; omega
  change X.tapeImage x=_
  simp only [tapeImage,fillSegment,ite_eq_right off]
  dsimp only [x]
  simp [commandImage,fillSegment,range,commandWord_at]

theorem read_info (jobs : List (HistoryReadyTape.Job w)) (j : Fin 4) :
    X.published jobs (X.target+j.val)=((info X.table).words j : Word w) :=
  info_read X.table X.target _ j

def prefixCost := HistoryPartyBootExec.bootCost X.layout X.checks +
  (6+(3*Nat.clog 2 (HistoryPartyBootExec.extent X.layout (numeric X.input))+5))
def headerCost := 4+26*(2*(actualHeader w X.layout X.checks).binds+4)
def cmdCost := 13+21*X.count*(2*(batchTerm w X.layout true).binds+4)
def argCost := 13+23*X.count*(2*(batchTerm w X.layout false).binds+4)
def resultCost := 13+4*(2*(HeaderScan.closed (resultWord X.layout) : Term w 0 1).binds+4)
def cost (jobs : List (HistoryReadyTape.Job w)) :=
  (((X.prefixCost+X.headerCost)+X.cmdCost)+
    (X.argCost+(HistoryReadyTape.cost (scanExpr w).binds jobs+X.resultCost)))

private theorem job_cost (b : ℕ) (jobs : List (HistoryReadyTape.Job w)) :
    HistoryReadyTape.cost b jobs=6+19*jobs.length+(2*b+4)*(jobs.map HistoryReadyTape.Job.count).sum := by
  induction jobs with
  | nil => simp [HistoryReadyTape.cost]
  | cons j js ih =>
    simp only [HistoryReadyTape.cost,List.map_cons,List.sum_cons,List.length_cons,ih]
    ring

def fixedTicks := HistoryPartyBootExec.bootCost X.layout X.checks+11+X.headerCost+26+6+X.resultCost
def perChild := 21*(2*(batchTerm w X.layout true).binds+4)+23*(2*(batchTerm w X.layout false).binds+4)+57
noncomputable def staticCost := X.fixedTicks+3+X.perChild+(2*HistorySelectedOps.tariff []+4)

theorem cost_le (jobs : List (HistoryReadyTape.Job w)) (size : jobs.length=3*X.count) :
    X.cost jobs ≤ X.staticCost*(1+Nat.clog 2 (HistoryPartyBootExec.extent X.layout (numeric X.input))+
      X.count+(jobs.map HistoryReadyTape.Job.count).sum) := by
  let log := Nat.clog 2 (HistoryPartyBootExec.extent X.layout (numeric X.input))
  let n := (jobs.map HistoryReadyTape.Job.count).sum
  have sc : (scanExpr w).binds ≤ HistorySelectedOps.tariff [] :=
    HistorySelectedOps.rows_size_of w (.literal (0:Word w) : Term w 0 4)
      (by norm_num [Term.literal, Term.binds]) []
  have const : X.fixedTicks≤X.staticCost := by unfold staticCost; omega
  have lc : 3≤X.staticCost := by unfold staticCost; omega
  have child : X.perChild≤X.staticCost := by unfold staticCost; omega
  have contents : 2*(scanExpr w).binds+4 ≤ X.staticCost := by unfold staticCost; omega
  calc
    X.cost jobs = X.fixedTicks+3*log+X.perChild*X.count+(2*(scanExpr w).binds+4)*n := by
      simp only [cost,prefixCost,argCost,cmdCost,job_cost,size,fixedTicks,perChild,log,n]
      ring
    _ ≤ X.staticCost+X.staticCost*log+X.staticCost*X.count+X.staticCost*n := by
      exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add const (Nat.mul_le_mul_right _ lc))
        (Nat.mul_le_mul_right _ child)) (Nat.mul_le_mul_right _ contents)
    _ = _ := by change _ = X.staticCost*(1+log+X.count+n); ring

private theorem static_header_binds (v v' : ℕ) (A B : Layout) (checks : Bool) :
    (actualHeader v A checks).binds = (actualHeader v' B checks).binds := by
  simp only [actualHeader, Term.binds_instantiate, HeaderScan.binds_closed]
  apply congrArg (fun n => (HistoryPartyHeader.formula checks).work + n)
  apply Finset.sum_congr rfl
  intro i _
  by_cases z : i = 0 <;> by_cases f : i = 5 <;> simp only [z, f, ite_true, ite_false] <;> rfl

private theorem static_batch_binds (v v' : ℕ) (A B : Layout) (cmd : Bool) :
    (batchTerm v A cmd).binds = (batchTerm v' B cmd).binds := by
  simp only [batchTerm, Term.binds_instantiate, HeaderScan.binds_closed]
  apply congrArg (fun n => (if cmd then HistoryBatchTape.rawCommand else HistoryBatchTape.rawArguments).work + n)
  apply Finset.sum_congr rfl
  intro i _
  fin_cases i <;> rfl

set_option maxRecDepth 16000 in
theorem staticCost_eq {w' : ℕ} (Y : Build w') (b : X.checks=Y.checks) : X.staticCost=Y.staticCost := by
  have seed : (seedFormula X.layout Y.checks).work = (seedFormula Y.layout Y.checks).work := rfl
  have result : (resultWord X.layout).work = (resultWord Y.layout).work := rfl
  simp only [staticCost, fixedTicks, perChild, headerCost, resultCost, HistoryPartyBootExec.bootCost,
    HeaderScan.binds_closed, b, seed, result, static_header_binds w w' X.layout Y.layout,
    static_batch_binds w w' X.layout Y.layout]

private theorem triples_length {α β : Type*} (g : α → List β) (size : ∀ i,(g i).length=3)
    (xs : List α) : (xs.flatMap g).length=3*xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [List.flatMap_cons,ih,size,Nat.mul_add,Nat.add_comm]

private theorem triple_at {α β : Type*} (g : α → List β) (size : ∀ i,(g i).length=3)
    (xs : List α) (i : Fin xs.length) (u : Fin 3) :
    (xs.flatMap g)[3*i.val+u.val]?=(g (xs.get i))[u.val]? := by
  induction xs with
  | nil => exact i.elim0
  | cons a xs ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [List.flatMap_cons,List.getElem?_append_left (show u.val<(g a).length by rw [size]; exact u.isLt)]
    · have idx : 3*j.succ.val+u.val=(g a).length+(3*j.val+u.val) := by rw [size]; simp [Nat.mul_add]; omega
      simpa only [List.flatMap_cons,idx,List.getElem?_append_right (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left,List.get_cons_succ'] using ih j

theorem loaded_groups (g : Fin X.count → List (HistoryReadyTape.Job w)) (size : ∀ i,(g i).length=3)
    (bounds : ∀ i (u : Fin 3), let j := (g i).get ⟨u.val,by rw [size]; exact u.isLt⟩
      HistoryBatchTape.command X.table i.val u 1=j.start ∧ HistoryBatchTape.command X.table i.val u 6=j.finish)
    (apart : X.layout.commands+21*X.count≤X.layout.arguments ∨ X.layout.arguments+23*X.count≤X.layout.commands) :
    HistoryReadyTape.Loaded X.layout.commands ((List.finRange X.count).flatMap g) X.tapeImage := by
  intro j
  have bound : j.val<3*X.count := by
    simpa only [triples_length g size,List.length_finRange] using j.isLt
  let i : Fin X.count := ⟨j.val/3,by omega⟩
  let u : Fin 3 := ⟨j.val%3,by omega⟩
  have pos : 3*i.val+u.val=j.val := by dsimp [i,u]; omega
  have ui : u.val<(g i).length := by rw [size]; exact u.isLt
  let i' : Fin (List.finRange X.count).length := ⟨i.val,by simp⟩
  have ident : (List.finRange X.count).get i'=i := by simp [i',List.get_eq_getElem]
  have e := triple_at g size (List.finRange X.count) i' u
  change ((List.finRange X.count).flatMap g)[3*i.val+u.val]? = _ at e
  rw [ident,pos,List.getElem?_eq_getElem j.isLt,List.getElem?_eq_getElem ui] at e
  have dj : ((List.finRange X.count).flatMap g).get j = (g i).get ⟨u.val,ui⟩ := Option.some.inj e
  rw [dj]
  obtain ⟨start,stop⟩ := bounds i u
  rw [←start,←stop]
  constructor
  · have a : X.layout.commands+7*j.val+1 = X.layout.commands+(21*i.val+(7*u.val+1)) := by omega
    rw [a]
    exact X.read_command i u 1 apart
  · have a : X.layout.commands+7*j.val+6 = X.layout.commands+(21*i.val+(7*u.val+6)) := by omega
    rw [a]
    exact X.read_command i u 6 apart

theorem scanned_outside (jobs : List (HistoryReadyTape.Job w)) (x : ℕ)
    (off : x≠X.ctrl.val) (away : ∀ J∈jobs, x<J.start ∨ J.finish≤x) :
    X.scanned jobs x = X.tapeImage x := by
  unfold scanned
  generalize X.tapeImage = m
  induction jobs generalizing m with
  | nil => rfl
  | cons j js ih =>
    rw [HistoryReadyTape.after,ih (fun J h => away J (by simp [h]))]
    have bad : ¬(j.start≤x ∧ x<j.start+j.count) := by
      have p := away j (by simp)
      unfold HistoryReadyTape.Job.finish at p
      omega
    simp [HistoryJoinController.bumpMemory,writeMemory,off,fillSegment,bad]

theorem tape_outside (x : ℕ) (room : X.layout.seed+37<2^w)
    (seed : x<X.layout.seed ∨ X.layout.seed+37≤x) (batch : x<X.layout.batch ∨ X.layout.batch+26≤x)
    (cmd : x<X.layout.commands ∨ X.layout.commands+21*X.count≤x)
    (arg : x<X.layout.arguments ∨ X.layout.arguments+23*X.count≤x) : X.tapeImage x=X.input x := by
  have ha : ¬(X.layout.arguments≤x ∧ x<X.layout.arguments+23*X.count) := by omega
  have hc : ¬(X.layout.commands≤x ∧ x<X.layout.commands+21*X.count) := by omega
  have hh : ¬(X.layout.batch≤x ∧ x<X.layout.batch+26) := by omega
  simp only [tapeImage,commandImage,headerImage,fillSegment,ite_eq_right ha,ite_eq_right hc,ite_eq_right hh]
  exact HistoryPartyBootExec.output_outside X.layout X.checks X.input room x seed


theorem published_outside (jobs : List (HistoryReadyTape.Job w)) (x : ℕ)
    (room : X.layout.seed+37<2^w) (off : x≠X.ctrl.val)
    (seed : x<X.layout.seed ∨ X.layout.seed+37≤x)
    (header : x<X.layout.batch ∨ X.layout.batch+26≤x)
    (cmd : x<X.layout.commands ∨ X.layout.commands+21*X.count≤x)
    (arg : x<X.layout.arguments ∨ X.layout.arguments+23*X.count≤x)
    (jobsAway : ∀ J∈jobs, x<J.start ∨ J.finish≤x)
    (info : x<X.target ∨ X.target+4≤x) :
    X.published jobs x=X.input x := by
  have hr : ¬(X.target≤x ∧ x<X.target+4) := by omega
  simp only [published,fillSegment,ite_eq_right hr,X.scanned_outside jobs x off jobsAway]
  have a : ¬(X.layout.arguments≤x ∧ x<X.layout.arguments+23*X.count) := by omega
  have c : ¬(X.layout.commands≤x ∧ x<X.layout.commands+21*X.count) := by omega
  have b : ¬(X.layout.batch≤x ∧ x<X.layout.batch+26) := by omega
  simp only [tapeImage,fillSegment,ite_eq_right a,commandImage,ite_eq_right c,headerImage,ite_eq_right b]
  exact HistoryPartyBootExec.output_outside X.layout X.checks X.input room x seed

private theorem seedWord (j : Fin 37) (room : X.layout.seed+37<2^w) (h2 : j.val≠2) (h3 : j.val≠3) :
    X.bootImage (X.layout.seed+j.val) = (seedWords X.layout X.checks (numeric X.input) j : Word w) := by
  rw [bootImage,HistoryPartyBootExec.output_at _ _ _ room,ite_eq_right (by omega),ite_eq_right (by omega)]
  exact HistoryPartyBootExec.seedMemory_at _ _ _ j

private theorem registerSeed (j : Fin 11) :
    seedWords X.layout X.checks (numeric X.input) ⟨4+j.val,by have := j.isLt; omega⟩=X.regs.words j := by
  fin_cases j <;> rfl

theorem registers_boot (j : Fin 11) (room : X.layout.seed+37<2^w) (fit : X.regs.words j<2^w) :
    numeric X.bootImage (X.layout.seed+4+j.val)=X.regs.words j := by
  let k : Fin 37 := ⟨4+j.val,by have := j.isLt; omega⟩
  have eq := X.seedWord k room (by dsimp [k]; omega) (by dsimp [k]; omega)
  change X.bootImage (X.layout.seed+(4+j.val))=(seedWords _ _ _ k : Word w) at eq
  rw [X.registerSeed j] at eq
  rw [numeric,Nat.add_assoc,eq,Fin.val_cast_of_lt fit]

/-- The three generated arrays lie in increasing disjoint intervals after the control words. -/
structure Ordered (X : Build w) : Prop where
  seed : X.layout.seed+37≤X.layout.batch
  header : X.layout.batch+26≤X.layout.commands
  commands : X.layout.commands+21*X.count≤X.layout.arguments

theorem seed_frames (ord : Ordered X) (x : ℕ) (bound : x<X.layout.seed+37) :
    X.headerImage x=X.bootImage x ∧ X.commandImage x=X.bootImage x ∧ X.tapeImage x=X.bootImage x := by
  have a := ord.seed
  have b := ord.header
  have c := ord.commands
  have h1 : ¬(X.layout.batch≤x ∧ x<X.layout.batch+26) := by omega
  have h2 : ¬(X.layout.commands≤x ∧ x<X.layout.commands+21*X.count) := by omega
  have h3 : ¬(X.layout.arguments≤x ∧ x<X.layout.arguments+23*X.count) := by omega
  simp only [headerImage,commandImage,tapeImage,fillSegment,ite_eq_right h1,ite_eq_right h2,ite_eq_right h3,and_self]

private theorem stageControl (m : Memory w) (room : X.layout.seed+37<2^w) (j : Fin 8)
    (h : m (X.layout.seed+28)=((X.layout.seed+29:ℕ):Word w)) :
    HeaderScan.headerWord m ((X.layout.seed+28 : ℕ):Word w) j.val = m (X.layout.seed+(29+j.val)) := by
  simp only [HeaderScan.headerWord,Fin.val_cast_of_lt (by omega : X.layout.seed+28<2^w),h,
    ←Nat.cast_add,Nat.add_assoc,Fin.val_cast_of_lt (by have := j.isLt; omega : X.layout.seed+(29+j.val)<2^w)]

theorem controls_at (m : Memory w) (room : X.layout.seed+37<2^w) (j : Fin 8)
    (root : m (X.layout.seed+28)=X.bootImage (X.layout.seed+28))
    (slot : m (X.layout.seed+(29+j.val))=X.bootImage (X.layout.seed+(29+j.val))) :
    HeaderScan.headerWord m ((X.layout.seed+28 : ℕ):Word w) j.val =
      (seedWords X.layout X.checks (numeric X.input) ⟨29+j.val,by have := j.isLt; omega⟩:Word w) := by
  have p := root.trans (X.seedWord 28 room (by decide) (by decide))
  rw [X.stageControl m room j p,slot]
  exact X.seedWord ⟨29+j.val, by have := j.isLt; omega⟩ room (by change 29+j.val≠2; omega) (by change 29+j.val≠3; omega)

theorem scanned_seed (jobs : List (HistoryReadyTape.Job w)) (ord : Ordered X)
    (room : X.layout.seed+37<2^w) (away : HistoryReadyTape.Away X.layout.seed 37 jobs)
    (k : ℕ) (small : k<37) (off : k≠33) :
    X.scanned jobs (X.layout.seed+k)=X.bootImage (X.layout.seed+k) := by
  have hc : X.ctrl.val = X.layout.seed+33 := Fin.val_cast_of_lt (by omega)
  have h := X.scanned_outside jobs (X.layout.seed+k) (by rw [hc]; omega)
    (fun J hJ => by rcases away J hJ with l|r <;> omega)
  exact h.trans (X.seed_frames ord _ (by omega)).2.2

theorem scanned_header (jobs : List (HistoryReadyTape.Job w)) (ord : Ordered X)
    (room : X.layout.seed+37<2^w) (away : HistoryReadyTape.Away X.layout.batch 26 jobs)
    (j : Fin 26) (bound : X.table.words j<2^w) :
    numeric (X.scanned jobs) (X.layout.batch+j.val)=X.table.words j := by
  let x := X.layout.batch+j.val
  have h0 := ord.seed
  have h1 := ord.header
  have h2 := ord.commands
  have below : x<X.layout.commands := by dsimp [x]; have := j.isLt; omega
  have fc : ¬(X.layout.commands≤x ∧ x<X.layout.commands+21*X.count) := by omega
  have fa : ¬(X.layout.arguments≤x ∧ x<X.layout.arguments+23*X.count) := by omega
  have hc : X.ctrl.val=X.layout.seed+33 := Fin.val_cast_of_lt (by omega)
  have e := X.scanned_outside jobs x (by rw [hc]; dsimp [x]; omega)
    (fun J hJ => by dsimp [x]; have := j.isLt; rcases away J hJ with a|b <;> omega)
  simp only [tapeImage,commandImage,fillSegment,ite_eq_right fc,ite_eq_right fa] at e
  change numeric (X.scanned jobs) x = _
  rw [numeric,e,X.read_header,Fin.val_cast_of_lt bound]

/-- Representability, disjoint row-expression probes, and concrete fields used by the
seven stages. The command decoder reads the complete emitted argument and command arrays. -/
structure Source (X : Build w) (jobs : List (HistoryReadyTape.Job w)) : Prop where
  seedRoom : X.layout.seed+37 < 2^w
  seedAway : ∀ x, HistoryPartyBootExec.SeedRead X.layout X.checks (numeric X.input) x →
    x<X.layout.seed ∨ X.layout.seed+37≤x
  motifRoom : X.layout.motif<2^w
  seedProbeRoom : ∀ x, HistoryPartyBootExec.SeedRead X.layout X.checks (numeric X.input) x → x<2^w
  partyRoom : X.layout.motif<numeric X.input (kernel X.layout (numeric X.input)+3) → 2^X.layout.party<2^w
  power : 2^Nat.clog 2 (HistoryPartyBootExec.extent X.layout (numeric X.input)) < 2^w
  registerRoom : ∀ j : Fin 11, X.regs.words j < 2^w
  gridRead : ∀ j : Fin 7, numeric X.bootImage (X.regs.grid+j.val)=X.kind.words j
  headerRoom : X.layout.batch+26 < 2^w
  headerProtected : HeaderProtected X.layout X.regs X.kind X.checks X.bootImage
  headerReadRoom : HistoryPartyHeader.ReadRoom w X.regs X.kind X.checks (numeric X.bootImage)
  wordSize : 23<2^w
  commandRoom : X.layout.commands+21*X.count<2^w
  argumentRoom : X.layout.arguments+23*X.count<2^w
  headerBound : ∀ j : Fin 26, X.table.words j<2^w
  order : Ordered X
  quotaRoom : X.table.checks=true → ∀ i : Fin X.count, X.table.r≤ i.val →
    X.table.hist+(i.val-X.table.r)<2^w ∧
      (X.table.hist+(i.val-X.table.r)<X.layout.arguments ∨
        X.layout.arguments+23*X.count≤X.table.hist+(i.val-X.table.r))
  awaySeed : HistoryReadyTape.Away X.layout.seed 37 jobs
  awayHeader : HistoryReadyTape.Away X.layout.batch 26 jobs
  awayCtrl : HistoryReadyTape.Away X.ctrl.val 2 jobs
  awayCmd : HistoryReadyTape.Away X.layout.commands (7*jobs.length) jobs
  resultRoom : X.target+4<2^w
  resultBefore : X.target+4≤X.layout.seed ∨ X.layout.batch+26≤X.target

theorem procedure_exec (jobs : List (HistoryReadyTape.Job w)) (s : Source X jobs)
    (numJobs : jobs.length=3*X.count) (jobRoom : ∀ J∈jobs, J.finish<2^w)
    (loaded : HistoryReadyTape.Loaded X.layout.commands jobs X.tapeImage)
    (drives : HistoryReadyTape.readJobs (scanExpr w) (fun _=>X.ctrl) X.ctrl jobs X.tapeImage) :
    (HistoryPartyBatch.procedure w X.layout X.checks).Exec X.input (X.published jobs) (X.cost jobs) := by
  let addr : Word w := ((X.layout.seed+28 : ℕ):Word w)
  have left : ((HistoryPartyBootExec.boot w X.layout X.checks).seq (dyadic w X.layout)).Exec
      X.input X.bootImage X.prefixCost := HistoryPartyBootExec.prefix_exec w X.layout X.checks X.input s.seedRoom s.seedAway
    (HistoryPartyBootExec.resident_fit X.layout X.checks X.input s.seedAway (fun j => HistoryPartyBootExec.seed_fits w X.layout X.checks X.input j s.seedRoom s.motifRoom s.seedProbeRoom s.partyRoom s.power)) s.power
  have head : (PhysicalInputPhases.writing (actualHeader w X.layout X.checks) Fin.elim0 X.layout.batch 26).Exec
      X.bootImage X.headerImage X.headerCost := header_exec X.layout X.regs X.kind X.checks X.bootImage
    (fun j => X.registers_boot j s.seedRoom (s.registerRoom j)) s.gridRead
    s.headerRoom s.seedRoom s.headerProtected s.headerReadRoom
  have hdr (j : Fin 26) : numeric X.headerImage (X.layout.batch+j.val)=X.table.words j := by
    rw [numeric,X.read_header,Fin.val_cast_of_lt (s.headerBound j)]
  have ch (j : Fin 8) := X.controls_at X.headerImage s.seedRoom j
    (X.seed_frames s.order (X.layout.seed+28) (by omega)).1
    (X.seed_frames s.order (X.layout.seed+(29+j.val)) (by have := j.isLt; omega)).1
  have ca (j : Fin 8) := X.controls_at X.commandImage s.seedRoom j
    (X.seed_frames s.order (X.layout.seed+28) (by omega)).2.1
    (X.seed_frames s.order (X.layout.seed+(29+j.val)) (by have := j.isLt; omega)).2.1
  have rRoom : X.table.r<2^w := s.headerBound 3
  have cmd : (HeaderScan.procedure addr 0 1 (batchTerm w X.layout true)).Exec
      X.headerImage X.commandImage X.cmdCost := commands_exec X.layout X.table X.count X.headerImage hdr (ch 0) (ch 1)
    (by have := s.wordSize; omega) s.commandRoom s.headerRoom rRoom s.order.header
  have hdr2 (j : Fin 26) : numeric X.commandImage (X.layout.batch+j.val)=X.table.words j := by
    have low : X.layout.batch+j.val < X.layout.commands := by have := s.order.header; have := j.isLt; omega
    simpa only [numeric,commandImage,fillSegment,ite_eq_right (by omega :
      ¬(X.layout.commands ≤ X.layout.batch+j.val ∧
        X.layout.batch+j.val<X.layout.commands+21*X.count))] using hdr j
  have arg : (HeaderScan.procedure addr 2 3 (batchTerm w X.layout false)).Exec
      X.commandImage X.tapeImage X.argCost := arguments_exec X.layout X.table X.count X.commandImage hdr2 (ca 2) (ca 3)
    s.wordSize s.argumentRoom s.headerRoom rRoom
    (by have := s.order.header; have := s.order.commands; omega) s.quotaRoom
  have len : 7*jobs.length=21*X.count := by rw [numJobs]; omega
  have vc : X.ctrl.val=X.layout.seed+33 := Fin.val_cast_of_lt (by have := s.seedRoom; omega)
  have vc' : (X.ctrl+1).val=X.layout.seed+34 := by
    rw [Fin.val_add_one_of_lt' (by rw [vc]; have := s.seedRoom; omega),vc,Nat.add_assoc]
  have cur := (X.seed_frames s.order (X.layout.seed+33) (by omega)).2.2.trans
    (X.seedWord 33 s.seedRoom (by decide) (by decide))
  have stop := (X.seed_frames s.order (X.layout.seed+34) (by omega)).2.2.trans
    (X.seedWord 34 s.seedRoom (by decide) (by decide))
  have tape : (HistoryReadyTape.execute (scanExpr w) (Fin.last 0) (fun _=>X.ctrl)).Exec
      X.tapeImage (X.scanned jobs) (HistoryReadyTape.cost (scanExpr w).binds jobs) := by
    intro P R K M pc reg pub exit installed params cfg m start init
    subst m
    exact HistoryReadyTape.execute_spec (scanExpr w) (Fin.last 0) (fun _=>X.ctrl)
      (fun m=>m=X.tapeImage) jobs X.layout.commands
      (by rw [vc]; have := s.order.seed; have := s.order.header; omega)
      (by rw [len]; exact s.commandRoom) s.awayCtrl s.awayCmd jobRoom (fun mem h => by
        subst mem
        exact ⟨by rw [vc]; exact cur,
          by rw [len,vc']; exact stop,loaded,drives⟩)
      M pc reg pub exit installed params cfg X.tapeImage start rfl
  have ss := X.scanned_seed jobs s.order s.seedRoom s.awaySeed
  have cr (j : Fin 8) (skip : 29+j.val≠33) := X.controls_at (X.scanned jobs) s.seedRoom j
    (ss 28 (by decide) (by decide)) (ss _ (by have := j.isLt; omega) skip)
  have targetRead : numeric (X.scanned jobs) (X.layout.seed+35)=X.target := by
    have posted : X.bootImage (X.layout.seed+35) = (X.target : Word w) :=
      X.seedWord (35 : Fin 37) s.seedRoom (by decide) (by decide)
    rw [numeric,ss 35 (by decide) (by decide),posted]
    exact Fin.val_cast_of_lt (by have := s.resultRoom; omega)
  have publish : (HeaderScan.procedure addr 6 7 (HeaderScan.closed (resultWord X.layout))).Exec
      (X.scanned jobs) (X.published jobs) X.resultCost := result_exec X.layout X.table X.target (X.scanned jobs) (fun j => X.scanned_header jobs s.order s.seedRoom s.awayHeader j (s.headerBound j)) targetRead
    (cr 6 (by decide)) (cr 7 (by decide)) s.resultRoom s.seedRoom s.headerRoom
    (by have := s.resultBefore; have := s.order.seed; omega)
    (by have := s.resultBefore; have := s.order.seed; omega)
  intro P R K M pc reg pub exit installed params cfg m start input
  exact Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then left head) cmd)
    (Procedure.Exec.then arg (Procedure.Exec.then tape publish))
    M pc reg pub exit installed params cfg m start input

/-- Unoccupied bounded roles execute empty instruction arrays. Their native charge has a fixed bound. -/
theorem inactive_exec (s : Source X []) (inactive : ¬occupied X.layout (numeric X.input)) :
    (HistoryPartyBatch.procedure w X.layout X.checks).Exec X.input (X.published []) X.staticCost ∧
    (∀ j : Fin 4, X.published [] (X.target+j.val)=((info X.table).words j:Word w)) := by
  have zero : X.count=0 := by simp [count,children,HistoryPartyBatch.copies,kinds,inactive]
  have run : (HistoryPartyBatch.procedure w X.layout X.checks).Exec X.input (X.published []) (X.cost []) :=
    X.procedure_exec [] s (by simp [zero]) (by simp) (fun j => j.elim0) True.intro
  have size := X.cost_le [] (by simp [zero])
  have ext : HistoryPartyBootExec.extent X.layout (numeric X.input)=0 := by
    simp [HistoryPartyBootExec.extent,HistoryPartyBatch.copies,digit,inactive]
  have cost : X.cost []≤X.staticCost := by simpa [zero,ext] using size
  exact ⟨Procedure.Spec.mono run (fun _=>id) (fun _ _=>id) cost,X.read_info []⟩

private theorem loaded_count {n : ℕ} (hn : n=X.count) (g : Fin n → List (HistoryReadyTape.Job w))
    (size : ∀ i,(g i).length=3)
    (bounds : ∀ i (u : Fin 3), let j := (g i).get ⟨u.val,by rw [size]; exact u.isLt⟩
      HistoryBatchTape.command X.table i.val u 1=j.start ∧ HistoryBatchTape.command X.table i.val u 6=j.finish)
    (ord : Ordered X) : HistoryReadyTape.Loaded X.layout.commands ((List.finRange n).flatMap g) X.tapeImage := by
  subst n
  exact X.loaded_groups g size bounds (Or.inl ord.commands)

theorem generated_banks (ord : Ordered X) (hc : X.table.r+X.table.s=X.count) :
    HistoryPartyTapeRun.Banks X.table X.layout.commands (numeric X.commandImage) X.tapeImage := by
  constructor
  · intro i j a
    simpa only [Fin.val_cast, Nat.add_assoc] using X.read_command (i.cast hc) j a (Or.inl ord.commands)
  · intro i a
    change X.tapeImage (X.layout.arguments+23*i.val+a.val)=_
    simpa only [Fin.val_cast, Nat.add_assoc] using X.read_operand (i.cast hc) a

section Typed
open HistoryPartyTapeRun HistoryCompiledRows
variable {F : Type*} [CommRing F] [Fintype F] {z B D p h : ℕ}
variable {arity : Fin (X.table.r+X.table.s)→ℕ} (N : ∀ i,BitNetwork F (arity i))
    (wire : ∀ i,Fin (arity i)→BitSource h p) (id : ((Fin 3→Bool)→F)→ℕ)
    (L : HistoryStaticArchive.Catalog F z B) (page : Fin z) (power : Fin (D+1))
    (logical fixedBase compactBase : ℕ)

/-- The permanent table banks precede the stage scratch and are retained by all
four preparations before the generated tape is fetched. -/
theorem archive_at_tape (ord : Ordered X) (room : X.layout.seed+37<2^w)
    (initial : Archive id L (D:=D) fixedBase compactBase X.input)
    (lutAway : fixedBase+HistoryStaticArchive.size z B≤X.layout.seed ∨
      X.layout.arguments+23*X.count≤fixedBase)
    (compactAway : compactBase+StableCompactROMNative.size D≤X.layout.seed ∨
      X.layout.arguments+23*X.count≤compactBase) :
    Archive id L (D:=D) fixedBase compactBase X.tapeImage := by
  have keep (x : ℕ) (outside : x<X.layout.seed ∨ X.layout.arguments+23*X.count≤x) : X.tapeImage x=X.input x := by
    have := ord.seed
    have := ord.header
    have := ord.commands
    exact X.tape_outside x room (by omega) (by omega) (by omega) (by omega)
  constructor
  · intro j
    exact (keep _ (by have := j.isLt;omega)).trans (initial.fixed j)
  · intro j
    exact (keep _ (by have := j.isLt;omega)).trans (initial.compact j)

theorem models_at_commands (ord : Ordered X)
    (model : Models X.table N wire id L page power logical fixedBase compactBase (numeric X.bootImage))
    (quotas : X.table.checks=true → 0<X.table.s → X.table.hist+X.table.s≤X.layout.batch ∨
      X.layout.commands+21*X.count≤X.table.hist) :
    Models X.table N wire id L page power logical fixedBase compactBase (numeric X.commandImage) := by
  refine ⟨model.lut,model.comp,model.small,model.leftSize,model.leftRows,model.rightSize,model.rightRows,?_⟩
  intro i x
  have same : quotaAt X.table (numeric X.commandImage) i.val=quotaAt X.table (numeric X.bootImage) i.val := by
    unfold quotaAt
    by_cases reads : X.table.checks=true ∧ ¬i.val<X.table.r
    · rw [ite_eq_left reads,ite_eq_left reads]
      have idx : partAt X.table i.val<X.table.s := by
        rw [partAt,ite_eq_right reads.2]; have := i.isLt; omega
      have region := quotas reads.1 (by omega)
      have h := ord.header
      simp only [numeric,commandImage,headerImage,fillSegment,
        ite_eq_right (by omega : ¬(X.layout.commands≤X.table.hist+partAt X.table i.val ∧
          X.table.hist+partAt X.table i.val<X.layout.commands+21*X.count)),
        ite_eq_right (by omega : ¬(X.layout.batch≤X.table.hist+partAt X.table i.val ∧ X.table.hist+partAt X.table i.val<X.layout.batch+26))]
    · rw [ite_eq_right reads,ite_eq_right reads]
  rw [same]
  exact model.mapWords i x

omit [CommRing F] [Fintype F] in
theorem total_job_words :
    (((HistoryPartyTapeRun.jobs (w:=w) X.table N wire id)).map HistoryReadyTape.Job.count).sum =
      8*(X.table.r*X.table.left.rows+X.table.s*X.table.right.rows)+X.table.r*X.table.left.arity+X.table.s*X.table.right.arity := by
  let f (i : Fin (X.table.r+X.table.s)) :=
    if i.val<X.table.r then 8*X.table.left.rows+X.table.left.arity else 8*X.table.right.rows+X.table.right.arity
  have add (i : Fin (X.table.r+X.table.s)) :
      ((group (w:=w) X.table N wire id i).map HistoryReadyTape.Job.count).sum = f i := by
    change (X.table.row i.val).count + (X.table.arity i.val + ((X.table.row i.val).count + 0)) = _
    dsimp only [HistoryBatchTape.Header.row,HistoryBatchTape.Header.arity,BatchRows.record,f]
    split <;> ring
  have flatten (xs : List (Fin (X.table.r+X.table.s))) :
      ((xs.flatMap (group (w:=w) X.table N wire id)).map HistoryReadyTape.Job.count).sum=(xs.map f).sum := by
    induction xs with
    | nil => rfl
    | cons i xs ih => simp [List.flatMap_cons,add,ih]
  rw [jobs,flatten,←Fin.sum_univ_def,Fin.sum_univ_add]
  have left (i : Fin X.table.r) : f (Fin.castAdd X.table.s i)=8*X.table.left.rows+X.table.left.arity := ite_eq_left i.isLt
  have right (i : Fin X.table.s) : f (Fin.natAdd X.table.r i)=8*X.table.right.rows+X.table.right.arity :=
    ite_eq_right (by change ¬X.table.r+i.val<X.table.r; omega)
  simp only [left,right,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  ring

omit [CommRing F] [Fintype F] in
theorem typed_cost_le (hc : X.table.r+X.table.s=X.count) :
    X.cost (HistoryPartyTapeRun.jobs (w:=w) X.table N wire id) ≤ X.staticCost*(1+Nat.clog 2 (HistoryPartyBootExec.extent X.layout (numeric X.input))+
      X.count+(8*(X.table.r*X.table.left.rows+X.table.s*X.table.right.rows)+X.table.r*X.table.left.arity+X.table.s*X.table.right.arity)) := by
  rw [←X.total_job_words N wire id]
  apply X.cost_le
  rw [jobs_length,hc]

theorem complete (s : Source X (HistoryPartyTapeRun.jobs (w:=w) X.table N wire id)) (hc : X.table.r+X.table.s=X.count)
    (model : Models X.table N wire id L page power logical fixedBase compactBase (numeric X.bootImage))
    (quotas : X.table.checks=true → 0<X.table.s → X.table.hist+X.table.s≤X.layout.batch ∨
      X.layout.commands+21*X.count≤X.table.hist)
    (shape : HistoryPartyTapeRun.Shape (p:=p) (h:=h) X.table N)
    (space : Space (z:=z) (B:=B) (D:=D) X.table N wire id fixedBase compactBase X.ctrl X.layout.commands)
    (archive : Archive (D:=D) id L fixedBase compactBase X.tapeImage)
    (work : StableCompactNativeBudget.budget power<2^w)
    (pins : ∀ i : Fin (X.table.r+X.table.s),2+arity i<2^w)
    (small : ∀ i (r : Fin (N i).cells) j,metadata id (N i) r j<2^w)
    (side : X.table.e*X.table.d<2^w) (stripe : X.table.r*X.table.d<2^w)
    (placed : ∀ i,(X.table.row i.val).dest=(info X.table).stream+4*before (fun i=>(N i).cells) i)
    (infoDisjoint : X.target+4 ≤ (info X.table).stream ∨ (info X.table).stream+4*(glue N wire).cells≤X.target) :
    (HistoryPartyBatch.procedure w X.layout X.checks).Exec X.input (X.published (HistoryPartyTapeRun.jobs (w:=w) X.table N wire id)) (X.cost (HistoryPartyTapeRun.jobs (w:=w) X.table N wire id)) ∧
    (∀ j : Fin 4, X.published (HistoryPartyTapeRun.jobs (w:=w) X.table N wire id) (X.target+j.val)=((info X.table).words j:Word w)) ∧
    Records id (glue N wire) (info X.table).stream (X.published (HistoryPartyTapeRun.jobs (w:=w) X.table N wire id)) := by
  have mount : Mount X.table id L (D:=D) fixedBase compactBase X.layout.commands
      (numeric X.commandImage) X.tapeImage := ⟨X.generated_banks s.order hc,archive⟩
  have vc : X.ctrl.val=X.layout.seed+33 := Fin.val_cast_of_lt (by have := s.seedRoom; omega)
  have cur : X.tapeImage X.ctrl.val=(X.layout.commands:Word w) := by
    rw [vc]
    exact (X.seed_frames s.order _ (by omega)).2.2.trans (X.seedWord 33 s.seedRoom (by decide) (by decide))
  have mapFit (i : Fin (X.table.r+X.table.s)) (x : Fin (arity i)) (d : ℕ) (m : ℕ→ℕ) :
      HistoryMotifMaps.formula.Fits w (fun _=>d) m (mapRegs X.table (numeric X.commandImage) i.val x.val) := by
    apply HistoryMotifMaps.fits_values
    · have := s.wordSize; omega
    · have := pins i; have := x.isLt; omega
    · exact s.headerBound 3
    · exact s.headerBound 14
    · exact s.headerBound 16
    · exact side
    · exact stripe
    · unfold quotaAt
      split
      · exact (X.commandImage _).isLt
      · exact Nat.two_pow_pos w
  have reads := read_jobs X.table N wire id L page power logical fixedBase compactBase
    (.literal (0:Word w) : Term w 0 4) [] (fun _ => X.ctrl)
    (X.models_at_commands N wire id L page power logical fixedBase compactBase s.order model quotas) shape space
    (by simp; have := s.wordSize; omega) work pins small mapFit X.tapeImage mount cur
  have loaded := X.loaded_count hc (group X.table N wire id) (group_length X.table N wire id)
    (group_bounds X.table N wire id) s.order
  refine ⟨X.procedure_exec (HistoryPartyTapeRun.jobs (w:=w) X.table N wire id) s (by rw [jobs_length,hc]) space.finishes loaded reads,X.read_info (HistoryPartyTapeRun.jobs (w:=w) X.table N wire id),?_⟩
  have copied := records_after (z:=z) (B:=B) (D:=D) X.table N wire id fixedBase compactBase
    shape space (info X.table).stream placed X.tapeImage
  intro i j
  have bound : 4*i.val+j.val<4*(glue N wire).cells := by have := i.isLt; have := j.isLt; omega
  have off : ¬(X.target ≤ (info X.table).stream+(4*i.val+j.val) ∧
      (info X.table).stream+(4*i.val+j.val)<X.target+4) := by omega
  simpa only [published,fillSegment,ite_eq_right off,scanned] using copied i j


end Typed


end Build


end ThreeFlat.RAM.HistoryPartyBatchExec

end OAI
