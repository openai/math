import OAI.Hierarchy.TraceResourceTails
import OAI.ThreeFlat.RAM.PhysicalPinsNat
import OAI.ThreeFlat.RAM.TerminalWireArchive

namespace OAI
/-! # Native publication of work, input-bit lengths, and external-pair direction counts

The first pass sweeps a row for every initial interval, in descending interval
order. Each entry includes its successor's previously written total. The second
pass reads the head of each terminal factor's list and the charge of its
physical archive node, producing the row consumed by geometric registration.
-/

namespace Hierarchy.TraceAdmission.Resources

open ThreeFlat Diagonal
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure RAM.PhysicalPinsExpr
open scoped Classical Fin.CommRing

structure Parameters (α : Type) where
  lanes : α
  roots : α
  directions : α
  pairSpan : α
  band : α
  cap : α
  heads : α
  links : α
  scratch : α
  resources : α
  charges : α
  firstFinal : α

def Parameters.map {α β : Type} (f : α → β) (p : Parameters α) : Parameters β :=
  ⟨f p.lanes,f p.roots,f p.directions,f p.pairSpan,f p.band,f p.cap,
   f p.heads,f p.links,f p.scratch,f p.resources,f p.charges,f p.firstFinal⟩

private abbrev Expr := Formula 1
private abbrev plus (x y : Expr) := Formula.op .add x y
private abbrev times (x y : Expr) := Formula.op .mul x y
private abbrev quotient (x y : Expr) := Formula.op .div x y
private abbrev remainder (x y : Expr) := Formula.op .mod x y
private abbrev minimum (x y : Expr) := Formula.select .lt x y x y
private abbrev maximum (x y : Expr) := Formula.select .lt x y y x

/-- Header cells 0..3 give the two base/lengths; cells 4..15 give the
numeric scanner parameters. The same instruction array serves all sizes. -/
def fields (control : ℕ) : Parameters Expr :=
  let q (i : ℕ) : Expr := .load (plus (.load (.lit control)) (.lit i))
  ⟨q 4,q 5,q 6,q 7,q 8,q 9,q 10,q 11,q 12,q 13,q 14,q 15⟩

def pointerRow (lanes ptr : Expr) : Expr :=
  .select .eq ptr (.lit 0) (.lit 0) (.cut (plus lanes (.lit 1)) ptr)

def scratchExpr (p : Parameters Expr) : Expr :=
  let offset := Formula.cut (.reg 0) p.scratch
  let stride := plus p.directions (.lit 1)
  let row := quotient offset stride
  let col := remainder offset stride
  let q := Formula.cut p.lanes row
  let lo := times q p.pairSpan
  let hi := plus lo p.pairSpan
  let left := times (.cut col (.lit 1)) p.band
  let right := times col p.band
  let bits := minimum (times (.lit 2) p.pairSpan) (.cut p.cap (times (.lit 2) lo))
  let pairs := Formula.cut (minimum hi right) (maximum lo left)
  let localValue := Formula.select .eq col (.lit 0) bits pairs
  let tail := pointerRow p.lanes (.load (plus p.links q))
  let address := plus (plus p.scratch (times tail stride)) col
  .select .eq row (.lit 0) (.lit 0) (plus localValue (.load address))

def resourceExpr (p : Parameters Expr) : Expr :=
  let offset := Formula.cut (.reg 0) p.resources
  let stride := plus p.directions (.lit 2)
  let root := quotient offset stride
  let col := remainder offset stride
  let charged := plus p.charges (times (.lit 2) (plus p.firstFinal root))
  let head := pointerRow p.lanes (.load (plus p.heads root))
  let addr := plus (plus p.scratch (times head (plus p.directions (.lit 1)))) (.cut col (.lit 1))
  .select .eq col (.lit 0) (.load charged) (.load addr)

def ptrRow (lanes ptr : ℕ) := if ptr=0 then 0 else lanes+1-ptr

def laneValue (p : Parameters ℕ) (q col : ℕ) :=
  if col=0 then min (2*p.pairSpan) (p.cap-2*(q*p.pairSpan))
  else min (q*p.pairSpan+p.pairSpan) (col*p.band) - max (q*p.pairSpan) ((col-1)*p.band)

def scratchValue (p : Parameters ℕ) (m : ℕ → ℕ) (a : ℕ) :=
  let row := (a-p.scratch)/(p.directions+1)
  let col := (a-p.scratch)%(p.directions+1)
  let q := p.lanes-row
  let tail := ptrRow p.lanes (m (p.links+q))
  if row=0 then 0 else laneValue p q col + m (p.scratch+tail*(p.directions+1)+col)

def resourceValue (p : Parameters ℕ) (m : ℕ → ℕ) (a : ℕ) :=
  let root := (a-p.resources)/(p.directions+2)
  let col := (a-p.resources)%(p.directions+2)
  let head := ptrRow p.lanes (m (p.heads+root))
  if col=0 then m (p.charges+2*(p.firstFinal+root))
  else m (p.scratch+head*(p.directions+1)+(col-1))

theorem laneValue_bits (p : Parameters ℕ) (q : ℕ) :
    laneValue p q 0=FactorPinIntervals.bucketLength p.cap (2*p.pairSpan) q := by
  simp [laneValue,FactorPinIntervals.bucketLength,Nat.mul_comm,Nat.mul_assoc]

theorem laneValue_direction (p : Parameters ℕ) (q i : ℕ) :
    laneValue p q (i+1)=bandLength p.pairSpan q (i*p.band) ((i+1)*p.band) := by
  rw [bandLength_eq _ _ _ _ (Nat.mul_le_mul_right _ (Nat.le_succ _))]
  simp [laneValue,Nat.succ_mul,min_comm,max_comm]

def natEval (w : ℕ) (m : ℕ → ℕ) (a : ℕ) (f : Expr) :=
  f.natural w (fun _=>0) m (fun _=>a)

section
variable (w : ℕ) (m : ℕ→ℕ) (a : ℕ)
local notation "E" => natEval w m a

private theorem reg_eval (i : Fin 1) : E (.reg i)=a := rfl
private theorem lit_eval (i : ℕ) : E (.lit i)=i := rfl
private theorem load_eval (x : Expr) : E (.load x)=m (E x) := rfl
private theorem op_eval (op : BinaryOp) (x y : Expr) : E (.op op x y)=natOp w op (E x) (E y) := rfl
private theorem cut_eval (x y : Expr) : E (.cut x y)=E x-E y := rfl

private theorem eq_eval (x y left right : Expr) :
    E (.select .eq x y left right)=(if E x=E y then E left else E right) := by
  change (if natTest .eq (E x) (E y) then E left else E right)=_
  by_cases h : E x=E y <;> simp [natTest,h]

private theorem lt_eval (x y left right : Expr) :
    E (.select .lt x y left right)=(if E x<E y then E left else E right) := by
  change (if natTest .lt (E x) (E y) then E left else E right)=_
  by_cases h : E x<E y <;> simp [natTest,h]
end

private noncomputable def chooseNat (p : Prop) (yes no : ℕ) : ℕ :=
  @ite ℕ p (Classical.propDecidable p) yes no

private theorem ite_chooseNat (p : Prop) (d : Decidable p) (yes no : ℕ) :
    @ite ℕ p d yes no=chooseNat p yes no :=
  congrArg (fun dec : Decidable p => @ite ℕ p dec yes no) (Subsingleton.elim _ _)

set_option maxHeartbeats 800000 in
set_option pp.all true in
theorem eval_scratch (p : Parameters Expr) (w : ℕ) (m : ℕ → ℕ) (a : ℕ) :
    natEval w m a (scratchExpr p)=scratchValue (p.map (natEval w m a)) m a := by
  simp only [scratchExpr,scratchValue,laneValue,ptrRow,pointerRow,plus,times,minimum,maximum,
    quotient,remainder,Parameters.map,min_def_lt,max_def_lt,eq_eval,lt_eval,reg_eval,lit_eval,
    load_eval,op_eval,cut_eval,natOp]
  first
  | solve | simp only [ite_chooseNat]
  | solve | congr!

set_option pp.all true in
theorem eval_resource (p : Parameters Expr) (w : ℕ) (m : ℕ → ℕ) (a : ℕ) :
    natEval w m a (resourceExpr p)=resourceValue (p.map (natEval w m a)) m a := by
  simp only [resourceExpr,resourceValue,ptrRow,pointerRow,plus,times,quotient,remainder,
    Parameters.map,eq_eval,reg_eval,lit_eval,load_eval,op_eval,cut_eval,natOp]
  first
  | solve | simp only [ite_chooseNat]
  | solve | congr!

def scratchPass (w control : ℕ) : Procedure w :=
  HeaderScan.procedure (control:Word w) 0 1 (HeaderScan.closed (scratchExpr (fields control)))

def resourcePass (w control : ℕ) : Procedure w :=
  HeaderScan.procedure (control:Word w) 2 3 (HeaderScan.closed (resourceExpr (fields control)))

private theorem eval_word {w : ℕ} (mem : Memory w) (a : ℕ) (f : Expr)
    (fit : f.Fits w (fun _=>0) (fun i=>(mem i).val) (fun _=>a)) :
    (HeaderScan.closed f).eval Fin.elim0 mem (fun _=>(a:Word w))=
      (natEval w (fun i=>(mem i).val) a f : Word w) := by
  rw [HeaderScan.eval_closed]
  simpa only [Nat.cast_zero,Fin.cast_val_eq_self,natEval] using
    f.value_eq_natural (w:=w) (fun _=>0) (fun i=>(mem i).val) (fun _=>a) fit

/-- The actual linked procedure executes either numerical scan, reading its
prior generated scratch cells before emitting the next word. -/
private theorem scan_spec {w : ℕ} (control start count lo n : ℕ) (f : Expr)
    (m : Memory w) (image : ℕ → Word w) (room : lo+n<2^w)
    (base : (HeaderScan.headerWord m (control:Word w) start).val=lo)
    (len : (HeaderScan.headerWord m (control:Word w) count).val=n)
    (step : ∀ i<n,
      let raw := fun j=>(fillSegment lo i image m j).val
      f.Fits w (fun _=>0) raw (fun _=>lo+i) ∧ (natEval w raw (lo+i) f : Word w)=image (lo+i)) :
    (HeaderScan.procedure (control:Word w) start count (HeaderScan.closed f)).Spec (·=m)
      (fun _ output=>output=fillSegment lo n image m) (11+n*(2*f.work+4)) := by
  rw [← HeaderScan.binds_closed (w:=w) f]
  apply HeaderScan.prefix_spec _ _ _ _ _ _ _ _ room base len
  intro i hi
  exact (eval_word _ _ _ (step i hi).1).trans (step i hi).2

/-- The fixed first pass issues the cumulative linked-list array in increasing
physical addresses, with its sentinel row first. -/
theorem scratchPass_spec {w : ℕ} (control : ℕ) (p : Parameters ℕ) (m : Memory w)
    (n : ℕ) (room : p.scratch+n<2^w)
    (lo : (HeaderScan.headerWord m (control:Word w) 0).val=p.scratch)
    (len : (HeaderScan.headerWord m (control:Word w) 1).val=n)
    (image : ℕ → Word w)
    (step : ∀ i<n, let raw := fun j=>(fillSegment p.scratch i image m j).val
      (scratchExpr (fields control)).Fits w (fun _=>0) raw (fun _=>p.scratch+i) ∧
      (fields control).map (natEval w raw (p.scratch+i))=p ∧
      (scratchValue p raw (p.scratch+i) : Word w)=image (p.scratch+i)) :
    (scratchPass w control).Spec (·=m) (fun _ out=>out=fillSegment p.scratch n image m)
      (11+n*(2*(scratchExpr (fields control)).work+4)) := by
  apply scan_spec _ _ _ _ _ _ _ _ room lo len
  intro i hi
  obtain ⟨fits,params,read⟩ := step i hi
  exact ⟨fits,by rw [eval_scratch,params];exact read⟩

/-- Release columns 0..k+1 in the allocator's physical row-major ABI. -/
theorem resourcePass_spec {w : ℕ} (control : ℕ) (p : Parameters ℕ) (m : Memory w)
    (n : ℕ)
    (room : p.resources+n<2^w)
    (lo : (HeaderScan.headerWord m (control:Word w) 2).val=p.resources)
    (len : (HeaderScan.headerWord m (control:Word w) 3).val=n)
    (image : ℕ → Word w)
    (step : ∀ i<n, let raw := fun j=>(fillSegment p.resources i image m j).val
      (resourceExpr (fields control)).Fits w (fun _=>0) raw (fun _=>p.resources+i) ∧
      (fields control).map (natEval w raw (p.resources+i))=p ∧
      (resourceValue p raw (p.resources+i) : Word w)=image (p.resources+i)) :
    (resourcePass w control).Spec (·=m) (fun _ out=>out=fillSegment p.resources n image m)
      (11+n*(2*(resourceExpr (fields control)).work+4)) := by
  apply scan_spec _ _ _ _ _ _ _ _ room lo len
  intro i hi
  obtain ⟨fits,params,read⟩ := step i hi
  exact ⟨fits,by rw [eval_resource,params];exact read⟩

/-- Both instruction arrays have constant size, independent of the dimensions
and the selector. The whole two-pass registration takes linear time in the
explicit scratch and output array lengths. -/
def ticks (control : ℕ) (p : Parameters ℕ) :=
  11+(p.lanes+1)*(p.directions+1)*(2*(scratchExpr (fields control)).work+4) +
  (11+p.roots*(p.directions+2)*(2*(resourceExpr (fields control)).work+4))

theorem ticks_bound (control : ℕ) (p : Parameters ℕ) :
    ticks control p ≤ 22+(p.lanes+1+p.roots)*(p.directions+2)*
      (2*max (scratchExpr (fields control)).work (resourceExpr (fields control)).work+4) := by
  let A := 2*max (scratchExpr (fields control)).work (resourceExpr (fields control)).work+4
  have left : 2*(scratchExpr (fields control)).work+4 ≤ A := by dsimp [A]; omega
  have right : 2*(resourceExpr (fields control)).work+4 ≤ A := by dsimp [A]; omega
  unfold ticks
  calc
    _ ≤ 11+(p.lanes+1)*(p.directions+2)*A + (11+p.roots*(p.directions+2)*A) := by gcongr; omega
    _ = _ := by ring

theorem resource_index (p : Parameters ℕ) (m : ℕ→ℕ) (v col : ℕ) (hc : col<p.directions+2) :
    resourceValue p m (p.resources+v*(p.directions+2)+col) =
      if col=0 then m (p.charges+2*(p.firstFinal+v)) else
        m (p.scratch+ptrRow p.lanes (m (p.heads+v))*(p.directions+1)+(col-1)) := by
  have sub : p.resources+v*(p.directions+2)+col-p.resources=v*(p.directions+2)+col := by omega
  have hl : 0 < p.directions+2 := by omega
  have div : (v*(p.directions+2)+col)/(p.directions+2)=v := by
    rw [Nat.mul_comm v, Nat.mul_add_div hl,Nat.div_eq_of_lt hc,Nat.add_zero]
  simp [resourceValue,sub,div,Nat.mul_add_mod_of_lt hc]

/-- If the charged-node and cumulative tables have been issued, the numerical
operands delivered to geometric registration are exactly the physical factor
work, input lengths, and counts in the original pair-direction bands. -/
theorem resource_readback {W lanes roots H N : ℕ} (p : Parameters ℕ) (v : Fin roots)
    (dest : Fin lanes→Fin roots) (m linked : Memory W) (store : ℕ→ℕ)
    (ready : TraceIntervalScanner.Output H N dest m linked)
    (mass : Fin roots→ℕ) (hl : p.lanes=lanes) (hh : p.heads=H)
    (work : store (p.charges+2*(p.firstFinal+v.val))=mass v)
    (head : store (H+v.val)=(linked (H+v.val)).val)
    (totals : ∀ i≤p.directions, ∀ r≤lanes,
      store (p.scratch+r*(p.directions+1)+i) =
        cumulative lanes (fun q=>(linked (N+q)).val) (fun q=>laneValue p q i) r) :
    resourceValue p store (p.resources+v.val*(p.directions+2))=mass v ∧
    resourceValue p store (p.resources+v.val*(p.directions+2)+1)=
      inputCount dest v p.cap p.pairSpan ∧
    ∀ i<p.directions, resourceValue p store (p.resources+v.val*(p.directions+2)+(2+i))=
      directionCount dest v p.band p.pairSpan i := by
  have collect (i : ℕ) (hi : i≤p.directions) :
      store (p.scratch+ptrRow p.lanes (store (p.heads+v.val))*(p.directions+1)+i)=
        rootSum dest v (fun q=>laneValue p q i) := by
    rw [hh,hl,head,ptrRow]
    have fit : (if (linked (H+v.val)).val=0 then 0 else lanes+1-(linked (H+v.val)).val)≤lanes := by
      split <;> omega
    exact (totals i hi _ fit).trans (cumulative_root ready v _)
  constructor
  · have zero := resource_index p store v.val 0 (by omega)
    simpa using zero.trans (by simpa using work)
  constructor
  · rw [resource_index p store v.val 1 (by omega)]
    have weights : (fun q=>laneValue p q 0)=FactorPinIntervals.bucketLength p.cap (2*p.pairSpan) :=
      funext (laneValue_bits p)
    simpa only [ite_false,Nat.one_ne_zero,Nat.sub_self,inputCount,weights] using collect 0 (by omega)
  · intro i hi
    rw [resource_index p store v.val (2+i) (by omega)]
    simpa [show 2+i-1=i+1 by omega,directionCount,laneValue_direction] using collect (i+1) (by omega)

def scratchWord {W : ℕ} (p : Parameters ℕ) (m : Memory W) (a : ℕ) : Word W :=
  let off := a-p.scratch
  let stride := p.directions+1
  (cumulative p.lanes (fun q=>(m (p.links+q)).val)
    (fun q=>laneValue p q (off%stride)) (off/stride) : Word W)

/-- A nonempty row points strictly backwards in the scratch array. This
establishes the real read-after-write recurrence for the first native pass,
even if arbitrarily large cumulative values are represented modulo the word size. -/
theorem scratchWord_step {W : ℕ} (p : Parameters ℕ) (m : Memory W)
    (apart : p.links+p.lanes≤p.scratch)
    (forward : ∀ j<p.lanes, let h := (m (p.links+j)).val
      h=0 ∨ j+1<h ∧ h≤p.lanes)
    (i : ℕ) (hi : i<(p.lanes+1)*(p.directions+1)) :
    let mem := fillSegment p.scratch i (scratchWord p m) m
    (scratchValue p (fun z=>(mem z).val) (p.scratch+i) : Word W) =
      scratchWord p m (p.scratch+i) := by
  intro mem
  let stride := p.directions+1
  let r := i/stride
  let col := i%stride
  have hs : 0<stride := Nat.succ_pos _
  have bound : r<p.lanes+1 := (Nat.div_lt_iff_lt_mul hs).mpr hi
  have decomp : col+r*stride=i := by simpa [r,col,Nat.mul_comm] using Nat.mod_add_div i stride
  have rem : col<stride := Nat.mod_lt _ hs
  let q := p.lanes-r
  let ptr := (m (p.links+q)).val
  let t := ptrRow p.lanes ptr
  change (scratchValue p (fun z=>(mem z).val) _ : Word W)=_
  unfold scratchValue scratchWord
  simp only [Nat.add_sub_cancel_left]
  change ((if r=0 then 0 else laneValue p q col+
      (mem (p.scratch+ptrRow p.lanes (mem (p.links+q)).val*stride+col)).val : ℕ) : Word W)=
    (cumulative p.lanes (fun j=>(m (p.links+j)).val) (fun j=>laneValue p j col) r : Word W)
  rw [cumulative]
  by_cases hz : r=0
  · simp only [hz,ite_true,Nat.cast_zero]
  have posR := Nat.pos_of_ne_zero hz
  have hq : q<p.lanes := Nat.sub_lt (posR.trans_le (Nat.le_of_lt_succ bound)) posR
  have next : (mem (p.links+q)).val=ptr := by
    simp [mem,fillSegment,ptr,show ¬p.scratch≤p.links+q by omega]
  have earlier : t<r := by
    rcases forward q hq with z|⟨gt,valid⟩
    · change ptr=0 at z
      simp [t,ptrRow,z,Nat.pos_of_ne_zero hz]
    · change q+1<ptr at gt
      change ptr≤p.lanes at valid
      dsimp [t,ptrRow,q] at *
      split <;> omega
  have prev : t*stride+col < i := by
    have mul := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt earlier)
    rw [Nat.succ_mul] at mul
    omega
  have word : mem (p.scratch+t*stride+col)=
      (cumulative p.lanes (fun j=>(m (p.links+j)).val) (fun j=>laneValue p j col) t : Word W) := by
    have sub : p.scratch+t*stride+col-p.scratch=t*stride+col := by omega
    simp only [mem,fillSegment,show p.scratch≤p.scratch+t*stride+col by omega,
      show p.scratch+t*stride+col<p.scratch+i by omega,and_self,ite_true,scratchWord,sub]
    change (cumulative _ _ (fun j=>laneValue p j ((t*stride+col)%stride))
      ((t*stride+col)/stride) : Word W)=_
    rw [Nat.mul_add_mod_of_lt rem,Nat.mul_comm t stride,Nat.mul_add_div hs,Nat.div_eq_of_lt rem,Nat.add_zero]
  simp only [ite_eq_right hz,next]
  change ((laneValue p q col+(mem (p.scratch+t*stride+col)).val : ℕ) : Word W) =
    ((laneValue p q col + (if _ : t<r then cumulative p.lanes (fun j=>(m (p.links+j)).val)
      (fun j=>laneValue p j col) t else 0) : ℕ) : Word W)
  rw [dite_eq_left earlier,word]
  simp
  apply Fin.ext
  exact Nat.mod_mod _ _

end Hierarchy.TraceAdmission.Resources

end OAI
