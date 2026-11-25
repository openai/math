import OAI.ThreeFlat.RAM.TerminalWireArchive

namespace OAI
/-! # Numeric records for the selected terminal roots
The receiver follows the selected ordinal to its eight-word node record.
Three exclusive prefix arrays give disjoint pin-map, gate-row and hidden-bit ranges. -/

namespace Hierarchy.TraceReceiverTasks
open ThreeFlat RAM DescriptorExpr DescriptorScan
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure
open scoped Classical Fin.CommRing

structure Layout where
  current : ℕ
  tasks : ℕ
  selected : ℕ
  first : ℕ
  results : ℕ
  parent : ℕ
  maps : ℕ
  pins : ℕ
  rows : ℕ
  bits : ℕ

variable {W : ℕ} (D : Layout)

private abbrev E (W : ℕ) := Term W 0 1

/-- Both the selected ordinal and the first terminal ID are read by the program. -/
def row : E W :=
  let fld (base : ℕ) (i : E W) := Term.load (.binary .add (.literal base) i)
  let x : E W := .binary .sub (.result 0) (.literal D.tasks)
  let i : E W := .binary .div x (.literal 5)
  let c : E W := .binary .mod x (.literal 5)
  let id := Term.binary .add (.load (.literal D.first)) (fld D.selected i)
  let ptr := Term.binary .add (.literal D.results) (.binary .mul (.literal 8) id)
  Term.select .eq c (.literal 0) ptr <|
  Term.select .eq c (.literal 1) (.literal D.parent) <|
  Term.select .eq c (.literal 2) (.binary .add (.literal D.maps) (fld D.pins i)) <|
  Term.select .eq c (.literal 3) (fld D.rows i) (fld D.bits i)

def entry (m : Memory W) (i c : Word W) : Word W :=
  if Comparison.test .eq c 0 then (D.results : Word W)+8*(m (D.first:Word W).val + m ((D.selected:Word W)+i).val)
  else if Comparison.test .eq c 1 then D.parent
  else if Comparison.test .eq c 2 then (D.maps:Word W)+m ((D.pins:Word W)+i).val
  else if Comparison.test .eq c 3 then m ((D.rows:Word W)+i).val else m ((D.bits:Word W)+i).val

def word (m : Memory W) (a : Word W) : Word W :=
  let i := a-(D.tasks:Word W)
  entry D m (BinaryOp.eval .div i 5) (BinaryOp.eval .mod i 5)

theorem eval (m : Memory W) (data : Fin 0 → Word W) (a : Word W) :
    (row D).eval data m (fun _ => a)=word D m a := by
  simp only [row,word,entry,Term.eval_select,Term.eval_load,Term.eval_binary,Term.eval_literal,
    Term.eval]
  rfl

theorem uniformWork : (row (W:=W) D).binds ≤ 128 := by
  simp [row,Term.select,Term.binary,Term.load,Term.literal,Term.binds]

def procedure (W : ℕ) := HeaderScan.procedure (D.current:Word W) 0 1 (row D)

def output (n : ℕ) (m : Memory W) := fillSegment D.tasks (5*n) (fun a=>word D m (a:Word W)) m

/-- A range of `n` readable words, disjoint from the current five-word task output. -/
def ReadRange (n W b : ℕ) : Prop :=
  b+n ≤ 2^W ∧ (b+n ≤ D.tasks ∨ D.tasks+5*n ≤ b)

/-- The selected IDs and all three native prefix tables are preserved during
the task scan. There is one fixed five-word output per selected root. -/
theorem run_disjoint (n : ℕ) (m : Memory W) (room : D.tasks+5*n < 2^W)
    (base : m (m (D.current:Word W).val+0).val=(D.tasks:Word W))
    (length : m (m (D.current:Word W).val+1).val=((5*n:ℕ):Word W))
    (first : D.first < D.tasks) (selected : D.selected+n ≤ D.tasks)
    (pins : ReadRange D n W D.pins) (rows : ReadRange D n W D.rows) (bits : ReadRange D n W D.bits) :
    (procedure D W).Spec (·=m) (fun _ out=>out=output D n m) (13+1300*n) := by
  intro P R K M pc reg pub exit installed data c state entryPC input
  subst state
  obtain ⟨t,time,c',exitPC,done⟩ := HeaderScan.advance_block (row D) (D.current:Word W) 0 1 D.tasks (5*n)
    room pc reg pub exit M installed c m entryPC (fun a => word D m (a:Word W)) base length (by
      intro a mem lo hi agrees
      rw [eval,show (a.val:Word W)=a from Fin.cast_val_eq_self a]
      let idx := BinaryOp.eval .div (a-(D.tasks:Word W)) 5
      have five : 5 < 2^W := by omega
      have rd : ((D.tasks : Word W)).val=D.tasks := Fin.val_cast_of_lt (by omega)
      have ix : idx.val=(a.val-D.tasks)/5 := by
        change (Fin.ofNat _ (_ / _)).val=_
        have ge : (D.tasks:Word W) ≤ a := by change (D.tasks:Word W).val ≤ a.val; rwa [rd]
        have den : (5:Word W).val=5 := Fin.val_cast_of_lt (show (5:ℕ) < 2^W from five)
        rw [Fin.sub_val_of_le ge,rd,den]
        apply Nat.mod_eq_of_lt
        exact (Nat.div_le_self ..).trans_lt (by omega)
      have hidx : idx.val < n := by rw [ix]; omega
      have atRead (b : ℕ) (bound : ReadRange D n W b) : mem ((b:Word W)+idx).val=m ((b:Word W)+idx).val := by
        obtain ⟨fits,separate⟩ := bound
        have e : ((b:Word W)+idx).val=b+idx.val := by
          calc
            _ = ((b:Word W)+(idx.val:Word W)).val := congrArg (fun t : Word W=>((b:Word W)+t).val) (Fin.cast_val_eq_self idx).symm
            _ = _ := by rw [←Nat.cast_add,Fin.val_cast_of_lt (show b+idx.val < 2^W by omega)]
        exact agrees _ (by rw [e]; omega)
      have firstWord := agrees ((D.first:Word W).val) (Or.inl (by rw [Fin.val_cast_of_lt (by omega)]; exact first))
      change TraceReceiverTasks.entry D mem idx _=TraceReceiverTasks.entry D m idx _
      simp only [TraceReceiverTasks.entry,firstWord,atRead D.selected ⟨by omega,Or.inl selected⟩,atRead D.pins pins,
        atRead D.rows rows,atRead D.bits bits])
  refine ⟨t, time.trans ?_, c',_,done,exitPC,rfl⟩
  have := uniformWork (W:=W) D
  have h := Nat.mul_le_mul_left (5*n) (show 2*(row (W:=W) D).binds+4 ≤ 260 by omega)
  omega

/-- The selected IDs and all three native prefix tables are preserved during
the task scan. There is one fixed five-word output per selected root. -/
theorem run (n : ℕ) (m : Memory W) (room : D.tasks+5*n < 2^W)
    (base : m (m (D.current:Word W).val+0).val=(D.tasks:Word W))
    (length : m (m (D.current:Word W).val+1).val=((5*n:ℕ):Word W))
    (first : D.first < D.tasks) (selected : D.selected+n ≤ D.tasks)
    (pins : D.pins+n ≤ D.tasks) (rows : D.rows+n ≤ D.tasks) (bits : D.bits+n ≤ D.tasks) :
    (procedure D W).Spec (·=m) (fun _ out=>out=output D n m) (13+1300*n) :=
  run_disjoint D n m room base length first selected ⟨by omega,Or.inl pins⟩
    ⟨by omega,Or.inl rows⟩ ⟨by omega,Or.inl bits⟩

/-- The actual eight-word header pointer, parent pointer and three counters
read by the seven-word command writer at offset five times the root ordinal. -/
theorem at_root (n : ℕ) (m : Memory W) (room : D.tasks+5*n < 2^W) (i : Fin n) (j : Fin 5) :
    output D n m (D.tasks+5*i.val+j.val)=entry D m (i.val:Word W) (j.val:Word W) := by
  have hi := i.isLt
  have hj := j.isLt
  have five : (5:Word W).val=5 := Fin.val_cast_of_lt (show (5:ℕ) < 2^W by omega)
  have delta : ((D.tasks+5*i.val+j.val:ℕ):Word W)-(D.tasks:Word W)=((5*i.val+j.val:ℕ):Word W) := by push_cast;ring
  have av : ((5*i.val+j.val:ℕ):Word W).val=5*i.val+j.val := Fin.val_cast_of_lt (by omega)
  simp only [output,fillSegment,ite_eq_left (show D.tasks ≤ D.tasks+5*i.val+j.val ∧ D.tasks+5*i.val+j.val < D.tasks+5*n by omega),word,delta]
  congr 1
  · change Fin.ofNat _ (_ / _)=_
    rw [av,five,show (5*i.val+j.val)/5=i.val by omega]; rfl
  · change Fin.ofNat _ (_ % _)=_
    rw [av,five,show (5*i.val+j.val)%5=j.val by omega]; rfl

end Hierarchy.TraceReceiverTasks

end OAI
