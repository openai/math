import OAI.ThreeFlat.RAM.HistoryCommandTable
import OAI.ThreeFlat.RAM.HeaderScan
import OAI.ThreeFlat.RAM.PhysicalProcedure

namespace OAI
/-! # Constructing the terminal gather commands from short tasks in RAM

The caller provides a five-word task for each selected root and compact child
and parent node records. A single native loop expands the tasks, obtaining
the number of output words from the active header. -/

namespace Hierarchy.TraceFactorReceiver.Commands

open ThreeFlat RAM Computability.VPVNP.BurstRAM PrivateRAM
open DescriptorExpr DescriptorScan PhysicalProcedure HistoryCommandTable HistoryJoinScan
open scoped Classical BigOperators Fin.CommRing

variable {w : ℕ}

private def args (w commands tasks : ℕ) : Fin 3 → Term w 0 1 :=
  ![.result 0,.literal (commands : Word w),.literal (tasks : Word w)]

def expression (w commands tasks : ℕ) : Term w 0 1 :=
  (HistoryCommandTable.term w 0).instantiate (args w commands tasks)

theorem cost (commands tasks : ℕ) : (expression w commands tasks).binds≤514 := by
  rw [expression,Term.binds_instantiate]
  have base := HistoryCommandTable.binds_le (w:=w) (k:=0)
  have extra : (∑ i, (args w commands tasks i).binds)=2 := by
    simp [Fin.sum_univ_succ,args,Term.literal,Term.binds]
  omega

def address (tasks commands a : Word w) :=
  tasks+5*BinaryOp.eval .div (a-commands) 7

def word (tasks commands : Word w) (m : Memory w) (a : Word w) :=
  let t := readTask m (address tasks commands a)
  let c := readNode m t.child
  let p := readNode m t.parent
  selectWord (t.header c p) (t.past c p) (BinaryOp.eval .mod (a-commands) 7)

theorem eval (commands tasks : ℕ) (m : Memory w) (a : Word w) :
    (expression w commands tasks).eval Fin.elim0 m (fun _ => a)=word tasks commands m a := by
  rw [expression,Term.eval_instantiate,HistoryCommandTable.term_eval]
  rfl

/-- Each task and both nodes it designates may be anywhere outside the
seven-word output stream. The other words of memory may change freely. -/
structure Separate (tasks commands count : ℕ) (m : Memory w) : Prop where
  task : ∀ (a : Word w), commands≤a.val → a.val<commands+7*count → ∀ j : Fin 5,
    let b := (address tasks commands a+(j.val : Word w)).val
    b<commands ∨ commands+7*count≤b
  child : ∀ (a : Word w), commands≤a.val → a.val<commands+7*count → ∀ j : Fin 4,
    let t := readTask m (address tasks commands a)
    let b := (t.child+(j.val : Word w)).val
    b<commands ∨ commands+7*count≤b
  parent : ∀ (a : Word w), commands≤a.val → a.val<commands+7*count → ∀ j : Fin 4,
    let t := readTask m (address tasks commands a)
    let b := (t.parent+(j.val : Word w)).val
    b<commands ∨ commands+7*count≤b

private theorem word_frame {tasks commands count : ℕ} {m m' : Memory w} (a : Word w)
    (low : commands≤a.val) (high : a.val<commands+7*count)
    (sep : Separate tasks commands count m) (frame : agreesOutside commands (commands+7*count) m' m) :
    word tasks commands m' a = word tasks commands m a := by
  let atTask := address (tasks : Word w) commands a
  have t : readTask m' atTask=readTask m atTask := by
    unfold readTask
    congr 1 <;> first | exact frame _ (sep.task a low high 0) | exact frame _ (sep.task a low high 1) |
      exact frame _ (sep.task a low high 2) | exact frame _ (sep.task a low high 3) |
      exact frame _ (sep.task a low high 4)
  let selected := readTask m atTask
  have c : readNode m' selected.child=readNode m selected.child := by
    unfold readNode
    congr 1 <;> first | exact frame _ (sep.child a low high 0) | exact frame _ (sep.child a low high 1) |
      exact frame _ (sep.child a low high 2) | exact frame _ (sep.child a low high 3)
  have p : readNode m' selected.parent=readNode m selected.parent := by
    unfold readNode
    congr 1 <;> first | exact frame _ (sep.parent a low high 0) | exact frame _ (sep.parent a low high 1) |
      exact frame _ (sep.parent a low high 2) | exact frame _ (sep.parent a low high 3)
  dsimp only [word]
  change selectWord ((readTask m' atTask).header _ _) ((readTask m' atTask).past _ _) _ = _
  rw [t,c,p]

/-- The code contains the fixed scratch addresses. The number of selected
roots is only a memory operand, read on entry from the current header. -/
def procedure (w current commands tasks : ℕ) : Procedure w :=
  let e := expression w commands tasks
  ⟨13+e.labels,4+e.binds,0,HeaderScan.block e (current : Word w) 0 1,Fin.elim0⟩

theorem dimensions (w current commands tasks : ℕ) :
    (procedure w current commands tasks).labels≤1556 ∧
    (procedure w current commands tasks).registers≤518 ∧
    (procedure w current commands tasks).slots=0 := by
  have bound := cost (w:=w) commands tasks
  change 13+(expression w commands tasks).labels≤1556 ∧
    4+(expression w commands tasks).binds≤518 ∧ 0=0
  rw [Term.labels_eq]
  omega

def output (commands tasks count : ℕ) (m : Memory w) :=
  fillSegment commands (7*count) (fun a => word tasks commands m (Fin.ofNat _ a)) m

set_option maxHeartbeats 1600000 in
theorem run (current commands tasks count : ℕ) (m : Memory w)
    (limit : commands+7*count<2^w)
    (lo : m (m (current : Word w).val+0).val=(commands : Word w))
    (len : m (m (current : Word w).val+1).val=((7*count:ℕ) : Word w))
    (sep : Separate tasks commands count m) :
    (procedure w current commands tasks).Spec (·=m)
      (fun _ out => out=output commands tasks count m) (13+7224*count) := by
  intro P R K M pc reg pub exit installed data c start entry hs
  subst start
  let e := expression w commands tasks
  have same : (fun i : Fin 0 => M.publicData (pub i))=Fin.elim0 := funext fun i=>i.elim0
  obtain ⟨steps,price,out,done,go⟩ := HeaderScan.advance_block e (current : Word w) 0 1 commands (7*count)
    limit pc reg pub exit M installed c m entry (fun a => word tasks commands m (Fin.ofNat _ a)) lo len (by
      intro a mem left right frame
      have rename := congrArg (fun f : Fin 0→Word w => e.eval f mem (fun _=>a)) same
      exact rename.trans ((eval commands tasks mem a).trans ((word_frame a left right sep frame).trans
        (congrArg (word tasks commands m) (Fin.ext (Nat.mod_eq_of_lt a.isLt).symm)))))
  refine ⟨steps,price.trans ?_,out,_,go,done,rfl⟩
  have unit : 2*e.binds+4≤1032 := by have := cost (w:=w) commands tasks; dsimp only [e]; omega
  have bound := Nat.mul_le_mul_left (7*count) unit
  omega

/-- The seven columns of one command are the named child's physical stream,
rebased destination, real pin map and arities, hidden offset, and ending word. -/
theorem at_root (commands tasks count : ℕ) (m : Memory w) (limit : commands+7*count<2^w)
    (i : Fin count) (j : Fin 7) :
    let t := readTask m ((tasks : Word w)+5*(i.val : Word w))
    let c := readNode m t.child
    let p := readNode m t.parent
    output commands tasks count m (commands+7*i.val+j.val)=selectWord (t.header c p) (t.past c p) (j.val : Word w) := by
  intro t c p
  have hi := i.isLt
  have hj := j.isLt
  have wide : 7<2^w := by omega
  have delta : ((commands+7*i.val+j.val : ℕ) : Word w)-(commands : Word w) =
      ((7*i.val+j.val : ℕ) : Word w) := by push_cast; ring
  have av : (((7*i.val+j.val : ℕ) : Word w)).val=7*i.val+j.val := Fin.val_cast_of_lt (by omega)
  have seven : (7 : Word w).val=7 := Fin.val_cast_of_lt wide
  have div : BinaryOp.eval .div ((7*i.val+j.val : ℕ) : Word w) 7=(i.val : Word w) := by
    change Fin.ofNat _ (_ / _) = _
    rw [av,seven,show (7*i.val+j.val)/7=i.val by omega]; rfl
  have mod : BinaryOp.eval .mod ((7*i.val+j.val : ℕ) : Word w) 7=(j.val : Word w) := by
    change Fin.ofNat _ (_ % _) = _
    rw [av,seven,show (7*i.val+j.val)%7=j.val by omega]; rfl
  simp only [output,fillSegment,ite_eq_left (show commands≤commands+7*i.val+j.val ∧
    commands+7*i.val+j.val<commands+7*count by omega)]
  change word tasks commands m ((commands+7*i.val+j.val : ℕ) : Word w)=_
  simp only [word,address,delta,div,mod]; rfl

end Hierarchy.TraceFactorReceiver.Commands

end OAI
