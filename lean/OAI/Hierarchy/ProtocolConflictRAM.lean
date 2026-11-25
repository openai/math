import OAI.Hierarchy.ProtocolConflictPack
import OAI.Hierarchy.ProtocolRAMSumScores

namespace OAI
/-! # Native bounded-degree greedy conflict scan

Memory has one failure bit per candidate, followed by fixed columns of
neighbour ordinals and then one decision word per candidate. Every query
to an earlier decision sees the word produced by the same scan.
-/

set_option maxHeartbeats 1200000
namespace Hierarchy.ProtocolConflictPack.Native

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing

variable {W n d : ℕ}
abbrev T (W : ℕ) := Term W 0 1

def dst (base n d : ℕ) := base+n+n*d
def row (W out : ℕ) : T W := .binary .sub (.result 0) (.literal out)
def mask (W base out : ℕ) : T W := .load (.binary .add (.literal base) (row W out))
def neighbour (W base n out j : ℕ) : T W :=
  .binary .add (.literal out) (.load (.binary .add (.literal (base+n+j*n)) (row W out)))
def clear (W base n out j : ℕ) : T W :=
  let q := neighbour W base n out j
  .select .lt q (.result 0) (.select .eq (.load q) (.literal 0) (.literal 1) (.literal 0)) (.literal 1)

def both (x y : T W) : T W := .select .eq x (.literal 0) (.literal 0) y

def checks (W base n d out : ℕ) : List (Fin d) → T W
  | [] => .literal 1
  | j::js => both (clear W base n out j.val) (checks W base n d out js)

def step (W base n d : ℕ) : T W :=
  both (mask W base (dst base n d)) (checks W base n d (dst base n d) (List.finRange d))

def scan (W base n d : ℕ) := PhysicalInputPhases.writing (step W base n d) Fin.elim0 (dst base n d) n

def Packed (base : ℕ) (fail : Fin n → Bool) (adj : Fin n → Fin d → Fin n) (m : Memory W) : Prop :=
  (∀ i, m (base+i.val) = (if fail i then 1 else 0)) ∧
  ∀ i j, m (base+n+j.val*n+i.val) = ((adj i j).val : Word W)

noncomputable def output (out : ℕ) (fail : Fin n → Bool) (adj : Fin n → Fin d → Fin n)
    (a : ℕ) : Word W :=
  if h : a-out<n then (if Chosen fail adj ⟨a-out,h⟩ then 1 else 0) else 0

@[simp] theorem output_at (out : ℕ) (fail : Fin n → Bool) (adj : Fin n → Fin d → Fin n) (i : Fin n) :
    output (W:=W) out fail adj (out+i.val) = if Chosen fail adj i then 1 else 0 := by
  simp [output,i.isLt]

private theorem both_correct (x y : T W) (mem : Memory W) (vs : Fin 1 → Word W)
    (p q : Prop) [Decidable p] [Decidable q]
    (left : x.eval Fin.elim0 mem vs = if p then 1 else 0)
    (right : y.eval Fin.elim0 mem vs = if q then 1 else 0) :
    (both x y).eval Fin.elim0 mem vs = if p ∧ q then 1 else 0 := by
  by_cases small : (1:Word W) = 0 <;> by_cases hp : p <;> by_cases hq : q <;>
    simp [both,Term.eval_select,Comparison.test,left,right,hp,hq,small]

private theorem checks_correct (base out : ℕ) (js : List (Fin d)) (mem : Memory W)
    (vs : Fin 1 → Word W) (ok : Fin d → Prop) [DecidablePred ok]
    (single : ∀ j : Fin d, (clear W base n out j.val).eval Fin.elim0 mem vs = if ok j then 1 else 0) :
    (checks W base n d out js).eval Fin.elim0 mem vs = if ∀ j∈js, ok j then 1 else 0 := by
  induction js with
  | nil => simp [checks]
  | cons j js ih =>
    rw [checks,both_correct _ _ _ _ (ok j) (∀ k∈js, ok k) (single j) ih]
    simp

private theorem step_correct (base : ℕ) (fail : Fin n → Bool) (adj : Fin n → Fin d → Fin n)
    (m : Memory W) (packed : Packed base fail adj m)
    (room : dst base n d+n<2^W) (i : Fin n) :
    let out := dst base n d
    (step W base n d).eval Fin.elim0 (fillSegment out i.val (output out fail adj) m)
      (fun _ => ((out+i.val:ℕ):Word W)) = output out fail adj (out+i.val) := by
  let out := dst base n d
  let mem := fillSegment out i.val (output (W:=W) out fail adj) m
  let vs := fun _ : Fin 1 => ((out+i.val:ℕ):Word W)
  let ok (j : Fin d) := adj i j < i → ¬Chosen fail adj (adj i j)
  have hi := i.isLt
  have ends : out+n<2^W := room
  have addr (u : Fin n) : out+u.val < 2^W := by have := u.isLt; omega
  have ordinal : (row W out).eval Fin.elim0 mem vs = (i.val : Word W) := by
    change ((out+i.val:ℕ):Word W) - (out:Word W) = _
    push_cast
    abel
  have flag : (mask W base out).eval Fin.elim0 mem vs = if fail i then 1 else 0 := by
    simp only [mask,Term.eval_load,Term.eval_binary,Term.eval_literal,ordinal,BinaryOp.eval,←Nat.cast_add]
    have away : base+i.val < out := by dsimp [out,dst]; omega
    rw [Fin.val_cast_of_lt (away.trans (by omega : out < 2^W))]
    change fillSegment out i.val _ _ _ = _
    rw [fillSegment,ite_eq_right (by omega)]
    exact packed.1 i
  have next (j : Fin d) :
      (neighbour W base n out j.val).eval Fin.elim0 mem vs = ((out+(adj i j).val:ℕ):Word W) := by
    have hj := j.isLt
    have colLast : (j.val+1)*n ≤ d*n := Nat.mul_le_mul_right n hj
    have away : base+n+j.val*n+i.val < out := by dsimp [out,dst]; nlinarith only [hi,colLast]
    simp only [neighbour,Term.eval_binary,Term.eval_literal,Term.eval_load,ordinal,BinaryOp.eval,
      ←Nat.cast_mul,←Nat.cast_add,Fin.val_cast_of_lt (away.trans (by omega : out < 2^W))]
    change (out:Word W)+fillSegment out i.val _ _ _ = _
    rw [fillSegment,ite_eq_right (by omega),packed.2 i j,Nat.cast_add]
  have one : (1:Word W) ≠ 0 := by
    have fit : 1<2^W := by omega
    intro he
    have eqn := congrArg Fin.val he
    have oneVal : (1:Word W).val = 1 := Fin.val_cast_of_lt fit
    rw [oneVal,Fin.val_zero] at eqn
    omega
  have single (j : Fin d) : (clear W base n out j.val).eval Fin.elim0 mem vs =
      if ok j then 1 else 0 := by
    have cmp : (((out+(adj i j).val:ℕ):Word W)<vs 0) ↔ adj i j < i := by
      change _ < ((out+i.val:ℕ):Word W) ↔ _
      rw [Fin.lt_def,Fin.val_cast_of_lt (addr _),Fin.val_cast_of_lt (addr _)]
      omega
    simp only [clear,Term.eval_select,Term.eval_load,Term.eval_literal,next,
      Comparison.test,beq_iff_eq,decide_eq_true_eq]
    change (if ((out+(adj i j).val:ℕ):Word W)<vs 0 then
      (if mem _ = 0 then 1 else 0) else 1) = _
    by_cases before : adj i j < i
    · have inside : out ≤ out+(adj i j).val ∧ out+(adj i j).val < out+i.val := by
        change (adj i j).val < i.val at before
        omega
      have priorWord : mem (out+(adj i j).val) = if Chosen fail adj (adj i j) then 1 else 0 := by
        change (if out≤out+(adj i j).val ∧ out+(adj i j).val<out+i.val then
          output out fail adj (out+(adj i j).val) else m (out+(adj i j).val)) = _
        rw [ite_eq_left inside,output_at]
      rw [ite_eq_left (cmp.mpr before),Fin.val_cast_of_lt (addr _),priorWord]
      by_cases hit : Chosen fail adj (adj i j) <;> simp [ok,before,hit,one]
    · rw [ite_eq_right (fun h=>before (cmp.mp h)),ite_eq_left (show ok j from fun hj=>(before hj).elim)]
  have code := checks_correct (n:=n) base out (List.finRange d) mem vs ok (fun j=>by
    by_cases h : ok j <;> simpa only [h,ite_true,ite_false] using single j)
  have chosen : Chosen fail adj i ↔ fail i=true ∧ ∀ j,ok j := chosen_iff fail adj i
  change (both (mask W base out) (checks W base n d out (List.finRange d))).eval Fin.elim0 mem vs =
    output out fail adj (out+i.val)
  simp only [both,Term.eval_select,Term.eval_literal,Comparison.test,beq_iff_eq,flag,code,output_at]
  by_cases f : fail i=true <;> by_cases all : ∀ j,ok j <;>
    simp [chosen,List.mem_finRange,f,all,one]

private theorem both_binds (x y : T W) : (both x y).binds = x.binds+y.binds+3 := by
  simp [both,Term.select,Term.literal,Term.binds,Nat.add_assoc]; omega

theorem step_binds (W base n d : ℕ) : (step W base n d).binds = 9+24*d := by
  let out := dst base n d
  have select (q : Comparison) (a b x y : T W) : (Term.select q a b x y).binds =
      a.binds+b.binds+x.binds+y.binds+1 := by simp [Term.select,Term.binds]; omega
  have binary (op : BinaryOp) (a b : T W) : (Term.binary op a b).binds=a.binds+b.binds+1 := by
    simp [Term.binary,Term.binds]; omega
  have load (a : T W) : (Term.load a).binds=a.binds+1 := by simp [Term.load,Term.binds]
  have slot (j : Fin d) : (clear W base n out j.val).binds = 21 := by
    simp only [clear,neighbour,row,select,binary,load,Term.literal,Term.binds]
  have cost (js : List (Fin d)) : (checks W base n d out js).binds = 1+24*js.length := by
    induction js with
    | nil => rfl
    | cons j rest ih =>
      simp only [checks,both_binds,slot,ih,List.length_cons]
      omega
  have flag : (mask W base out).binds = 5 := by
    simp only [mask,row,load,binary,Term.literal,Term.binds]
  change (both (mask W base out) (checks W base n d out (List.finRange d))).binds = _
  rw [both_binds,flag,cost,List.length_finRange]
  omega

/-- The fixed row program makes at most 22+48d native transitions per candidate.
The postcondition retains all input and adjacent memory outside the output bank. -/
theorem scan_spec (base : ℕ) (fail : Fin n → Bool) (adj : Fin n → Fin d → Fin n)
    (room : dst base n d+n<2^W) :
    (scan W base n d).Spec (Packed base fail adj)
      (fun m after => after=fillSegment (dst base n d) n (output (dst base n d) fail adj) m)
      (4+n*(22+48*d)) := by
  let out := dst base n d
  have bill : 4+n*(2*(step W base n d).binds+4)=4+n*(22+48*d) := by
    rw [step_binds]
    ring
  rw [←bill]
  apply ProtocolRAM.SumScores.writing_prefix (step W base n d) out n room (Packed base fail adj)
    (fun _ => output out fail adj)
  intro m packed a low high
  let i : Fin n := ⟨a.val-out,by omega⟩
  have ha : out+i.val=a.val := Nat.add_sub_of_le low
  have hh := step_correct base fail adj m packed room i
  change (step W base n d).eval Fin.elim0 (fillSegment out i.val (output out fail adj) m)
    (fun _ => ((out+i.val:ℕ):Word W)) = output out fail adj (out+i.val) at hh
  simpa only [ha,Fin.cast_val_eq_self] using hh

theorem read_decision (out : ℕ) (fail : Fin n → Bool) (adj : Fin n → Fin d → Fin n)
    (m : Memory W) (v : Fin n) :
    fillSegment out n (output out fail adj) m (out+v.val) =
      if v ∈ picked fail adj then 1 else 0 := by
  simp [fillSegment,picked,v.isLt]

end Hierarchy.ProtocolConflictPack.Native

end OAI
