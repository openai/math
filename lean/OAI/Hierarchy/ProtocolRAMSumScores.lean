import OAI.Hierarchy.ProtocolRAMScan
import OAI.ThreeFlat.RAM.PrefixExpressionScan

namespace OAI
/-! # A native running score and final threshold comparison

The first n words of the output contain the cumulative row scores. The next
word compares the last total with the chosen threshold. The empty scan also
writes its comparison bit, using zero as its total.
-/

set_option maxHeartbeats 1200000

namespace Hierarchy.ProtocolRAM.SumScores
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Fin.CommRing BigOperators Classical

variable {W n : ℕ}
abbrev T (W : ℕ) := Term W 0 1

def prior (W out : ℕ) : T W :=
  .select .eq (.result 0) (.literal out) (.literal 0)
    (.load (.binary .sub (.result 0) (.literal 1)))

def step (W out n bound : ℕ) (e : Expr) : T W :=
  let back := prior W out
  .select .eq (.result 0) (.literal (out+n))
    (.select .lt back (.literal bound) (.literal 0) (.literal 1))
    (.binary .add back (e.compile W out))

def procedure (W out n bound : ℕ) (e : Expr) :=
  PhysicalInputPhases.writing (step W out n bound e) Fin.elim0 out (n+1)

def total (score : Fin n → ℕ) (k : ℕ) :=
  ∑ i : Fin n, if i.val<k then score i else 0

@[simp] theorem total_zero (score : Fin n → ℕ) : total score 0 = 0 := by simp [total]
@[simp] theorem total_all (score : Fin n → ℕ) : total score n = ∑ i, score i := by simp [total]

theorem total_next (score : Fin n → ℕ) (i : Fin n) :
    total score (i.val+1) = total score i.val + score i := by
  have cut (j : Fin n) : (if j.val < i.val+1 then score j else 0) =
      (if j.val < i.val then score j else 0) + (if j=i then score i else 0) := by
    rcases lt_trichotomy j i with h|h|h
    · have lt : j.val < i.val := h
      simp [h.ne,lt,show j.val < i.val+1 by omega]
    · subst j
      simp
    · have lt : i.val < j.val := h
      simp [h.ne',show ¬j.val < i.val by omega,show ¬j.val < i.val+1 by omega]
  unfold total
  rw [Finset.sum_congr rfl (fun j _=>cut j),Finset.sum_add_distrib]
  simp

def word (out bound : ℕ) (score : Fin n → ℕ) (a : ℕ) : Word W :=
  if a-out<n then (total score (a-out+1):Word W)
  else if bound ≤ ∑ i,score i then 1 else 0

def Reads (m : Memory W) (e : Expr) (score : Fin n → ℕ) : Prop :=
  ∀ i : Fin n, e.eval m (i.val:Word W) = (score i:Word W)

private theorem select_cost (c : Comparison) (a b u v : T W) :
    (Term.select c a b u v).binds = a.binds+b.binds+u.binds+v.binds+1 := by
  simp only [Term.select,Term.binds_letThen,Term.binds_rename,Term.binds]; omega

private theorem binary_cost (op : BinaryOp) (a b : T W) :
    (Term.binary op a b).binds = a.binds+b.binds+1 := by
  simp only [Term.binary,Term.binds_letThen,Term.binds_rename,Term.binds]; omega

theorem step_binds (W out n bound : ℕ) (e : Expr) :
    (step W out n bound e).binds = 19+e.work := by
  have load_cost (a : T W) : (Term.load a).binds=a.binds+1 := by
    simp only [Term.load,Term.binds_letThen,Term.binds]
  have prev : (prior W out).binds=6 := by
    simp only [prior,select_cost,load_cost,binary_cost,Term.literal,Term.binds]
  simp only [step,select_cost,binary_cost,prev,compile_binds,Term.literal,Term.binds]; omega

private theorem row_correct (out bound : ℕ) (e : Expr) (score : Fin n → ℕ) (m : Memory W)
    (reads : Reads m e score) (fit : e.Fits W out) (room : out+(n+1)<2^W)
    (threshold : bound<2^W) (sumroom : (∑ i, score i)<2^W)
    (a : Word W) (lo : out≤a.val) (hi : a.val<out+(n+1)) :
    (step W out n bound e).eval Fin.elim0
      (fillSegment out (a.val-out) (word out bound score) m) (fun _ => a) = word out bound score a.val := by
  let k := a.val-out
  let mem := fillSegment out k (word (W:=W) out bound score) m
  have eqn : out+k=a.val := Nat.add_sub_of_le lo
  have endk : k≤n := by omega
  have aval : ((out+k:ℕ):Word W) = a := by rw [eqn]; exact Fin.cast_val_eq_self _
  have test (t : ℕ) (ht : out+t<2^W) : (a=((out+t:ℕ):Word W)) ↔ k=t := by
    rw [Fin.ext_iff,Fin.val_cast_of_lt ht]
    omega
  have prev : (prior W out).eval Fin.elim0 mem (fun _ => a) = (total score k : Word W) := by
    simp only [prior,Term.eval_select,Term.eval_literal,Term.eval_load,Term.eval_binary,
      BinaryOp.eval,Comparison.test,beq_iff_eq]
    change (if a=(out:Word W) then 0 else mem (a-1).val) = _
    have atStart : a=(out:Word W) ↔ k=0 := by simpa using test 0 (by omega)
    cases h : k with
    | zero => simp [atStart.mpr h]
    | succ t =>
      have notStart : a ≠ (out:Word W) := fun eq => by have := atStart.mp eq; omega
      rw [ite_eq_right notStart]
      have hprev : a-1 = ((out+t:ℕ):Word W) := by
        rw [←aval,h,Nat.add_succ,Nat.cast_succ]
        abel
      have inside : out≤out+t ∧ out+t<out+k := by omega
      have prevVal : (a-1).val=out+t :=
        (congrArg Fin.val hprev).trans (Fin.val_cast_of_lt (by omega))
      rw [prevVal]
      simp only [mem,fillSegment,ite_eq_left inside,word,Nat.add_sub_cancel_left,ite_eq_left (show t<n by omega)]
  change (step W out n bound e).eval Fin.elim0 mem (fun _ => a) = _
  simp only [step,Term.eval_select,Term.eval_literal,Term.eval_binary,BinaryOp.eval,
    Comparison.test,beq_iff_eq,decide_eq_true_eq,prev,←Nat.cast_add]
  change (if a=((out+n:ℕ):Word W) then
    (if (total score k:Word W)<(bound:Word W) then 0 else 1)
    else (total score k:Word W)+(e.compile W out).eval Fin.elim0 mem (fun _ => a)) = _
  have finalWord := test n (by omega)
  simp only [finalWord]
  by_cases final : k=n
  · rw [ite_eq_left final,final,total_all]
    have cmp : ((↑(∑ i, score i):Word W)<(bound:Word W)) ↔ (∑ i, score i)<bound := by
      rw [Fin.lt_def,Fin.val_cast_of_lt sumroom,Fin.val_cast_of_lt threshold]
    change _ = if k<n then _ else _
    by_cases small : (∑ i, score i)<bound
    · rw [ite_eq_left (cmp.mpr small),ite_eq_right (by omega : ¬k<n),ite_eq_right (not_le.mpr small)]
    · rw [ite_eq_right (fun h=>small (cmp.mp h)),ite_eq_right (by omega : ¬k<n),ite_eq_left (le_of_not_gt small)]
  · have valid : k<n := by omega
    let i : Fin n := ⟨k,valid⟩
    have row : a-(out:Word W) = (k:Word W) := by rw [←aval,Nat.cast_add]; abel
    have old : e.eval mem (k:Word W) = e.eval m (k:Word W) :=
      eval_below e _ m mem fit (fun j low => by simp [mem,fillSegment,not_le.mpr low])
    rw [ite_eq_right final,eval_compile e mem a fit (by omega),row,old,reads i]
    change (total score k:Word W)+(score i:Word W) = if k<n then _ else _
    rw [ite_eq_left valid,←Nat.cast_add,←total_next score i]

/-- Execute one fixed native expression against the already written prefix. -/
theorem writing_prefix (expr : T W) (out len : ℕ) (room : out+len < 2^W)
    (pre : Memory W → Prop) (value : Memory W → ℕ → Word W)
    (correct : ∀ m, pre m → ∀ a : Word W, out≤a.val → a.val<out+len →
      expr.eval Fin.elim0 (fillSegment out (a.val-out) (value m) m) (fun _=>a) = value m a.val) :
    (PhysicalInputPhases.writing expr Fin.elim0 out len).Spec pre
      (fun m after=>after=fillSegment out len (value m) m) (4+len*(2*expr.binds+4)) := by
  intro P R K M pc reg pub exit installed data c m start reads
  let φ : Fin 0 → Fin K := pub
  let pcs : Fin (6+expr.labels) ↪ Fin P := pc
  let regs : Fin (4+expr.binds) ↪ Fin R := reg
  have inst : (PhysicalScan.block expr out len).Installed M pcs regs φ exit := installed
  let A := PhysicalScan.linkedFrame expr pcs regs φ exit
  have rom (i : Fin (6+(expr.mapPublic φ).labels)) : M.code (A.pc i)=A.emit out (out+len) i := by
    let j : Fin (6+expr.labels) := i.cast (by simp only [Term.labels_mapPublic])
    have same : j.cast (by simp only [Term.labels_mapPublic] : 6+expr.labels=6+(expr.mapPublic φ).labels) = i :=
      Fin.ext rfl
    have hh := inst j
    change M.code (A.pc i)=A.emit out (out+len) (j.cast (by simp only [Term.labels_mapPublic])) at hh
    rwa [same] at hh
  have begins : c.pc=A.drv 0 := start
  have params : M.publicData ∘ φ = (Fin.elim0 : Fin 0 → Word W) := funext (fun i=>Fin.elim0 i)
  obtain ⟨t,ht,config,land,run⟩ := A.advance_prefix M out len room rom c m begins
    (value m) (by
      intro a lo hi
      rw [Term.eval_mapPublic,params]
      exact correct m reads a lo hi)
  exact ⟨t,by simpa only [Term.binds_mapPublic] using ht,config,_,run,land,rfl⟩

/-- Prefix scores and the final bit all come from the same native instruction scan. -/
theorem run (out bound : ℕ) (e : Expr) (score : Fin n → ℕ) (fit : e.Fits W out)
    (room : out+(n+1)<2^W) (threshold : bound<2^W) (sumroom : (∑ i, score i)<2^W) :
    (procedure W out n bound e).Spec (fun m => Reads m e score)
      (fun m after => after=fillSegment out (n+1) (word out bound score) m)
      (4+(n+1)*(42+2*e.work)) := by
  have bill : 4+(n+1)*(2*(step W out n bound e).binds+4)=4+(n+1)*(42+2*e.work) := by
    rw [step_binds]
    ring
  rw [←bill]
  intro P R K M pc reg pub exit installed data cfg m start reads
  exact writing_prefix (step W out n bound e) out (n+1) room
    (fun m=>Reads m e score) (fun _=>word out bound score)
    (fun m hm=>row_correct out bound e score m hm fit room threshold sumroom)
    M pc reg pub exit installed data cfg m start reads

theorem read_prefix (out bound : ℕ) (score : Fin n → ℕ) (m : Memory W) (i : Fin n) :
    fillSegment out (n+1) (word out bound score) m (out+i.val) = (total score (i.val+1):Word W) := by
  have hi := i.isLt
  have inside : out≤out+i.val ∧ out+i.val<out+(n+1) := by omega
  simp [fillSegment,inside,word,hi]

theorem read_flag (out bound : ℕ) (score : Fin n → ℕ) (m : Memory W) :
    fillSegment out (n+1) (word out bound score) m (out+n) =
      if bound ≤ ∑ i, score i then 1 else 0 := by simp [fillSegment,word]

end Hierarchy.ProtocolRAM.SumScores

end OAI
