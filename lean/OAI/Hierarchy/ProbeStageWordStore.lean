import OAI.ThreeFlat.RAM.PrefixExpressionScan
import OAI.ThreeFlat.RAM.PhysicalInputPhases
import OAI.ThreeFlat.RAM.AdmissionHeader
import OAI.ThreeFlat.RAM.PhysicalExactRun
import OAI.ThreeFlat.RAM.CountedProcedure

namespace OAI
/-! # One native read-modify-write expression and a descending counter -/

namespace Hierarchy.ProbeStage.WordStore

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr DescriptorScan PhysicalPinsExpr
open scoped Fin.CommRing

/-- A closed native assignment can read its own previous target and arbitrary other words. -/
def put (w a : ℕ) (f : Formula 1) : Procedure w :=
  PhysicalInputPhases.writing (AdmissionBank.closed f) Fin.elim0 a 1

def value {w : ℕ} (a : ℕ) (f : Formula 1) (m : Memory w) : Word w :=
  f.value (fun _ => 0) m (fun _ => (a : Word w))

theorem execute {w : ℕ} (a : ℕ) (f : Formula 1) (m : Memory w) (room : a+1<2^w) :
    (put w a f).Exec m (Function.update m a (value a f m)) (2*f.work+8) := by
  intro P R K M pc reg pub exit installed data c input start hinput
  subst input
  let e : Term w 0 1 := AdmissionBank.closed f
  change Fin 0 → Fin K at pub
  change Fin (6+e.labels) ↪ Fin P at pc
  change Fin (4+e.binds) ↪ Fin R at reg
  let A := PhysicalScan.linkedFrame e pc reg pub exit
  have rom (i : Fin (6+(e.mapPublic pub).labels)) : M.code (A.pc i)=A.emit a (a+1) i := by
    let j : Fin (6+e.labels) := i.cast (by simp)
    have same : j.cast (by simp : 6+e.labels=6+(e.mapPublic pub).labels) = i := Fin.ext rfl
    have hi := installed j
    change M.code (A.pc i)=A.emit a (a+1) (j.cast (by simp)) at hi
    rwa [same] at hi
  let word : ℕ → Word w := fun _ => value a f m
  have run := A.advance_prefix M a 1 room rom c m start word (fun z lo hi => by
    have hz : z.val=a := by omega
    have zz : z = (a : Word w) := Fin.ext (by rw [Fin.val_cast_of_lt (by omega : a<2^w)];exact hz)
    subst z
    rw [Fin.val_cast_of_lt (by omega : a<2^w),Nat.sub_self]
    simp [word,value,e,AdmissionBank.eval_closed])
  obtain ⟨t,ht,out,ho,hr⟩ := run
  refine ⟨t,?_,out,_,hr,ho,?_⟩
  · simp only [Term.binds_mapPublic,e,AdmissionBank.binds_closed,one_mul] at ht
    omega
  · funext j
    by_cases hj : j=a <;> simp [fillSegment,word,Function.update,hj]; omega

/-- State after exhausting the descending counter. Each physical guard decrements it before
running the body, whose expression sees the new counter value immediately. -/
def down {w : ℕ} (cell : Word w) (body : Memory w → Memory w) : ℕ → Memory w → Memory w
  | 0,m => m
  | n+1,m => down cell body n (body (writeMemory m cell (m cell.val-1)))

theorem down_exec {w : ℕ} (cell : Word w) (p : Procedure w) (body : Memory w → Memory w)
    (cost : ℕ) (runs : ∀ m, p.Exec m (body m) cost) (keeps : ∀ m, body m cell.val=m cell.val)
    (m : Memory w) :
    (p.counted cell).Exec m (down cell body (m cell.val).val m) ((m cell.val).val*(7+cost)+4) := by
  let n := (m cell.val).val
  let inv (z : ℕ) (s : Memory w) := down cell body z s=down cell body n m
  have run : (p.counted cell).Spec (fun s => inv n s ∧ (s cell.val).val=n)
      (fun _ s => inv 0 s) (n*(7+cost)+4) := Procedure.counted_spec p cell n cost inv (fun z s hs hz => by
    let pre := writeMemory s cell (s cell.val-1)
    have hval : (body pre cell.val).val=z := by
      rw [keeps]
      simp only [pre,writeMemory,ite_true]
      have fit : z+1<2^w := hz ▸ (s cell.val).isLt
      have same : s cell.val = ((z+1:ℕ):Word w) := Fin.ext (by rw [Fin.val_cast_of_lt fit];exact hz)
      rw [same,Nat.cast_add,Nat.cast_one,add_sub_cancel_right,Fin.val_cast_of_lt (by omega : z<2^w)]
    intro P R K M pc reg pub exit installed data cfg input start eqn
    change input=pre at eqn
    subst input
    obtain ⟨t,ht,o,out,hr,hpc,hout⟩ := runs pre M pc reg pub exit installed data cfg pre start rfl
    change out=body pre at hout
    subst out
    exact ⟨t,ht,o,body pre,hr,hpc,hval,hs⟩)
  intro P R K M pc reg pub exit installed data cfg input start eqn
  subst input
  exact run M pc reg pub exit installed data cfg m start ⟨rfl,rfl⟩

end Hierarchy.ProbeStage.WordStore

end OAI
