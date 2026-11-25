import OAI.Optimization.LinearProgramming.Recovery.SupportInit
import OAI.Optimization.LinearProgramming.RAM.CallableOddLeaf
import OAI.Optimization.LinearProgramming.RAM.CallableOddCalls
import OAI.Optimization.LinearProgramming.RAM.CallableControl

/-! The LP's marked-coordinate loop in ordinary relocatable RAM code. The persistent
support and pointers use the encoded odd caller bank. A call may replace the entire even
callee bank. Its returned tag is explicitly stored in the caller's decision register. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace SupportRAM

open RAM RAM.Callable
open _root_.OAI.Optimization.LinearProgramming.Geometry (deleteCoordinates)

abbrev outerLeaf := Odd.leaf

def markedIteration (call : Fragment) : Fragment := (outerLeaf clear).seq
  (call.seq ((outerLeaf applyReply).seq (outerLeaf advance)))

def markedLoop (call : Fragment) : Fragment := Fragment.loop (Odd.cond (.addrLT 152 150)) (markedIteration call)

def markedSearch (call : Fragment) : Fragment := (outerLeaf initFlags).seq (markedLoop call)

universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem leaf_run (P : K → Prop) (e : Memory K) (he : e.AllData P)
    {b : Block} {a t : Memory K} {k : ℕ} (h : Block.Eval (Memory.AllData P) b a k t) :
    (outerLeaf b).Run P (Odd.memory e a) (4*k) (Odd.memory e t) := Odd.leaf_run P e he h

/-- Normal procedure return stores the ordinary answer in logical index 154. `ready`
tracks the finitely localized auxiliary bank over successive calls. -/
def FragmentRealizes {n : ℕ} (call : Fragment) (P : K → Prop) (ready : Memory K → Prop)
    (base bound : ℕ) (oracle : Finset (Fin n) → Bool) :=
  ∀ (j : Fin n) (S : Finset (Fin n)) (callee caller : Memory K),
    ready callee → callee.AllData P → caller.AllData P → Layout caller base j.val S →
    ∃ callee', ready callee' ∧ callee'.AllData P ∧ call.Run P (Odd.memory callee caller) bound
      (Odd.memory callee' (caller.putIndex 154 (oracle S).toNat))

private theorem iteration_run {n base bound : ℕ} (oracle : Finset (Fin n) → Bool) (call : Fragment)
    (P : K → Prop) (h0 : P 0) (ready : Memory K → Prop) (hc : FragmentRealizes call P ready base bound oracle)
    (lo : 152 ≤ base) (j : Fin n) (S : Finset (Fin n)) (e m : Memory K) (rdy : ready e)
    (se : e.AllData P) (sm : m.AllData P) (h : Layout m base j.val S) :
    ∃ e' t, ready e' ∧ e'.AllData P ∧ t.AllData P ∧ Layout t base (j.val+1) (if oracle (S.erase j) then S.erase j else S) ∧
      (markedIteration call).Run P (Odd.memory e m) (bound+32) (Odd.memory e' t) := by
  obtain ⟨a,ea,la,stored⟩ := clear_spec j m h lo P sm h0
  obtain ⟨e',rdy',se',invoke⟩ := hc j (S.erase j) e a rdy se ea.safe_end la
  let b := a.putIndex 154 (oracle (S.erase j)).toNat
  have lb : Layout b base j.val (S.erase j) := by simpa [Layout,b] using la
  obtain ⟨c,ec,lc⟩ := reply_spec j b lb stored (oracle (S.erase j)) (by simp [b]) P ea.safe_end
  obtain ⟨t,et,lt⟩ := advance_spec c lc P ec.safe_end
  have run := (leaf_run P e se ea).seq (invoke.seq ((leaf_run P e' se' ec).seq (leaf_run P e' se' et)))
  exact ⟨e',t,rdy',se',et.safe_end,lt,run.mono (by omega)⟩

/-- The physical caller executes its exact list of remaining marked-coordinate tests.
Both the callee and every intermediate odd-bank step obey the shared scalar-height bound. -/
theorem markedLoop_run {n base bound : ℕ} (oracle : Finset (Fin n) → Bool) (call : Fragment)
    (P : K → Prop) (h0 : P 0) (ready : Memory K → Prop) (hc : FragmentRealizes call P ready base bound oracle)
    (lo : 152 ≤ base) (k l : ℕ) (endAt : k+l=n) (S : Finset (Fin n)) (e m : Memory K)
    (rdy : ready e) (se : e.AllData P) (sm : m.AllData P) (hm : Layout m base k S) :
    ∃ e' t, ready e' ∧ e'.AllData P ∧ t.AllData P ∧ Layout t base n (deleteCoordinates oracle (suffix k l endAt) S).1 ∧
      (markedLoop call).Run P (Odd.memory e m) (l*(bound+34)+1) (Odd.memory e' t) := by
  induction l generalizing k S e m with
  | zero =>
    have hk : k=n := by omega
    have test : (Odd.cond (.addrLT 152 150)).test (Odd.memory e m)=false := by
      rw [Odd.cond_test]; simp [Cond.test,hm.1,hm.2.2.1,hk]
    exact ⟨e,m,rdy,se,sm,by simpa [suffix,deleteCoordinates,hk] using hm,
      by simpa only [markedLoop,Nat.zero_mul,Nat.zero_add] using Fragment.Run.loopFalse test (Odd.allData e m se sm) (markedIteration call)⟩
  | succ l ih =>
    let j : Fin n := ⟨k,by omega⟩
    have test : (Odd.cond (.addrLT 152 150)).test (Odd.memory e m)=true := by
      rw [Odd.cond_test]; simp [Cond.test,hm.1,hm.2.2.1,show k < n by omega]
    obtain ⟨e',a,hr,sa,sa',la,one⟩ := iteration_run oracle call P h0 ready hc lo j S e m rdy se sm hm
    obtain ⟨e'',t,hr',st,st',lt,rest⟩ := ih (k+1) (by omega) _ e' a hr sa sa' la
    refine ⟨e'',t,hr',st,st',?_,(Fragment.Run.loopTrue test one rest).mono ?_⟩
    · rw [suffix_succ,deleteCoordinates]; exact lt
    · rw [Nat.succ_mul]; omega

/-- Starting with an uninitialized flag window, this is an ordinary caller fragment
whose calls may themselves execute arbitrary (linked) finite RAM programs. -/
theorem markedSearch_run {m base bound : ℕ} (oracle : Finset (Fin (m+1)) → Bool) (call : Fragment)
    (P : K → Prop) (zero : P 0) (one : P 1) (ready : Memory K → Prop)
    (hc : FragmentRealizes call P ready base bound oracle) (lo : 152 ≤ base) (e v : Memory K)
    (rdy : ready e) (se : e.AllData P) (sv : v.AllData P) (hn : v.index 150=m+1) (hb : v.index 151=base) :
    ∃ e' t, ready e' ∧ e'.AllData P ∧ t.AllData P ∧
      Layout t base (m+1) (deleteCoordinates oracle ((List.finRange (m+1)).erase 0) Finset.univ).1 ∧
      (markedSearch call).Run P (Odd.memory e v) (4*(5*(m+1)+7)+(m*(bound+34)+1)) (Odd.memory e' t) := by
  obtain ⟨a,init,ha,_,_⟩ := initFlags_spec P one v (m+1) base sv hn hb lo
  obtain ⟨e',t,rdy',se',st,ht,run⟩ := markedLoop_run oracle call P zero ready hc lo 1 m
    (Nat.add_comm 1 m) _ e a rdy se init.safe_end ha
  have sched : suffix 1 m (Nat.add_comm 1 m) = (List.finRange (m+1)).erase 0 := by
    rw [← List.ofFn_id,List.ofFn_succ]; simp only [id_eq,List.erase_cons_head,suffix]
    congr 1; funext i; apply Fin.ext; simp [Nat.add_comm]
  exact ⟨e',t,rdy',se',st,sched ▸ ht,(leaf_run P e se init).seq run⟩

end SupportRAM
end Recovery
end LinearProgramming
end Optimization
end OAI
