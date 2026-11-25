import OAI.Optimization.LinearProgramming.Recovery.SupportContextFrame
import OAI.Optimization.LinearProgramming.Recovery.SupportFragment

/-! The same physical greedy support code with a protected odd-caller context available
at every recursive decision request, covering the original LP and the fixed opposite basis. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace SupportRAM

open RAM RAM.Callable
open _root_.OAI.Optimization.LinearProgramming.Geometry (deleteCoordinates)

universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem initFlags_framed (P : K → Prop) (one : P 1) (m : Memory K) (n base : ℕ)
    (hs : m.AllData P) (hn : m.index 150=n) (hb : m.index 151=base) (lo : 152 ≤ base) :
    ∃ t, Block.Eval (Memory.AllData P) initFlags m (5*n+7) t ∧
      Layout t base 1 (Finset.univ : Finset (Fin n)) ∧ Frame base n m t := by
  obtain ⟨t,run,layout,ds,ix⟩ := initFlags_spec P one m n base hs hn hb lo
  exact ⟨t,run,layout,⟨fun p h _ o => ds p h o,fun p h i _ _ => ix p h i⟩⟩

def ContextRealizes {n : ℕ} (call : Fragment) (P : K → Prop) (ready context : Memory K → Prop)
    (base bound : ℕ) (oracle : Finset (Fin n) → Bool) : Prop :=
  ∀ (j : Fin n) (S : Finset (Fin n)) (callee caller : Memory K),
    ready callee → callee.AllData P → caller.AllData P → Layout caller base j.val S → context caller →
    ∃ callee', ready callee' ∧ callee'.AllData P ∧ call.Run P (Odd.memory callee caller) bound
      (Odd.memory callee' (caller.putIndex 154 (oracle S).toNat))

theorem markedIteration_run_withContext {n base bound : ℕ} (oracle : Finset (Fin n) → Bool)
    (call : Fragment) (P : K → Prop) (h0 : P 0) (ready context : Memory K → Prop)
    (stable : StableContext base n context) (hc : ContextRealizes call P ready context base bound oracle)
    (lo : 152 ≤ base) (j : Fin n) (S : Finset (Fin n)) (e m : Memory K) (rdy : ready e)
    (se : e.AllData P) (sm : m.AllData P) (hm : Layout m base j.val S) (cm : context m) :
    ∃ e' t, ready e' ∧ e'.AllData P ∧ t.AllData P ∧ context t ∧ Frame base n m t ∧
      Layout t base (j.val+1) (if oracle (S.erase j) then S.erase j else S) ∧
      (markedIteration call).Run P (Odd.memory e m) (bound+32) (Odd.memory e' t) := by
  obtain ⟨a,ea,la,stored⟩ := clear_spec j m hm lo P sm h0
  have fa := clear_frame j m a hm ea
  obtain ⟨e',rdy',se',invoke⟩ := hc j (S.erase j) e a rdy se ea.safe_end la (stable cm fa)
  let b := a.putIndex 154 (oracle (S.erase j)).toNat
  have fb : Frame base n a b := Frame.put_index base n a 154 _ (by decide)
  have lb : Layout b base j.val (S.erase j) := by simpa [Layout,b] using la
  have tag : b.index 154=(oracle (S.erase j)).toNat := by simp [b]
  obtain ⟨c,ec,lc⟩ := reply_spec j b lb stored (oracle (S.erase j)) tag P ea.safe_end
  have fc := reply_frame j b c lb (oracle (S.erase j)) tag ec
  obtain ⟨t,et,lt⟩ := advance_spec c lc P ec.safe_end
  have ft := ((fa.trans fb).trans fc).trans (advance_frame base n c t et)
  have run := (Odd.leaf_run P e se ea).seq
    (invoke.seq ((Odd.leaf_run P e' se' ec).seq (Odd.leaf_run P e' se' et)))
  exact ⟨e',t,rdy',se',et.safe_end,stable cm ft,ft,lt,run.mono (by omega)⟩

theorem markedLoop_run_withContext {n base bound : ℕ} (oracle : Finset (Fin n) → Bool)
    (call : Fragment) (P : K → Prop) (h0 : P 0) (ready context : Memory K → Prop)
    (stable : StableContext base n context) (hc : ContextRealizes call P ready context base bound oracle)
    (lo : 152 ≤ base) (k l : ℕ) (endAt : k+l=n) (S : Finset (Fin n)) (e m : Memory K)
    (rdy : ready e) (se : e.AllData P) (sm : m.AllData P) (hm : Layout m base k S) (cm : context m) :
    ∃ e' t, ready e' ∧ e'.AllData P ∧ t.AllData P ∧ context t ∧ Frame base n m t ∧
      Layout t base n (deleteCoordinates oracle (suffix k l endAt) S).1 ∧
      (markedLoop call).Run P (Odd.memory e m) (l*(bound+34)+1) (Odd.memory e' t) := by
  induction l generalizing k S e m with
  | zero =>
    have hk : k=n := by omega
    have test : (Odd.cond (.addrLT 152 150)).test (Odd.memory e m)=false := by
      rw [Odd.cond_test]; simp [Cond.test,hm.1,hm.2.2.1,hk]
    exact ⟨e,m,rdy,se,sm,cm,Frame.refl base n m,
      by simpa [suffix,deleteCoordinates,hk] using hm,
      by simpa only [markedLoop,Nat.zero_mul,Nat.zero_add] using
        Fragment.Run.loopFalse test (Odd.allData e m se sm) (markedIteration call)⟩
  | succ l ih =>
    let j : Fin n := ⟨k,by omega⟩
    have test : (Odd.cond (.addrLT 152 150)).test (Odd.memory e m)=true := by
      rw [Odd.cond_test]; simp [Cond.test,hm.1,hm.2.2.1,show k<n by omega]
    obtain ⟨e',a,hr,sa,sa',ca,fa,la,one⟩ :=
      markedIteration_run_withContext oracle call P h0 ready context stable hc lo j S e m rdy se sm hm cm
    obtain ⟨e'',t,hr',st,st',ct,ft,lt,rest⟩ := ih (k+1) (by omega) _ e' a hr sa sa' la ca
    refine ⟨e'',t,hr',st,st',ct,fa.trans ft,?_,(Fragment.Run.loopTrue test one rest).mono ?_⟩
    · rw [suffix_succ,deleteCoordinates]; exact lt
    · rw [Nat.succ_mul]; omega

/-- The compiled callback can require all read-only tape and matrix data in the caller
state. The real instructions keep that context on every trial, through ordinary return. -/
theorem markedSearch_run_withContext {m base bound : ℕ} (oracle : Finset (Fin (m+1)) → Bool)
    (call : Fragment) (P : K → Prop) (zero : P 0) (one : P 1) (ready context : Memory K → Prop)
    (stable : StableContext base (m+1) context)
    (hc : ContextRealizes call P ready context base bound oracle) (lo : 152 ≤ base) (e v : Memory K)
    (rdy : ready e) (se : e.AllData P) (sv : v.AllData P) (hn : v.index 150=m+1)
    (hb : v.index 151=base) (cv : context v) :
    ∃ e' t, ready e' ∧ e'.AllData P ∧ t.AllData P ∧ context t ∧ Frame base (m+1) v t ∧
      Layout t base (m+1) (deleteCoordinates oracle ((List.finRange (m+1)).erase 0) Finset.univ).1 ∧
      (markedSearch call).Run P (Odd.memory e v) (4*(5*(m+1)+7)+(m*(bound+34)+1)) (Odd.memory e' t) := by
  obtain ⟨a,init,ha,frame⟩ := initFlags_framed P one v (m+1) base sv hn hb lo
  obtain ⟨e',t,rdy',se',st,ct,tail,ht,run⟩ := markedLoop_run_withContext oracle call P zero ready
    context stable hc lo 1 m (Nat.add_comm 1 m) _ e a rdy se init.safe_end ha (stable cv frame)
  have sched : suffix 1 m (Nat.add_comm 1 m) = (List.finRange (m+1)).erase 0 := by
    rw [← List.ofFn_id,List.ofFn_succ]; simp only [id_eq,List.erase_cons_head,suffix]
    congr 1; funext i; apply Fin.ext; simp [Nat.add_comm]
  exact ⟨e',t,rdy',se',st,ct,frame.trans tail,sched ▸ ht,(Odd.leaf_run P e se init).seq run⟩

end SupportRAM
end Recovery
end LinearProgramming
end Optimization
end OAI
