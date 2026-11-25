import OAI.Optimization.LinearProgramming.RAM.Loops
import OAI.Optimization.LinearProgramming.Geometry.MinimalSupport

/-! A fixed scalar-RAM loop for the exact ordered coordinate tests in Section 2.  The
callee reads the *actual* proposed support in a contiguous scalar flag array.  The
current flag is saved across the call and restored precisely on a negative response. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace SupportRAM

open RAM
open _root_.OAI.Optimization.LinearProgramming.Geometry (deleteCoordinates)

/-- Persistent index headers: 150 dimension, 151 flag base, 152 current coordinate,
153 address of its flag. A decision returns its Boolean in index 154. -/
def Layout {K : Type*} [Zero K] [One K] {n : ℕ} (m : Memory K) (base cursor : ℕ)
    (s : Finset (Fin n)) : Prop :=
  m.index 150 = n ∧ m.index 151 = base ∧ m.index 152 = cursor ∧ m.index 153 = base + cursor ∧
    ∀ j : Fin n, m.data (base+j.val) = if j ∈ s then 1 else 0

def clear : Block := .seq (.op (.load 150 153)) (.seq (.op (.const 151 0)) (.op (.store 153 151)))

def applyReply : Block := .seq (.op (.addrConst 155 0))
  (.branch (.addrLT 155 154) .skip (.op (.store 153 150)))

def advance : Block := .seq (.op (.incr 152 152)) (.op (.incr 153 153))

def iteration (call : Block) : Block := .seq clear (.seq call (.seq applyReply advance))

def program (call : Block) : Block := .loop (.addrLT 152 150) (iteration call)

universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private abbrev Safe (P : K → Prop) (m : Memory K) := ∀ a, P (m.data a)

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
private theorem safeWrite {P : K → Prop} {m : Memory K} (hm : Safe P m) (a : ℕ) {v : K} (hv : P v) :
    Safe P (m.putData a v) := by
  intro i
  by_cases h : i=a
  · subst i; simpa
  · simpa [Memory.putData_ne _ h] using hm i

theorem clear_spec {n base : ℕ} {S : Finset (Fin n)} (j : Fin n) (m : Memory K)
    (hq : Layout m base j.val S) (hb : 152 ≤ base) (P : K → Prop) (hs : Safe P m) (h0 : P 0) :
    ∃ t, Block.Eval (Safe P) clear m 3 t ∧ Layout t base j.val (S.erase j) ∧
      t.data 150 = (if j ∈ S then 1 else 0) := by
  rcases hq with ⟨hn,hb',hj,hp,hm⟩
  let a := m.putData 150 (m.data (m.index 153))
  let b := a.putData 151 (0 : K)
  let t := b.putData (b.index 153) (b.data 151)
  have sa : Safe P a := safeWrite hs _ (hs _)
  have sb : Safe P b := safeWrite sa _ h0
  have st : Safe P t := safeWrite sb _ (sb _)
  have e₁ := Block.Eval.op_load m 150 153 hs sa
  have e₂ : Block.Eval (Safe P) (.op (.const 151 0)) a 1 b := by
    simpa only [Rat.cast_zero] using Block.Eval.op_const a 151 0 sa (by simpa only [Rat.cast_zero] using sb)
  have e₃ := Block.Eval.op_store b 153 151 sb st
  refine ⟨t,e₁.seq (e₂.seq e₃),⟨hn,hb',hj,hp,?_⟩,?_⟩
  · intro i
    by_cases hij : i=j
    · subst i; simp [t,b,a,hp]
    · have nd : base+i.val ≠ base+j.val := fun h => hij (Fin.ext (by omega))
      have n150 : base+i.val ≠ 150 := by omega
      have n151 : base+i.val ≠ 151 := by omega
      simp [t,b,a,hp,Memory.putData_ne _ nd,Memory.putData_ne _ n150,
        Memory.putData_ne _ n151,hm,hij]
  · have nd : 150 ≠ base+j.val := by omega
    simp [t,b,a,hp,Memory.putData_ne _ nd,hm]

/-- `call` can be any actual structured scalar-RAM subroutine. The saved original flag
must survive the call; its scratch arrays may change. -/
def Realizes {n : ℕ} (call : Block) (P : K → Prop) (base bound : ℕ) (oracle : Finset (Fin n) → Bool) : Prop :=
  ∀ (j : Fin n) (S : Finset (Fin n)) (m : Memory K), Safe P m → Layout m base j.val S →
    ∃ t k, k ≤ bound ∧ Block.Eval (Safe P) call m k t ∧ Layout t base j.val S ∧
      t.index 154 = (oracle S).toNat ∧ t.data 150 = m.data 150

theorem reply_spec {n base : ℕ} {S : Finset (Fin n)} (j : Fin n) (m : Memory K)
    (hq : Layout m base j.val (S.erase j)) (saved : m.data 150 = if j ∈ S then 1 else 0)
    (ans : Bool) (hans : m.index 154=ans.toNat) (P : K → Prop) (hs : Safe P m) :
    ∃ t, Block.Eval (Safe P) applyReply m 3 t ∧ Layout t base j.val (if ans then S.erase j else S) := by
  rcases hq with ⟨hn,hb,hj,hp,hm⟩
  let a := m.putIndex 155 0
  have sa : Safe P a := hs
  have e := Block.Eval.op_addrConst m 155 0 hs sa
  cases ans with
  | true =>
    have test : (Cond.addrLT 155 154).test a = true := by simp [Cond.test,a,hans]
    refine ⟨a,e.seq (.branchTrue test (.skip sa)),?_⟩
    simpa [Layout,a] using And.intro hn (And.intro hb (And.intro hj (And.intro hp hm)))
  | false =>
    have test : (Cond.addrLT 155 154).test a = false := by simp [Cond.test,a,hans]
    let t := a.putData (a.index 153) (a.data 150)
    have st : Safe P t := safeWrite sa _ (sa _)
    refine ⟨t,e.seq (.branchFalse test (Block.Eval.op_store a 153 150 sa st)),?_⟩
    refine ⟨by simpa [t,a] using hn,by simpa [t,a] using hb,by simpa [t,a] using hj,
      by simpa [t,a] using hp,?_⟩
    intro i
    by_cases hij : i=j
    · subst i; simp [t,a,hp,saved]
    · have nd : base+i.val ≠ base+j.val := fun h => hij (Fin.ext (by omega))
      simp [t,a,hp,Memory.putData_ne _ nd,hm,hij]

theorem advance_spec {n base cursor : ℕ} {S : Finset (Fin n)} (m : Memory K)
    (hq : Layout m base cursor S) (P : K → Prop) (hs : Safe P m) :
    ∃ t, Block.Eval (Safe P) advance m 2 t ∧ Layout t base (cursor+1) S := by
  rcases hq with ⟨hn,hb,hj,hp,hm⟩
  let a := m.putIndex 152 (m.index 152 + 1)
  let t := a.putIndex 153 (a.index 153 + 1)
  have sa : Safe P a := hs
  have st : Safe P t := hs
  refine ⟨t,(Block.Eval.op_incr m 152 152 hs sa).seq (Block.Eval.op_incr a 153 153 sa st),?_⟩
  simp [Layout,t,a,hn,hb,hj,hp,hm,Nat.add_assoc]

private theorem iteration_spec {n base limit : ℕ} (oracle : Finset (Fin n) → Bool)
    (call : Block) (P : K → Prop) (h0 : P 0) (hc : Realizes call P base limit oracle) (hb : 152 ≤ base)
    (j : Fin n) (S : Finset (Fin n)) (m : Memory K) (hs : Safe P m) (hm : Layout m base j.val S) :
    ∃ t k, k ≤ limit+8 ∧ Block.Eval (Safe P) (iteration call) m k t ∧
      Layout t base (j.val+1) (if oracle (S.erase j) then S.erase j else S) := by
  obtain ⟨a,ea,ha,sa⟩ := clear_spec j m hm hb P hs h0
  obtain ⟨b,k,hk,eb,hb',ans,saved⟩ := hc j (S.erase j) a ea.safe_end ha
  obtain ⟨c,ec,hc'⟩ := reply_spec j b hb' (saved.trans sa) _ ans P eb.safe_end
  obtain ⟨t,ed,ht⟩ := advance_spec c hc' P ec.safe_end
  exact ⟨t,_,by omega,ea.seq (eb.seq (ec.seq ed)),ht⟩

/-- Consecutive indices visited by the physical pointer, with its public upper bound. -/
def suffix {n : ℕ} (k count : ℕ) (h : k+count=n) : List (Fin n) :=
  List.ofFn fun i : Fin count => ⟨k+i.val,by omega⟩

theorem suffix_succ {n k l : ℕ} (h : k+(l+1)=n) :
    suffix k (l+1) h = (⟨k,by omega⟩ : Fin n) :: suffix (k+1) l (by omega) := by
  simp only [suffix,List.ofFn_succ]
  congr 1
  congr 1
  funext i
  apply Fin.ext
  simp [Nat.add_comm,Nat.add_left_comm]

/-- All instructions, including final false guard, participate in the common scalar bound.
The support returned here is the support of the manuscript's exact greedy search. -/
theorem program_spec {n base limit : ℕ} (oracle : Finset (Fin n) → Bool)
    (call : Block) (P : K → Prop) (h0 : P 0) (hc : Realizes call P base limit oracle) (hb : 152 ≤ base)
    (k l : ℕ) (endAt : k+l=n) (S : Finset (Fin n)) (m : Memory K) (hs : Safe P m)
    (hm : Layout m base k S) :
    ∃ t cost, cost ≤ l*(limit+10)+1 ∧ Block.Eval (Safe P) (program call) m cost t ∧
      Layout t base n (deleteCoordinates oracle (suffix k l endAt) S).1 := by
  induction l generalizing k S m with
  | zero =>
    have hk : k=n := by omega
    have test : (Cond.addrLT 152 150).test m = false := by simp [Cond.test,hm.1,hm.2.2.1,hk]
    exact ⟨m,1,by simp,.loopFalse test hs,by simpa [suffix,deleteCoordinates,hk] using hm⟩
  | succ l ih =>
    let j : Fin n := ⟨k,by omega⟩
    have hj : j.val=k := rfl
    have test : (Cond.addrLT 152 150).test m = true := by simp [Cond.test,hm.1,hm.2.2.1,show k<n by omega]
    obtain ⟨a,c,hc',ea,ha⟩ := iteration_spec oracle call P h0 hc hb j S m hs hm
    obtain ⟨t,c',hc'',eb,ht⟩ := ih (k+1) (by omega) _ a ea.safe_end ha
    refine ⟨t,_,?_,.loopTrue test ea eb,?_⟩
    · rw [Nat.succ_mul]; omega
    · rw [suffix_succ,deleteCoordinates]
      exact ht

/-- Public entry at the first nonanchor coordinate. -/
theorem marked_program_spec {m base limit : ℕ} (oracle : Finset (Fin (m+1)) → Bool)
    (call : Block) (P : K → Prop) (h0 : P 0) (hc : Realizes call P base limit oracle) (hb : 152 ≤ base)
    (v : Memory K) (hs : Safe P v) (hv : Layout v base 1 (Finset.univ : Finset (Fin (m+1)))) :
    ∃ t cost, cost ≤ m*(limit+10)+1 ∧ Block.Eval (Safe P) (program call) v cost t ∧
      Layout t base (m+1) (deleteCoordinates oracle ((List.finRange (m+1)).erase 0) Finset.univ).1 := by
  have sched : suffix 1 m (Nat.add_comm 1 m) = (List.finRange (m+1)).erase 0 := by
    rw [← List.ofFn_id, List.ofFn_succ]
    simp only [id_eq,List.erase_cons_head,suffix]
    congr 1; funext i; apply Fin.ext; simp [Nat.add_comm]
  simpa only [sched] using program_spec oracle call P h0 hc hb 1 m (Nat.add_comm 1 m) _ v hs hv

end SupportRAM
end Recovery
end LinearProgramming
end Optimization
end OAI
