import OAI.Optimization.LinearProgramming.BitRAM.IndexScript
import OAI.Optimization.LinearProgramming.Recovery.SupportRAM

/-! Compact the actual 0/1 independent-row mask into an array of row addresses.
The count is an address, so later code can allocate and traverse the packed matrix. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace RowIndex

open RAM RAM.Block
open OAI.Optimization.LinearProgramming.BitRAM.IndexScript

private def recordOps : List Instr := [.addrStore 166 163,.incr 165 165,.incr 166 166]
private def nextOps : List Instr := [.incr 163 163,.incr 164 164]
private def initOps : List Instr := [.addrConst 163 0,.addrCopy 164 161,.addrConst 165 0,.addrCopy 166 162]

def body : Block := .seq (.op (.load 6 164))
  (.seq (.branch (.scalarLT 5 6) (.straight recordOps) .skip) (.straight nextOps))

def program : Block := .seq (.op (.const 5 0)) (.seq (.straight initOps) (.loop (.addrLT 163 160) body))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private abbrev Safe (P : K → Prop) (m : Memory K) := ∀ a, P (m.data a)

/-- The physically written row-index array is address-valued and has an explicit count. -/
structure Represents {n : ℕ} (perm : ℕ) (rows : List (Fin n)) (m : Memory K) : Prop where
  count : m.index 165 = rows.length
  entries : ∀ k j, rows[k]? = some j → m.index (perm+k) = j.val

private structure At {n : ℕ} (S : Finset (Fin n)) (src perm : ℕ) (orig m : Memory K)
    (k : ℕ) (rows : List (Fin n)) : Prop where
  dim : m.index 160=n
  cursor : m.index 163=k
  flagsPtr : m.index 164=src+k
  permPtr : m.index 166=perm+rows.length
  rep : Represents perm rows m
  length_le : rows.length ≤ k
  zero : m.data 5=0
  flags : ∀ i : Fin n, m.data (src+i.val) = if i∈S then 1 else 0
  data : ∀ a, a≠5 → a≠6 → m.data a=orig.data a
  index : ∀ p, p≠163 → p≠164 → p≠165 → p≠166 → (p < perm ∨ perm+n ≤ p) → m.index p=orig.index p

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
private theorem writeSafe (P : K → Prop) (m : Memory K) (hs : Safe P m) (a : ℕ) (x : K) (hx : P x) :
    Safe P (m.putData a x) := by
  intro i
  by_cases h : i=a
  · subst i; simpa
  · simpa [Memory.putData_ne _ h] using hs i

private theorem recordOK (i : Instr) (hi : i∈recordOps) : allowed i = true := by
  simp [recordOps] at hi; rcases hi with rfl|rfl|rfl <;> rfl
private theorem nextOK (i : Instr) (hi : i∈nextOps) : allowed i = true := by
  simp [nextOps] at hi; rcases hi with rfl|rfl <;> rfl
private theorem initOK (i : Instr) (hi : i∈initOps) : allowed i = true := by
  simp [initOps] at hi; rcases hi with rfl|rfl|rfl|rfl <;> rfl

private theorem step {n src perm : ℕ} (P : K → Prop) (S : Finset (Fin n)) (lo : 7 ≤ src) (hi : 167 ≤ perm)
    (orig m : Memory K) (j : Fin n) (rows : List (Fin n)) (h : At S src perm orig m j.val rows)
    (hm : Safe P m) :
    ∃ t c, c ≤ 8 ∧ Eval (Safe P) body m c t ∧ At S src perm orig t (j.val+1) (rows ++ (if j∈S then [j] else [])) := by
  let a := m.putData 6 (m.data (m.index 164))
  have sa : Safe P a := writeSafe P m hm 6 _ (hm _)
  have load := Eval.op_load m 6 164 hm sa
  have flag := h.flags j
  have a5 : a.data 5=0 := by simpa [a] using h.zero
  have a6 : a.data 6 = if j∈S then 1 else 0 := by simpa [a,h.flagsPtr] using flag
  have ainds : a.index=m.index := rfl
  have aflags (i : Fin n) : a.data (src+i.val) = if i∈S then 1 else 0 := by
    simpa [a,Memory.putData_ne _ (by omega : src+i.val≠6)] using h.flags i
  have adata (p : ℕ) (h5 : p≠5) (h6 : p≠6) : a.data p=orig.data p :=
    (Memory.putData_ne _ h6 _).trans (h.data p h5 h6)
  by_cases hj : j∈S
  · have test : (Cond.scalarLT 5 6).test a=true := by simp [Cond.test,a5,a6,hj]
    let b : Memory K := ⟨a.data,run recordOps a.index⟩
    let t : Memory K := ⟨b.data,run nextOps b.index⟩
    have recorded : Eval (Safe P) (.straight recordOps) a 3 b := correct recordOps recordOK a sa
    have nxt := correct nextOps nextOK b sa
    refine ⟨t,8,by decide,load.seq ((Eval.branchTrue test recorded).seq nxt),?_⟩
    rw [ite_eq_left hj]
    have p163 : 163≠perm+rows.length := by omega
    have p164 : 164≠perm+rows.length := by omega
    have p165 : 165≠perm+rows.length := by omega
    have p166 : 166≠perm+rows.length := by omega
    have p160 : 160≠perm+rows.length := by omega
    have eqof (p : ℕ) (x : p≠163) (y : p≠164) (z : p≠165) (w : p≠166) (v : p≠perm+rows.length) :
        t.index p=m.index p := by
      simp [t,b,ainds,nextOps,recordOps,run,update,x,y,z,w,h.permPtr,v]
    refine ⟨(eqof 160 (by decide) (by decide) (by decide) (by decide) p160).trans h.dim,
      ?_,?_,?_,⟨?_,?_⟩,by simpa using Nat.succ_le_succ h.length_le,a5,aflags,adata,?_⟩
    · simp [t,b,ainds,nextOps,recordOps,run,update,h.permPtr,p163,p164,p165,p166,h.cursor]
    · simp [t,b,ainds,nextOps,recordOps,run,update,h.permPtr,p163,p164,p165,p166,h.flagsPtr,Nat.add_assoc]
    · simp [t,b,ainds,nextOps,recordOps,run,update,h.permPtr,p163,p164,p165,p166,Nat.add_assoc]
    · simp [t,b,ainds,nextOps,recordOps,run,update,h.permPtr,p163,p164,p165,p166,h.rep.count]
    · intro k i he
      have h163 : perm+k≠163 := by omega
      have h164 : perm+k≠164 := by omega
      have h165 : perm+k≠165 := by omega
      have h166 : perm+k≠166 := by omega
      by_cases hk : k < rows.length
      · have hv : perm+k≠perm+rows.length := by omega
        exact (eqof _ h163 h164 h165 h166 hv).trans (h.rep.entries k i (by simpa [List.getElem?_append,hk] using he))
      · have hlen : k=rows.length := by
          have hl := (List.getElem?_eq_some_iff.mp he).choose; simp at hl; omega
        subst k
        have heq : i=j := by simpa [List.getElem?_append] using he.symm
        subst i
        simp [t,b,ainds,nextOps,recordOps,run,update,h163,h164,h165,h166,h.permPtr,h.cursor]
    · intro p x y z w v
      have dj := j.isLt
      have dl := h.length_le
      have off : p≠perm+rows.length := by omega
      exact (eqof _ x y z w off).trans (h.index p x y z w v)
  · have test : (Cond.scalarLT 5 6).test a=false := by simp [Cond.test,a5,a6,hj]
    let t : Memory K := ⟨a.data,run nextOps a.index⟩
    have nxt := correct nextOps nextOK a sa
    refine ⟨t,4,by decide,load.seq ((Eval.branchFalse test (.skip sa)).seq nxt),?_⟩
    simp only [ite_eq_right hj,List.append_nil]
    have eqof (p : ℕ) (x : p≠163) (y : p≠164) : t.index p=m.index p := by simp [t,ainds,nextOps,run,update,x,y]
    refine ⟨(eqof 160 (by decide) (by decide)).trans h.dim,?_,?_,(eqof 166 (by decide) (by decide)).trans h.permPtr,
      ⟨(eqof 165 (by decide) (by decide)).trans h.rep.count,?_⟩,h.length_le.trans (Nat.le_succ _),a5,aflags,adata,?_⟩
    · simp [t,ainds,nextOps,run,update,h.cursor]
    · simp [t,ainds,nextOps,run,update,h.flagsPtr,Nat.add_assoc]
    · intro k i he; exact (eqof _ (by omega) (by omega)).trans (h.rep.entries k i he)
    · intro p x y z w v; exact (eqof _ x y).trans (h.index p x y z w v)

/-- The result indices enumerate exactly the true mask rows in their original order. -/
theorem program_spec {n src perm : ℕ} (P : K → Prop) (S : Finset (Fin n)) (s : Memory K) (hs : Safe P s)
    (h0 : P 0) (h160 : s.index 160=n) (h161 : s.index 161=src) (h162 : s.index 162=perm)
    (lo : 7 ≤ src) (hi : 167 ≤ perm) (flags : ∀ i : Fin n, s.data (src+i.val)=if i∈S then 1 else 0) :
    ∃ t k, k ≤ 10*n+6 ∧ Eval (Safe P) program s k t ∧ Represents perm ((List.finRange n).filter (·∈S)) t ∧
      (∀ a, a≠5 → a≠6 → t.data a=s.data a) ∧
      ∀ p, p≠163 → p≠164 → p≠165 → p≠166 → (p < perm ∨ perm+n ≤ p) → t.index p=s.index p := by
  let initial := s.putData 5 (0 : K)
  let a : Memory K := ⟨initial.data,run initOps initial.index⟩
  have si : Safe P initial := writeSafe P s hs 5 _ h0
  have ei : Eval (Safe P) (.op (.const 5 0)) s 1 initial := by
    simpa only [Rat.cast_zero] using Eval.op_const s 5 0 hs (by simpa only [Rat.cast_zero] using si)
  have ea := correct initOps initOK initial si
  have hstart : At S src perm s a 0 [] := by
    refine ⟨?_,?_,?_,?_,⟨?_,by simp⟩,by simp,by simp [a,initial],?_,?_,?_⟩
    · simp [a,initial,initOps,run,update,h160]
    · simp [a,initial,initOps,run,update]
    · simp [a,initial,initOps,run,update,h161]
    · simp [a,initial,initOps,run,update,h162]
    · simp [a,initial,initOps,run,update]
    · intro j; simpa [a,initial,Memory.putData_ne _ (by omega : src+j.val≠5)] using flags j
    · intro p x _; simp [a,initial,Memory.putData_ne _ x]
    · intro p x y z w _; simp [a,initial,initOps,run,update,x,y,z,w]
  let walk (k l : ℕ) (endAt : k+l=n) := SupportRAM.suffix k l endAt
  have all (l k : ℕ) (endAt : k+l=n) (v : Memory K) (rows : List (Fin n)) (sv : Safe P v)
      (hv : At S src perm s v k rows) :
      ∃ t c, c ≤ 10*l+1 ∧ Eval (Safe P) (.loop (.addrLT 163 160) body) v c t ∧
        At S src perm s t n (rows ++ (walk k l endAt).filter (·∈S)) := by
    induction l generalizing k v rows with
    | zero =>
      have hk : k=n := by omega
      exact ⟨v,1,by simp,.loopFalse (by simp [Cond.test,hv.cursor,hv.dim,hk]) sv,by simpa [walk,SupportRAM.suffix,hk] using hv⟩
    | succ l ih =>
      let j : Fin n := ⟨k,by omega⟩
      have test : (Cond.addrLT 163 160).test v=true := by simp [Cond.test,hv.cursor,hv.dim,show k < n by omega]
      obtain ⟨u,c,hc,eu,hu⟩ := step P S lo hi s v j rows hv sv
      obtain ⟨t,d,hd,et,ht⟩ := ih (k+1) (by omega) u _ eu.safe_end hu
      have tail : walk k (l+1) endAt = j :: walk (k+1) l (by omega) := by
        simp only [walk,SupportRAM.suffix,List.ofFn_succ]; congr 1; congr 1
        funext i; apply Fin.ext; simp [Nat.add_comm,Nat.add_left_comm]
      refine ⟨t,_,by omega,.loopTrue test eu et,?_⟩
      rw [tail]; by_cases hmem : j∈S <;> simpa [hmem,List.append_assoc] using ht
  obtain ⟨t,k,hk,et,ht⟩ := all n 0 (by omega) a [] si hstart
  have sched : walk 0 n (by omega) = List.finRange n := by
    rw [← List.ofFn_id]; dsimp [walk,SupportRAM.suffix]; congr 1; funext j; apply Fin.ext; simp
  refine ⟨t,_,by change 1+(4+k) ≤ _; omega,ei.seq (ea.seq et),?_,ht.data,ht.index⟩
  simpa [sched] using ht.rep

end RowIndex
end Recovery
end LinearProgramming
end Optimization
end OAI
