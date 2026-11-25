import OAI.Optimization.LinearProgramming.NativePrice.RatRAM

/-! Decode a vector of rational prices into disjoint contiguous scalar registers. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace NativePrice

open RAM RAM.Block OracleSpec

private def vectorCell : Block :=
  .seq ratBlock <| .straight [.store 11 3,.incr 11 11,.incr 10 10]

private def vectorLoop : Block := .loop (.addrLT 10 0) vectorCell

/-- Address registers 0, 3 and 9 hold the dimension, input cursor and output base.
Address registers 10 and 11 become the count and output cursor. -/
def vectorBlock : Block :=
  .seq (.op (.addrConst 10 0)) (.seq (.op (.addrCopy 11 9)) vectorLoop)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem vectorLoop_spec (P : K → Prop) (xs : List ℚ) (s : Memory K) (j c d : ℕ)
    (hn : s.index 0=j+xs.length) (hc : s.index 3=c) (hj : s.index 10=j)
    (hd : s.index 11=d) (hc9 : 9≤c) (hd9 : 9≤d)
    (hw : WordAt s c (xs.flatMap encodeRat))
    (hsep : d+xs.length≤c ∨ c+(xs.flatMap encodeRat).length≤d)
    (hm : s.AllData P)
    (hPnat : ∀ x ∈ xs, ∀ v : ℕ, v≤2^(max x.num.natAbs.bits.length x.den.bits.length) → P (v:K))
    (hPneg : ∀ x ∈ xs, P (x.num:K)) (hPq : ∀ x ∈ xs, P (x:K)) :
    ∃ t k, k≤24*(xs.flatMap encodeRat).length+45*xs.length+1 ∧
      Eval (Memory.AllData P) vectorLoop s k t ∧ t.index 3=c+(xs.flatMap encodeRat).length ∧
      (∀ l (hl : l<xs.length), t.data (d+l)=((xs[l]:ℚ):K)) ∧
      (∀ r, (r<3 ∨ 8<r) → (r<d ∨ d+xs.length≤r) → t.data r=s.data r) ∧
      ∀ r, (r<3 ∨ 6<r) → r≠10 → r≠11 → t.index r=s.index r := by
  induction xs generalizing s j c d with
  | nil =>
    have stop : (Cond.addrLT 10 0).test s=false := by simp [Cond.test,hn,hj]
    exact ⟨s,1,by simp,.loopFalse stop hm,by simpa using hc,fun l h => (Nat.not_lt_zero _ h).elim,
      fun _ _ _ => rfl,fun _ _ _ _ => rfl⟩
  | cons x xs ih =>
    have hlen : ((x::xs).flatMap encodeRat).length =
        (encodeRat x).length + (xs.flatMap encodeRat).length := by simp
    have hx : x∈x::xs := .head _
    have hlen' : (x::xs).length=xs.length+1 := rfl
    obtain ⟨hxword,hwords⟩ := wordAt_append.mp (show WordAt s c (encodeRat x ++ xs.flatMap encodeRat) from hw)
    obtain ⟨r,kr,hkr,rd,qval,cnext,df,af⟩ := ratBlock_spec P x s c hc hc9 hxword hm
      (hPnat x hx) (hPneg x hx) (hPq x hx)
    let v := r.putData d (x:K)
    let a := v.putIndex 11 (d+1)
    let u := a.putIndex 10 (j+1)
    have hv : v.AllData P := rd.safe_end.putData _ (hPq _ hx)
    have dp : r.index 11=d := (af _ (by decide)).trans hd
    have jp : r.index 10=j := (af _ (by decide)).trans hj
    have e0 : Eval (Memory.AllData P) (.op (.store 11 3)) r 1 v := by
      simpa only [v,dp,qval] using Eval.op_store r 11 3 rd.safe_end (by simpa only [dp,qval] using hv)
    have e1 : Eval (Memory.AllData P) (.op (.incr 11 11)) v 1 a := by
      simpa [a,v,dp] using Eval.op_incr v 11 11 hv hv
    have e2 : Eval (Memory.AllData P) (.op (.incr 10 10)) a 1 u := by
      simpa [u,a,v,jp] using Eval.op_incr a 10 10 hv hv
    have cell : Eval (Memory.AllData P) vectorCell s (kr+3) u :=
      rd.seq (e0.seq (e1.seq (e2.seq (.skip hv))))
    have nnext : u.index 0=j+1+xs.length := by
      have h := (af 0 (by decide)).trans hn
      simpa [u,a,v,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h
    have cc : u.index 3=c+(encodeRat x).length := by simpa [u,a,v] using cnext
    have uj : u.index 10=j+1 := by simp [u]
    have ud : u.index 11=d+1 := by simp [u,a]
    have tw : WordAt u (c+(encodeRat x).length) (xs.flatMap encodeRat) :=
      hwords.of_data (by
        intro k hk hl
        have ne : k≠d := by omega
        simpa [u,a,v,ne] using df k (by omega))
    have sep : d+1+xs.length≤c+(encodeRat x).length ∨
        c+(encodeRat x).length+(xs.flatMap encodeRat).length≤d+1 := by omega
    obtain ⟨z,kz,hkz,tail,cz,written,frame,addr⟩ := ih u (j+1) (c+(encodeRat x).length)
      (d+1) nnext cc uj ud (by omega) (by omega) tw sep hv
      (fun q hq => hPnat q (.tail _ hq)) (fun q hq => hPneg q (.tail _ hq)) (fun q hq => hPq q (.tail _ hq))
    have guard : (Cond.addrLT 10 0).test s=true := by
      simp only [Cond.test,decide_eq_true_eq,hn,hj,List.length_cons]
      omega
    refine ⟨z,1+(kr+3)+1+kz,by omega,Eval.loopTrue guard cell tail,by omega,?_,?_,?_⟩
    · intro l hl
      cases l with
      | zero =>
        have same := frame d (by omega) (.inl (by omega))
        simpa [u,a,v] using same
      | succ l =>
        have hl' : l<xs.length := by simpa using hl
        simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using written l hl'
    · intro k hk he
      have ne : k≠d := by omega
      have e := frame k hk (by omega)
      exact e.trans (by simpa [u,a,v,ne] using df k hk)
    · intro k h6 h10 h11
      have e : u.index k=r.index k := by simp [u,a,v,h10,h11]
      exact (addr k h6 h10 h11).trans (e.trans (af k h6))

theorem vectorBlock_spec (P : K → Prop) {N : ℕ} (p : Fin N→ℚ) (s : Memory K) (c d : ℕ)
    (hn : s.index 0=N) (hc : s.index 3=c) (hd : s.index 9=d) (hc9 : 9≤c) (hd9 : 9≤d)
    (hw : WordAt s c ((List.ofFn p).flatMap encodeRat))
    (hsep : d+N≤c ∨ c+((List.ofFn p).flatMap encodeRat).length≤d) (hm : s.AllData P)
    (hPnat : ∀ j, ∀ v : ℕ, v≤2^(max (p j).num.natAbs.bits.length (p j).den.bits.length) → P (v:K))
    (hPneg : ∀ j, P ((p j).num:K)) (hPq : ∀ j, P ((p j):K)) :
    ∃ t k, k≤(N+1)*(24*((List.ofFn p).flatMap encodeRat).length+50) ∧
      Eval (Memory.AllData P) vectorBlock s k t ∧ t.index 3=c+((List.ofFn p).flatMap encodeRat).length ∧
      (∀ j : Fin N, t.data (d+j.val)=((p j):K)) ∧
      (∀ j, (j<3 ∨ 8<j) → (j<d ∨ d+N≤j) → t.data j=s.data j) ∧
      ∀ j, (j<3 ∨ 6<j) → j≠10 → j≠11 → t.index j=s.index j := by
  let a := s.putIndex 10 0
  let b := a.putIndex 11 d
  have e0 : Eval (Memory.AllData P) (.op (.addrConst 10 0)) s 1 a := Eval.op_addrConst s 10 0 hm hm
  have e1 : Eval (Memory.AllData P) (.op (.addrCopy 11 9)) a 1 b := by
    simpa [a,b,hd] using Eval.op_addrCopy a 11 9 hm hm
  obtain ⟨t,k,hk,run,cur,written,fr,af⟩ := vectorLoop_spec P (List.ofFn p) b 0 c d
    (by simpa [a,b] using hn) (by simpa [a,b] using hc) (by simp [a,b]) (by simp [b]) hc9 hd9 hw
    (by simpa using hsep) hm
    (fun q hq => by obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq; exact hPnat j)
    (fun q hq => by obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq; exact hPneg j)
    (fun q hq => by obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq; exact hPq j)
  simp only [List.length_ofFn] at hk
  refine ⟨t,1+(1+k),?_,e0.seq (e1.seq run),cur,?_,?_,?_⟩
  · rw [Nat.succ_mul,Nat.mul_add]
    omega
  · intro j
    simpa using written j.val (by simp)
  · intro j hj hf
    exact fr j hj (by simpa using hf)
  · intro j hj h10 h11
    simpa [a,b,h10,h11] using af j hj h10 h11

end NativePrice
end LinearProgramming
end Optimization
end OAI
