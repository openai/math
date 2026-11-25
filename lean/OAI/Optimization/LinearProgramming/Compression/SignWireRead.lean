import OAI.Optimization.LinearProgramming.Compression.SignWireField

/-! The fixed row reader for the binary lattice sign-service ABI. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire
open RAM NativePrice OracleSpec

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private def packet (zs : List ℤ) : Word := zs.flatMap fieldWord

private def rowBody : Block :=
  .seq signedFieldBlock (.straight [.store 12 3, .incr 12 12, .incr 11 11])

private def rowLoop : Block := .loop (.addrLT 11 10) rowBody

/-- The controller has supplied dimension in address 10, destination in
address 12, and packet base in the standard callback register 43. -/
def signRowReadBlock : Block :=
  .seq (.straight [.addrCopy 3 43,.const 8 0,.addrConst 11 0]) rowLoop

private theorem rowLoop_spec (P : K → Prop) (zs : List ℤ) :
    ∀ (m : Memory K) (q cur dst : ℕ), m.AllData P → m.index 3=cur → m.index 12=dst →
    m.index 10=q+zs.length → m.index 11=q → m.data 8=0 →
    9 ≤ cur → cur+(packet zs).length ≤ dst → WordAt m cur (packet zs) →
    (∀ z ∈ zs, ∀ v : ℕ, v ≤ 2^z.natAbs.bits.length → P (v:K)) →
    (∀ z ∈ zs, P (z:K)) →
    ∃ t k, k ≤ 16*(packet zs).length+13*zs.length+1 ∧
      Block.Eval (Memory.AllData P) rowLoop m k t ∧
      t.index 3=cur+(packet zs).length ∧ t.index 12=dst+zs.length ∧
      (∀ i : Fin zs.length, t.data (dst+i.val)=(zs[i.val]:K)) ∧
      (∀ j, (j < 3 ∨ 7 < j) → (j < dst ∨ dst+zs.length ≤ j) → t.data j=m.data j) ∧
      (∀ j, (j < 3 ∨ 6 < j) → j ≠ 11 → j ≠ 12 → t.index j=m.index j) := by
  induction zs with
  | nil =>
    intro m q cur dst hm hc hd hn hq _ _ _ _ _ _
    have guard : (Cond.addrLT 11 10).test m=false := by simp [Cond.test,hn,hq]
    exact ⟨m,1,by simp [packet],.loopFalse guard hm,by simpa [packet] using hc,
      by simpa using hd,fun i => i.elim0,fun _ _ _ => rfl,fun _ _ _ _ => rfl⟩
  | cons z zs ih =>
    intro m q cur dst hm hc hd hn hq hzero hc₀ hsep hw hP hp
    let fw := fieldWord z
    have hlen : (packet (z::zs)).length = fw.length+(packet zs).length := by simp [packet,fw]
    have hhead : WordAt m cur (fw++packet zs) := hw
    obtain ⟨head,tail⟩ := wordAt_append.mp hhead
    obtain ⟨s,j,hj,es,sv,sc,sd,si⟩ := signedFieldBlock_spec P z m cur hm hc hc₀ hzero head
      (hP z (by simp)) (hp z (by simp))
    have sdst : s.index 12=dst := (si 12 (by decide)).trans hd
    let u := s.putData (s.index 12) (s.data 3)
    let v := u.putIndex 12 (u.index 12+1)
    let w := v.putIndex 11 (v.index 11+1)
    have hu : u.AllData P := es.safe_end.putData _ (es.safe_end _)
    have hv : v.AllData P := hu
    have hww : w.AllData P := hv
    have estore := Block.Eval.op_store s 12 3 es.safe_end hu
    have einc := Block.Eval.op_incr u 12 12 hu hv
    have ecount := Block.Eval.op_incr v 11 11 hv hww
    have ebody : Block.Eval (Memory.AllData P) rowBody m (j+3) w :=
      es.seq (estore.seq (einc.seq (ecount.seq (.skip hww))))
    have whigh (i : ℕ) (hi : i < 3 ∨ 7 < i) (hneq : i ≠ dst) : w.data i=m.data i := by
      simpa [w,v,u,sdst,hneq] using sd i hi
    have widx (i : ℕ) (hi : i < 3 ∨ 6 < i) (h11 : i ≠ 11) (h12 : i ≠ 12) :
        w.index i=m.index i := by simpa [w,v,u,h11,h12] using si i hi
    have wd : w.index 12=dst+1 := by simp [w,v,u,sdst]
    have wc : w.index 3=cur+fw.length := by simpa [w,v,u,fw] using sc
    have w10 : w.index 10=(q+1)+zs.length := by
      rw [widx 10 (by decide) (by decide) (by decide),hn,List.length_cons];omega
    have w11 : w.index 11=q+1 := by
      simp [w,v,u,si 11 (by decide),hq]
    have wzero : w.data 8=0 := (whigh 8 (by decide) (by omega)).trans hzero
    have wtail : WordAt w (cur+fw.length) (packet zs) :=
      tail.of_data (by intro i hlow hi;apply whigh <;> omega)
    have wrote : w.data dst=(z:K) := by simp [w,v,u,sdst,sv]
    obtain ⟨t,k,hk,et,tc,tdst,values,tf,ti⟩ := ih w (q+1) (cur+fw.length) (dst+1)
      hww wc wd w10 w11 wzero (by omega) (by omega) wtail
      (fun x hx => hP x (List.mem_cons_of_mem _ hx)) (fun x hx => hp x (List.mem_cons_of_mem _ hx))
    have guard : (Cond.addrLT 11 10).test m=true := by
      simp [Cond.test,hn,hq]
    refine ⟨t,1+(j+3)+1+k,?_,.loopTrue guard ebody et,?_,?_,?_,?_,?_⟩
    · rw [hlen,List.length_cons];change j ≤ 16*fw.length+8 at hj;omega
    · rw [hlen,tc];omega
    · rw [tdst,List.length_cons];omega
    · intro i
      cases i using Fin.cases with
      | zero => simpa using (tf dst (by omega) (by omega)).trans wrote
      | succ i =>
        have hi := values i
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hi
    · intro i hi hr
      rw [tf i hi (by simp only [List.length_cons] at hr;omega)]
      exact whigh i hi (by simp only [List.length_cons] at hr;omega)
    · intro i hi h11 h12
      exact (ti i hi h11 h12).trans (widx i hi h11 h12)

/-- Decode every scalar field in its stored order. The input packet length
in address register 37 is unchanged and the final cursor identifies its end.
Only scratch address registers 3 through 6, 11 and 12 are touched, so all VM
state in the high address bank is preserved. -/
theorem signRowReadBlock_spec {p : ℕ} (P : K → Prop) (row : Fin p → ℤ)
    (m : Memory K) (base out : ℕ) (hm : m.AllData P) (hzero : P 0)
    (hq : m.index 43=base) (hl : m.index 37=(Lattice.signRowWord row).length)
    (hn : m.index 10=p) (hd : m.index 12=out)
    (hbase : 9 ≤ base) (hsep : base+(Lattice.signRowWord row).length ≤ out)
    (hw : WordAt m base (Lattice.signRowWord row))
    (hP : ∀ i, ∀ v : ℕ, v ≤ 2^(row i).natAbs.bits.length → P (v:K))
    (hval : ∀ i, P (row i:K)) :
    ∃ t k, k ≤ 16*(Lattice.signRowWord row).length+13*p+4 ∧
      Block.Eval (Memory.AllData P) signRowReadBlock m k t ∧
      t.index 3=base+t.index 37 ∧ t.index 12=out+p ∧
      (∀ i, t.data (out+i.val)=(row i:K)) ∧
      (∀ i, (i < 3 ∨ 8 < i) → (i < out ∨ out+p ≤ i) → t.data i=m.data i) ∧
      (∀ i, (i < 3 ∨ 6 < i) → i ≠ 11 → i ≠ 12 → t.index i=m.index i) := by
  let u := m.putIndex 3 (m.index 43)
  let v := u.putData 8 ((0 : ℚ) : K)
  let w := v.putIndex 11 0
  have hu : u.AllData P := hm
  have hv : v.AllData P := hu.putData _ (by simpa only [Rat.cast_zero] using hzero)
  have hs : w.AllData P := hv
  have ei := (Block.Eval.op_addrCopy m 3 43 hm hu).seq
    ((Block.Eval.op_const u 8 0 hu hv).seq ((Block.Eval.op_addrConst v 11 0 hv hs).seq (.skip hs)))
  let xs := List.ofFn row
  have hp : xs.length=p := List.length_ofFn
  have encoded : packet xs=Lattice.signRowWord row := rfl
  have wf : WordAt w base (packet xs) := (encoded ▸ hw).of_data (by
    intro i hh _;simp [w,v,u,show i ≠ 8 by omega])
  obtain ⟨t,k,hk,et,tc,td,vals,tf,ti⟩ := rowLoop_spec P xs w 0 base out hs
    (by simp [w,v,u,hq]) (by simpa [w,v,u] using hd)
    (by simpa [w,v,u,hp] using hn) (by simp [w]) (by simp [w,v]) hbase
    (encoded ▸ hsep) wf (by
      rintro z hx
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
      exact hP i) (by
      rintro z hx
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
      exact hval i)
  have t37 := ti 37 (by decide) (by decide) (by decide)
  refine ⟨t,3+k,?_,ei.seq et,?_,by simpa [hp] using td,?_,?_,?_⟩
  · rw [encoded,hp] at hk;omega
  · simpa [t37,w,v,u,hl,encoded] using tc
  · intro i
    let j : Fin xs.length := ⟨i.val,by rw [hp];exact i.isLt⟩
    simpa [xs,j] using vals j
  · intro i hi hr
    rw [tf i (by omega) (by simpa only [hp] using hr)]
    simp [w,v,u,show i ≠ 8 by omega]
  · intro i hi h11 h12
    simpa [w,v,u,h11,show i ≠ 3 by omega] using ti i hi h11 h12

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
