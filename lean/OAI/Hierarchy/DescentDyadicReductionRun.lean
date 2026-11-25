import OAI.Hierarchy.DescentDyadicReductionSchedule
import OAI.Hierarchy.DescentWalshScalarReduction

namespace OAI
/-! # Complete chronological packed reduction over the real host population -/
namespace Hierarchy.DescentPackedWalshReduction.Plan
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section

variable (P : Plan)
abbrev pageWords (t : ℕ) := P.hosts t*P.chunks t

def codeStep (w root first t : ℕ) : Procedure w :=
  let old:=P.dataAt first t
  let out:=P.dataAt first (t+1)
  if P.scalar t then DescentWalshScalarReduction.program w old out (P.hosts (t+1)) (2^P.axis)
  else scan w out (P.tile t).rows ((P.tile t).banks (P.headerAt root t) old).read

def stateStep {w : ℕ} (root first t : ℕ) (m : Memory w) : Memory w :=
  let old:=P.dataAt first t
  let out:=P.dataAt first (t+1)
  if P.scalar t then DescentWalshScalarReduction.after old out (P.hosts (t+1)) (2^P.axis) m
  else image out (P.tile t).rows ((P.tile t).banks (P.headerAt root t) old).read m

def ticks (t : ℕ) := 4+(if P.scalar t then 70 else 90)*P.pageWords (t+1)

theorem step (x : Fin P.sites→Fin (2^P.axis)→ℕ) (hx : ∀i d,x i d<2^P.bits)
    {w : ℕ} (root first t : ℕ) (m oldMemory : Memory w) (lt : t<P.depth)
    (stat : P.headerAt root P.depth≤first) (space : P.dataAt first (t+2)<2^w)
    (kept : ∀a<first,m a=P.mount root oldMemory P.depth a)
    (old : Stored (P.dataAt first t) (P.hosts t) (P.chunks t) (P.lanes t) (P.bits+t) (P.values x t) m) :
    let dst:=P.stateStep root first t m
    (P.codeStep w root first t).Exec m dst (P.ticks t) ∧
      Stored (P.dataAt first (t+1)) (P.hosts (t+1)) (P.chunks (t+1)) (P.lanes (t+1)) (P.bits+(t+1))
        (P.values x (t+1)) dst ∧
      (∀a<P.dataAt first (t+1),dst a=m a) ∧ ∀a,P.dataAt first (t+2)≤a→dst a=m a := by
  let out:=P.dataAt first (t+1)
  let source:=P.dataAt first t
  have cap : out+P.pageWords (t+1)<2^w:=space
  have prev : source+P.pageWords t=out:=rfl
  have oldCap : (P.tile t).inputRows=P.pageWords t:=P.inputRows lt
  have afterCap : (P.tile t).rows=P.pageWords (t+1):=P.rows t
  have starts : first≤out:=P.data_mono first (Nat.zero_le (t+1))
  by_cases late : P.scalar t
  · obtain ⟨l0,l1,k0,k1⟩:=P.scalar_lanes late
    have twice : 2*P.hosts (t+1)=P.hosts t := (Nat.mul_comm ..).trans (P.old_hosts lt)
    have bankSize : (DescentWalshScalarReduction.bank source (P.hosts (t+1)) (2^P.axis)).size=P.pageWords t := by
      rw [show P.pageWords t=P.hosts t*2^P.axis by rw [pageWords,k0]]
      change 2^Nat.clog 2 (2*P.hosts (t+1)*2^P.axis)=P.hosts t*2^P.axis
      rw [twice,hosts,←pow_add,Nat.clog_pow _ _ (by decide)]
    have rows : ∀v<2*P.hosts (t+1),∀d<2^P.axis,m (source+(v*2^P.axis+d))=(P.values x t v d:Word w) := by
      intro v hv d hd
      rw [twice] at hv
      have had:=old v hv d (k0.symm ▸ hd)
      rw [k0,l0,packNat_one _ _ (by simpa using P.value_bound x hx t v d)] at had
      simpa only [Nat.mul_one,Nat.add_zero,Nat.add_assoc] using had
    have ⟨run,read,lo,hi,_⟩:=DescentWalshScalarReduction.run source out (P.hosts (t+1)) (2^P.axis)
      m P.axis rfl (P.values x t) rows (by rw [bankSize]; exact prev.le) (by simpa only [pageWords,k1] using cap)
    refine ⟨?_,?_,?_,?_⟩
    · simp only [codeStep,stateStep,ticks,ite_eq_left late,pageWords,k1]
      exact @run
    · intro v hv d hd
      have hd':d<2^P.axis:=hd.trans_le k1.le
      rw [k1,l1,packNat_one _ _ (by simpa using P.value_bound x hx (t+1) v d)]
      simpa only [stateStep,ite_eq_left late,out,source,Nat.mul_one,Nat.add_zero,Nat.add_assoc,
        values,DescentWalshDyadicSums.value_succ] using read v hv d hd'
    · simpa only [stateStep,ite_eq_left late,out,source] using lo
    · simpa only [stateStep,ite_eq_left late,out,source,dataAt,k1] using hi
  · let S:=P.tile t
    have «prefix» : P.headerAt root t+S.span≤first := by
      have low:=(P.header_mono root (show t+1≤P.depth from lt)).trans stat
      simpa only [headerAt,headerSize,ite_eq_right late,S] using low
    have head (j : ℕ) (atj : j<S.span) : m (P.headerAt root t+j)=S.word j :=
      (kept _ (by omega)).trans (P.headerRead root oldMemory lt late j atj)
    have tileInput : Stored source (S.H*2) S.K (S.Z*S.L) S.digits (P.values x t) m := by
      rw [show S.H*2=P.hosts t from P.old_hosts lt,show S.K=P.chunks t from rfl,
        show S.Z*S.L=P.lanes t from P.old_lanes t,show S.digits=P.bits+t from rfl]
      exact old
    have tilePrior : source+S.inputRows≤out := (congrArg (source+·) oldCap).trans_le prev.le
    have tileEnd : out+S.rows=P.dataAt first (t+2) := (congrArg (out+·) afterCap).trans rfl
    obtain ⟨run,read,lo,hi⟩:=S.run_nat (rom:=P.headerAt root t) (source:=source) (out:=out)
      (P.values x t) m (P.value_bound x hx t) («prefix».trans starts) tilePrior
      (tileEnd.trans_lt space) head tileInput
    have elapsed : P.ticks t=4+90*S.rows := by
      rw [ticks,ite_eq_right late,show S.rows=P.pageWords (t+1) from afterCap]
    refine ⟨?_,?_,?_,?_⟩
    · simp only [codeStep,stateStep,ite_eq_right late,elapsed]
      exact @run
    · rw [show S.K*S.Z=P.chunks (t+1) from P.new_chunks t,
        show S.H=P.hosts (t+1) from rfl,show S.L=P.lanes (t+1) from rfl,
        show S.digits+1=P.bits+(t+1) from rfl,P.values_step] at read
      simpa only [stateStep,ite_eq_right late] using read
    · simpa only [stateStep,ite_eq_right late] using lo
    · intro i far
      simpa only [stateStep,ite_eq_right late] using hi i (tileEnd.trans_le far)

def code (P : Plan) (w root first : ℕ) : ℕ→Procedure w
  | 0=>scan w first 0 .row
  | t+1=>(P.code w root first t).seq (P.codeStep w root first t)
def state (P : Plan) {w : ℕ} (root first : ℕ) (m : Memory w) : ℕ→Memory w
  | 0=>m
  | t+1=>P.stateStep root first t (P.state root first m t)
def duration (P : Plan) : ℕ→ℕ
  | 0=>4
  | t+1=>P.duration t+P.ticks t

private theorem start {w : ℕ} (first : ℕ) (m : Memory w) (cap : first<2^w) :
    (scan w first 0 .row).Exec m m 4 := by
  have noRows : image first 0 .row m=m := by
    funext j
    exact ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (by omega)
  have emptyScan : (scan w first 0 .row).Exec m (image first 0 .row m)
      (4+0*(2*Expr.row.work+4)) :=
    @scan_exec w first 0 .row m trivial (by omega : first+0<2^w)
  rw [noRows,Nat.zero_mul,Nat.add_zero] at emptyScan
  exact @emptyScan

theorem runTo (x : Fin P.sites→Fin (2^P.axis)→ℕ) (hx : ∀i d,x i d<2^P.bits)
    {w : ℕ} (root first : ℕ) (m old : Memory w) (n : ℕ) (bound : n≤P.depth)
    (stat : P.headerAt root P.depth≤first) (space : P.dataAt first (P.depth+1)<2^w)
    (rom : ∀j<first,m j=P.mount root old P.depth j)
    (base : Stored first (P.hosts 0) (P.chunks 0) (P.lanes 0) P.bits (P.values x 0) m) :
    let dst:=P.state root first m n
    (P.code w root first n).Exec m dst (P.duration n) ∧
      Stored (P.dataAt first n) (P.hosts n) (P.chunks n) (P.lanes n) (P.bits+n) (P.values x n) dst ∧
      (∀j<first,dst j=m j) ∧ ∀j,P.dataAt first (n+1)≤j→dst j=m j := by
  induction n with
  | zero=>
    exact ⟨start first m ((P.data_mono first (Nat.zero_le (P.depth+1))).trans_lt space),base,fun _ _=>rfl,fun _ _=>rfl⟩
  | succ t ih=>
    obtain ⟨past,oldWords,low,high⟩:=ih (by omega)
    have last : P.dataAt first (t+2)<2^w := (P.data_mono first (by omega)).trans_lt space
    obtain ⟨one,read,l,h⟩:=P.step x hx root first t (P.state root first m t) old bound stat last
      (fun j hj=>(low j hj).trans (rom j hj)) oldWords
    exact ⟨Procedure.Exec.then past one,read,fun j hj=>(l j (hj.trans_le (P.data_mono first (Nat.zero_le _)))).trans (low j hj),
      fun j hj=>(h j hj).trans (high j ((P.data_mono first (Nat.le_succ _)).trans hj))⟩

end
end Hierarchy.DescentPackedWalshReduction.Plan

end OAI
