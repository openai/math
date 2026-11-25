import OAI.Hierarchy.DescentDyadicReductionGhosts

namespace OAI
/-! # The dyadic reduction's fixed passes on arbitrary old memory -/
namespace Hierarchy.DescentPackedWalshReduction.Plan
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (P : Plan) {w : ℕ}

theorem any_step (root first t : ℕ) (m : Memory w) (lt : t<P.depth)
    (stat : P.headerAt root P.depth≤first) (space : P.dataAt first (t+2)<2^w) :
    (P.codeStep w root first t).Exec m (P.stateStep root first t m) (P.ticks t) := by
  let out:=P.dataAt first (t+1)
  let src:=P.dataAt first t
  have cap : out+P.pageWords (t+1)<2^w:=space
  have prev : src+P.pageWords t=out:=rfl
  have starts : first≤out:=P.data_mono first (Nat.zero_le (t+1))
  refine @Classical.byCases (P.scalar t)
    ((P.codeStep w root first t).Exec m (P.stateStep root first t m) (P.ticks t)) ?_ ?_
  · intro late
    obtain ⟨_,_,k0,k1⟩:=P.scalar_lanes late
    have twice : 2*P.hosts (t+1)=P.hosts t := (Nat.mul_comm ..).trans (P.old_hosts lt)
    have bankSize : (DescentWalshScalarReduction.bank src (P.hosts (t+1)) (2^P.axis)).size=P.pageWords t := by
      rw [show P.pageWords t=P.hosts t*2^P.axis by rw [pageWords,k0]]
      change 2^Nat.clog 2 (2*P.hosts (t+1)*2^P.axis)=P.hosts t*2^P.axis
      rw [twice,hosts,←pow_add,Nat.clog_pow _ _ (by decide)]
    let f:=fun v d=>(m (src+(v*2^P.axis+d))).val
    obtain ⟨run,_⟩:=DescentWalshScalarReduction.run src out (P.hosts (t+1)) (2^P.axis)
      m P.axis rfl f (fun _ _ _ _=>by simp [f]) (by rw [bankSize];exact prev.le)
      (by simpa only [pageWords,k1] using cap)
    simp only [codeStep,stateStep,ticks,ite_eq_left late,pageWords,k1]
    exact @run
  · intro late
    let T:=P.tile t
    have static : P.headerAt root t+T.span≤first := by
      have low:=(P.header_mono root (show t+1≤P.depth from lt)).trans stat
      simpa only [headerAt,headerSize,ite_eq_right late,T] using low
    let B:=T.banks (P.headerAt root t) src
    have count : T.rows=P.pageWords (t+1):=P.rows t
    have finish : out+T.rows<2^w:=by rw [count];exact cap
    have prior : src+T.inputRows≤out := (congrArg (src+·) (P.inputRows lt)).trans_le prev.le
    have room:=T.room (static.trans starts) prior finish
    have legal : B.read.Fits w out:=⟨room.table,⟨room.tag,trivial⟩,
      ⟨room.old,room.hi,trivial⟩,room.shift,room.old,room.lo,trivial⟩
    have work : 2*B.read.work+4=90:=rfl
    have exec : (scan w out T.rows B.read).Exec m (image out T.rows B.read m) (4+90*T.rows) := by
      rw [Nat.mul_comm 90,←work]
      exact @scan_exec w out T.rows B.read m legal finish
    have elapsed : P.ticks t=4+90*T.rows := by rw [ticks,ite_eq_right late,count]
    simp only [codeStep,stateStep,ite_eq_right late,elapsed]
    exact @exec

theorem any_reduce (root first : ℕ) (m : Memory w) (n : ℕ) (within : n≤P.depth)
    (stat : P.headerAt root P.depth≤first) (space : P.dataAt first (P.depth+1)<2^w) :
    (P.code w root first n).Exec m (P.state root first m n) (P.duration n) := by
  induction n with
  | zero=>
    have cap : first<2^w:=(P.data_mono first (Nat.zero_le _)).trans_lt space
    have same : image first 0 .row m=m:=by
      funext a
      exact ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (by omega)
    have emptyScan : (scan w first 0 .row).Exec m (image first 0 .row m) (4+0*(2*Expr.row.work+4)) :=
      @scan_exec w first 0 .row m trivial (by omega : first+0<2^w)
    rw [same,Nat.zero_mul,Nat.add_zero] at emptyScan
    exact @emptyScan
  | succ n ih=>
    have yes : (P.depth+1)≥n+2:=by omega
    have final : (P.codeStep w root first n).Exec (P.state root first m n)
      (P.stateStep root first n (P.state root first m n)) (P.ticks n) :=P.any_step root first n (P.state root first m n) within stat ((P.data_mono first yes).trans_lt space)
    intro labels regs slots machine
    exact Procedure.Exec.then (ih (Nat.le_of_succ_le within)) final machine

theorem any_pad (first : ℕ) (m : Memory w) (room : P.dataAt first 1<2^w) :
    (P.padProgram w first).Exec m (P.pad first m) P.padTicks := by
  have cap : P.ghostBase first+P.ghostRows<2^w:=(P.pad_end first).trans_lt room
  change (scan w _ _ (.lit 0)).Exec m (image _ _ (.lit 0) m) (4+6*P.ghostRows)
  rw [Nat.mul_comm 6]
  exact @scan_exec w _ _ (.lit 0) m trivial cap

end
end Hierarchy.DescentPackedWalshReduction.Plan

end OAI
