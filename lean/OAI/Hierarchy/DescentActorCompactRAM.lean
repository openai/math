import OAI.Hierarchy.ProtocolRAMGeneratedWriteCheap
import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! # Inverting the physical dense prefix of a sparse actor directory -/
namespace Hierarchy.DescentActorRaster.Inverse
open ProtocolRAM DescentPackedZip Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {X : Type} [Fintype X] {N w : ℕ}

def destination (sparse : X↪Fin N) (dense : X↪Fin N) (out : ℕ) (j : Fin N) : ℕ :=
  if live : ∃x,sparse x=j then out+(dense live.choose).val else out+N+j.val

theorem known (sparse dense : X↪Fin N) (out : ℕ) (x : X) :
    destination sparse dense out (sparse x)=out+(dense x).val := by
  let hit : ∃y,sparse y=sparse x:=⟨x,rfl⟩
  simp [destination]

theorem unique (sparse dense : X↪Fin N) (out : ℕ) : Function.Injective (destination sparse dense out) := by
  intro i j eqn
  by_cases a:∃x,sparse x=i
  · obtain ⟨u,rfl⟩:=a
    rw [known] at eqn
    by_cases b:∃y,sparse y=j
    · obtain ⟨v,rfl⟩:=b
      rw [known] at eqn
      exact congrArg sparse (dense.injective (Fin.ext (Nat.add_left_cancel eqn)))
    · simp only [destination,dite_eq_right b] at eqn
      have:=(dense u).isLt
      omega
  · by_cases b:∃y,sparse y=j
    · obtain ⟨v,rfl⟩:=b
      rw [known] at eqn
      simp only [destination,dite_eq_right a] at eqn
      have:=(dense v).isLt
      omega
    · simp only [destination,dite_eq_right a,dite_eq_right b] at eqn
      exact Fin.ext (Nat.add_left_cancel eqn)

def address (flags ranks : Bank) (out N : ℕ) : Expr :=
  .branch .eq (.lookup flags .row) (.lit 0)
    (.op .add (.lit (out+N)) .row) (.op .add (.lit out) (.lookup ranks .row))

def program (w scratch values out N : ℕ) (flags ranks : Bank) :=
  ProtocolRAMGeneratedWrite.program w scratch values N (address flags ranks out N) .row

def image (sparse dense : X↪Fin N) (flags ranks : Bank) (scratch values out : ℕ) (m : Memory w) :=
  ProtocolRAMGeneratedWrite.image scratch values (address flags ranks out N) .row
    (destination sparse dense out) (fun j=>(j.val:Word w)) m

theorem run (sparse dense : X↪Fin N) (flags ranks : Bank) (scratch values out : ℕ) (m : Memory w)
    (flagFit : flags.Fits w scratch) (rankFit : ranks.Fits w scratch) (fs : N≤flags.size) (rs : N≤ranks.size)
    (sep : scratch+N≤values) (after : values+N≤out) (room : out+2*N<2^w) (one : 1<2^w)
    (presence : ∀j : Fin N,m (flags.base+j.val)=if ∃x,sparse x=j then 1 else 0)
    (ordinals : ∀x,m (ranks.base+(sparse x).val)=((dense x).val:Word w)) :
    let dst:=image sparse dense flags ranks scratch values out m
    let proc:=program w scratch values out N flags ranks
    proc.Exec m dst (ProtocolRAMGeneratedWrite.work N (address flags ranks out N) .row) ∧
    (∀x,dst (out+(dense x).val)=((sparse x).val:Word w)) ∧
    (∀a,a<scratch ∨ out+2*N≤a→dst a=m a) ∧ CheapCode proc := by
  let loc:=destination sparse dense out
  have bounds (j : Fin N) : out≤loc j ∧ loc j<out+2*N:=by
    by_cases hit : ∃x,sparse x=j
    · rcases hit with ⟨x,rfl⟩
      dsimp [loc];rw [known]
      have:=(dense x).isLt
      omega
    · simp only [loc,destination,dite_eq_right hit]
      omega
  have nz : (1:Word w)≠0:=by
    intro eqn
    have bad:=congrArg Fin.val eqn
    change 1%(2^w)=0 at bad
    rw [Nat.mod_eq_of_lt one] at bad
    exact Nat.one_ne_zero bad
  have addr (j : Fin N) : (address flags ranks out N).eval m (j.val:Word w)=(loc j:Word w) := by
    by_cases hit : ∃x,sparse x=j
    · rcases hit with ⟨x,rfl⟩
      have own : ∃y,sparse y=sparse x:=⟨x,rfl⟩
      simp [address,Expr.eval,bank_read _ _ ((sparse x).isLt.trans_le fs) flagFit,
        bank_read _ _ ((sparse x).isLt.trans_le rs) rankFit,presence,ordinals,loc,known,
        Comparison.test,RowOp.opcode,BinaryOp.eval,nz]
    · simp [address,Expr.eval,bank_read _ _ (j.isLt.trans_le fs) flagFit,presence,hit,loc,
        destination,Comparison.test,RowOp.opcode,BinaryOp.eval]
  refine ⟨ProtocolRAMGeneratedWrite.run scratch values (address flags ranks out N) .row loc (fun j=>(j.val:Word w)) m ?_ trivial sep (by omega)
    addr (fun _=>rfl) (fun j=>(bounds j).2.trans room) ?_ ?_,?_,?_,ProtocolRAMRankCheap.generated w scratch values N (address flags ranks out N) .row⟩
  · simp [address,Expr.Fits,flagFit,rankFit]
  · intro i j
    have:=(bounds j).1
    omega
  · intro i j
    have:=(bounds j).1
    omega
  · intro x
    rw [←known sparse dense out x]
    exact ProtocolRAMGeneratedWrite.read _ _ _ _ loc _ m (unique sparse dense out) _
  · intro a outside
    apply ProtocolRAMGeneratedWrite.frame
    · intro j
      change a≠loc j
      obtain ⟨lo,hi⟩:=bounds j
      omega
    · omega
    · omega

end
end Hierarchy.DescentActorRaster.Inverse

end OAI
