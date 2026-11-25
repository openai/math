import OAI.ThreeFlat.RAM.DeterministicBlock

namespace OAI
/-! # Coiterating the native instruction interpreter on an actual terminal RAM run -/
namespace Hierarchy.DescentTerminalSimulatedClock
open Computability.VPVNP.BurstRAM ThreeFlat.RAM

variable {w W : ℕ} {C D : Type*} (P : Program w C) (U : Program W D)
variable (Rep : C→Memory w→D→Memory W→Prop)

/-- Only continuing source instructions have a successor. The finish instruction
is handled by the physically separate return block. The interval accommodates
instruction-dependent prices and a fixed microclock as a special case. -/
def Steps (lo hi : ℕ) : Prop :=
  ∀c m d n,Rep c m d n→∀c' m',advance P 1 c m=some (c',m')→
    ∃v d' n',lo ≤ v ∧ v ≤ hi ∧ advance U v d n=some (d',n') ∧ Rep c' m' d' n'

theorem coiterate {lo hi : ℕ} (micro : Steps P U Rep lo hi)
    {t : ℕ} {c c' : C} {m m' : Memory w} {d : D} {n : Memory W}
    (initial : Rep c m d n) (old : advance P t c m=some (c',m')) :
    ∃v d' n',lo*t ≤ v ∧ v ≤ hi*t ∧ advance U v d n=some (d',n') ∧ Rep c' m' d' n' := by
  induction t generalizing c m d n with
  | zero=>
    obtain ⟨rfl,rfl⟩:=Prod.mk.inj (Option.some.inj old)
    exact ⟨0,d,n,by simp,by simp,rfl,initial⟩
  | succ t ih=>
    rw [show t+1=1+t by omega,advance_add] at old
    cases one : advance P 1 c m with
    | none=>simp [one] at old
    | some pair=>
      obtain ⟨cc,mm⟩:=pair
      rw [one] at old
      change advance P t cc mm=some (c',m') at old
      obtain ⟨u,dd,nn,lb,ub,tick,next⟩:=micro c m d n initial cc mm one
      obtain ⟨v,last,out,lb',ub',run,end_⟩:=ih next old
      refine ⟨u+v,last,out,?_,?_,advance_trans tick run,end_⟩ <;>
        rw [Nat.mul_succ] <;> omega

theorem exact {K t : ℕ} (micro : Steps P U Rep K K)
    {c c' : C} {m m' : Memory w} {d : D} {n : Memory W}
    (initial : Rep c m d n) (old : advance P t c m=some (c',m')) :
    ∃d' n',advance U (K*t) d n=some (d',n') ∧ Rep c' m' d' n' := by
  obtain ⟨v,d',n',lo,hi,run,end_⟩:=coiterate P U Rep micro initial old
  exact ⟨d',n',Nat.le_antisymm hi lo ▸ run,end_⟩

theorem simulate {K t : ℕ} (micro : Steps P U Rep 0 K)
    {c c' : C} {m m' : Memory w} {d : D} {n : Memory W}
    (initial : Rep c m d n) (old : advance P t c m=some (c',m')) :
    ∃v d' n',v ≤ K*t ∧ advance U v d n=some (d',n') ∧ Rep c' m' d' n' := by
  obtain ⟨v,d',n',_,hi,run,end_⟩:=coiterate P U Rep micro initial old
  exact ⟨v,d',n',hi,run,end_⟩

/-- A final memory relation allows high scratch, opcode and register banks in
the target. In particular it can assert equality of just the observed words. -/
theorem terminal {K budget bootFee returnFee : ℕ} (micro : Steps P U Rep 0 K)
    (oldStart : Word w) (newStart : Word W) (oldInput : Memory w) (newInput : Memory W)
    (boot : ∃t d n,t ≤ bootFee ∧ advance U t (U.start newStart) newInput=some (d,n) ∧
      Rep (P.start oldStart) oldInput d n)
    (Obs : Memory w→Memory W→Prop)
    (ret : ∀c m d n,Rep c m d n→∀result,P.step c=.finish result→
      ∃u d' n' result',u ≤ returnFee ∧ advance U u d n=some (d',n') ∧ U.step d'=.finish result' ∧ Obs m n')
    {out : Memory w}
    (old : ∃t c result,t < budget ∧ advance P t (P.start oldStart) oldInput=some (c,out) ∧ P.step c=.finish result) :
    ∃t d out' result,t < bootFee+K*budget+returnFee+1 ∧
      advance U t (U.start newStart) newInput=some (d,out') ∧ U.step d=.finish result ∧ Obs out out' := by
  obtain ⟨a,d,n,paid,start,ready⟩:=boot
  obtain ⟨t,c,result,short,ran,finished⟩:=old
  obtain ⟨u,d',n',ticks,steps,represented⟩:=simulate P U Rep micro ready ran
  obtain ⟨v,last,image,answer,price,finish,halt,seen⟩:=ret c out d' n' represented result finished
  have bound:=Nat.mul_le_mul_left K short.le
  exact ⟨a+u+v,last,image,answer,by omega,advance_trans (advance_trans start steps) finish,halt,seen⟩

/-- If a native dispatcher uses an absorbing local instruction after source
termination, an exact public deadline can instead be observed inside that loop. -/
theorem idle {c : D} (loop : U.step c=.localStep c) (n : Memory W) (t : ℕ) :
    advance U t c n=some (c,n) := by
  induction t with
  | zero=>rfl
  | succ t ih=>simpa only [advance,loop] using ih

theorem deadline {K t budget bootFee returnFee : ℕ} (micro : Steps P U Rep K K)
    {c c' : C} {m out : Memory w} {d : D} {n : Memory W}
    (origin : D) (input : Memory W) (boot : advance U bootFee origin input=some (d,n))
    (ready : Rep c m d n) (ran : advance P t c m=some (c',out))
    (short : t ≤ budget) (Obs : Memory W→Prop)
    (ret : ∀d' n',Rep c' out d' n'→∃pc last,advance U returnFee d' n'=some (pc,last) ∧
      U.step pc=.localStep pc ∧ Obs last) :
    ∃pc last,advance U (bootFee+K*budget+returnFee) origin input=some (pc,last) ∧ Obs last := by
  obtain ⟨d',n',advanced,held⟩:=exact P U Rep micro ready ran
  obtain ⟨pc,last,returned,loop,seen⟩:=ret d' n' held
  have run:=advance_trans (advance_trans boot advanced) returned
  have padded:=advance_trans run (idle U loop last (K*budget-K*t))
  have paid:=Nat.mul_le_mul_left K short
  have time : bootFee+K*t+returnFee+(K*budget-K*t)=bootFee+K*budget+returnFee:=by omega
  exact ⟨pc,last,time ▸ padded,seen⟩

end Hierarchy.DescentTerminalSimulatedClock

end OAI
